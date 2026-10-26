#!/usr/bin/env python3
"""Run independent real-editor sleep/network recovery trials; retain all evidence."""

import argparse
from collections.abc import Callable
import concurrent.futures
import os
from pathlib import Path
import re
import signal
import subprocess
import tempfile
import time
from typing import TextIO

ROOT = Path(__file__).resolve().parents[2]
BINARY = Path(os.environ.get("TEAMTYPEV_BINARY", str(ROOT / "target/release/teamtypev")))
os.environ["TEAMTYPEV_BINARY"] = str(BINARY)


def run(*args: str) -> str:
    return subprocess.check_output(
        args, text=True, stderr=subprocess.STDOUT, timeout=10
    ).strip()


def wait_for(check: Callable[[], bool], timeout_s: float = 90) -> None:
    deadline = time.monotonic() + timeout_s
    while time.monotonic() < deadline:
        if check():
            return
        time.sleep(0.1)
    raise TimeoutError("condition did not become true")


def trial(out: Path, mode: str, duration_s: int, repeat: int) -> str:
    name = f"{mode}-{duration_s}-{repeat}"
    work = out / name
    work.mkdir()
    processes: list[subprocess.Popen[bytes]] = []
    logs: list[TextIO] = []
    expected = {"seed"}
    daemons: dict[str, subprocess.Popen[bytes]] = {}
    editors: dict[str, subprocess.Popen[bytes]] = {}
    ns: list[str] = []

    def start(args: list[str], cwd: Path, log: str) -> subprocess.Popen[bytes]:
        stream = (work / log).open("w")
        logs.append(stream)
        proc = subprocess.Popen(args, cwd=cwd, stdout=stream, stderr=subprocess.STDOUT)
        processes.append(proc)
        return proc

    def expr(person: str, expression: str) -> str:
        return run(
            "nvim",
            "--server",
            str(work / f"{person}.nvim"),
            "--remote-expr",
            expression,
        )

    def edit(person: str, marker: str) -> None:
        expr(person, f"nvim_buf_set_lines(0, 1, 1, 0, ['{marker}'])")
        expected.add(marker)

    def agrees() -> bool:
        texts = [(work / p / "shared.txt").read_text() for p in "abc"]
        if len(set(texts)) != 1 or set(texts[0].splitlines()) != expected:
            return False
        if len(texts[0].splitlines()) != len(expected):
            return False
        return all(
            expr(p, 'join(getline(1, "$"), "\\n")') == texts[0].rstrip("\n")
            for p in "abc"
        )

    try:
        for p in "abc":
            (work / p / ".teamtypev").mkdir(parents=True)
        (work / "a/shared.txt").write_text("seed\n")
        daemons["a"] = start(
            [str(BINARY), "share", "--no-join-code", "--show-secret-address"],
            work / "a",
            "a.log",
        )
        wait_for(lambda: "peer=" in (work / "a.log").read_text())
        match = re.search(r"peer=\S+", (work / "a.log").read_text())
        assert match is not None
        address = match.group()
        for p in "bc":
            (work / p / ".teamtypev/config").write_text(address + "\n")
            if p == "c" and mode == "network":
                (work / "resolv.conf").write_text("nameserver 10.0.2.3\n")
                keeper = start(
                    [
                        "unshare",
                        "-rmn",
                        "sh",
                        "-c",
                        'mount --bind "$1" /etc/resolv.conf; exec sleep infinity',
                        "sh",
                        str(work / "resolv.conf"),
                    ],
                    work / p,
                    "namespace.log",
                )
                time.sleep(0.2)
                start(
                    [
                        "slirp4netns",
                        "--configure",
                        "--userns-path",
                        f"/proc/{keeper.pid}/ns/user",
                        str(keeper.pid),
                        "tap0",
                    ],
                    work / p,
                    "slirp.log",
                )
                ns = [
                    "nsenter",
                    "--preserve-credentials",
                    "-U",
                    "-n",
                    "-m",
                    "-t",
                    str(keeper.pid),
                ]
                wait_for(lambda: "tap0" in run(*ns, "ip", "link"))
                daemons[p] = start(
                    [*ns, f"--wd={work / p}", str(BINARY), "join"], work / p, f"{p}.log"
                )
            else:
                daemons[p] = start([str(BINARY), "join"], work / p, f"{p}.log")
        wait_for(lambda: all((work / p / "shared.txt").exists() for p in "abc"))
        for p in "abc":
            editors[p] = start(
                [
                    "nvim",
                    "--headless",
                    "--clean",
                    "-n",
                    "--listen",
                    str(work / f"{p}.nvim"),
                    "--cmd",
                    f"set runtimepath^={ROOT}/nvim-plugin",
                    "shared.txt",
                ],
                work / p,
                f"{p}.nvim.log",
            )
            wait_for(lambda: (work / f"{p}.nvim").exists())
        time.sleep(2)
        edit("c", "baseline-c")
        wait_for(agrees)
        edit("c", "just-before-stop-c")
        # 🧑 "simulate sleep by stopping a joiner process with SIGSTOP (also its editor client)"
        if mode == "sleep":
            os.kill(daemons["c"].pid, signal.SIGSTOP)
            os.kill(editors["c"].pid, signal.SIGSTOP)
        else:
            run(*ns, "ip", "link", "set", "tap0", "down")
            edit("c", "offline-c")
        stopped_at = time.monotonic()
        tick = 0
        while time.monotonic() - stopped_at < duration_s:
            for p in "ab":
                edit(p, f"during-{p}-{tick}")
            tick += 1
            time.sleep(min(2, max(0, duration_s - (time.monotonic() - stopped_at))))
        resumed_at = time.monotonic()
        if mode == "sleep":
            os.kill(daemons["c"].pid, signal.SIGCONT)
            os.kill(editors["c"].pid, signal.SIGCONT)
        else:
            run(*ns, "ip", "link", "set", "tap0", "up")
            run(
                *ns,
                "ip",
                "route",
                "replace",
                "default",
                "via",
                "10.0.2.2",
                "dev",
                "tap0",
            )
        wait_for(agrees, 180)
        recovery_s = time.monotonic() - resumed_at
        for p in "abc":
            edit(p, f"after-{p}")
        wait_for(agrees)
        if recovery_s >= 10:
            raise RuntimeError(f"slow catch-up: {recovery_s:.3f} s; no edits lost")
        result = f"{name}\tPASS\t{recovery_s:.3f}\t{len(expected)}\tno edits lost"
    except Exception as exc:
        result = f"{name}\tFAIL\t{type(exc).__name__}: {exc}"
    finally:
        (work / "expected.txt").write_text("\n".join(sorted(expected)) + "\n")
        for proc in reversed(processes):
            if proc.poll() is None:
                proc.send_signal(signal.SIGCONT)
                proc.terminate()
        for proc in processes:
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait()
        for log in logs:
            log.close()
    (work / "result.tsv").write_text(result + "\n")
    print(result, flush=True)
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--durations", type=int, nargs="+", default=[30, 120, 900, 1800]
    )
    parser.add_argument("--repeats", type=int, default=2)
    parser.add_argument("--modes", nargs="+", default=["sleep", "network"])
    parser.add_argument("--workers", type=int, default=3)
    parser.add_argument("--work", type=Path)
    args = parser.parse_args()
    out = args.work or Path(tempfile.mkdtemp(prefix="teamtypev-sleep-"))
    out.mkdir(parents=True, exist_ok=True)
    print(out, flush=True)
    cases = [
        (mode, duration, repeat)
        for mode in args.modes
        for duration in args.durations
        for repeat in range(args.repeats)
    ]
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = [pool.submit(trial, out, *case) for case in cases]
        results = [future.result() for future in futures]
    (out / "results.tsv").write_text("\n".join(results) + "\n")
    return int(any("\tFAIL\t" in result for result in results))


if __name__ == "__main__":
    raise SystemExit(main())
