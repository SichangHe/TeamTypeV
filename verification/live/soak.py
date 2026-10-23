#!/usr/bin/env python3
"""Run isolated peers with concurrent edits and timed network outages."""

import argparse
import asyncio
import hashlib
import json
import os
from pathlib import Path
import re
import random
import signal
import time
from collections.abc import Callable, Sequence
from datetime import datetime, timezone
from typing import final

ROOT = Path(__file__).resolve().parents[2]
BINARY = Path(os.environ.get("SOAK_BINARY", ROOT / "target/release/teamtype"))


@final
class Soak:
    def __init__(self, work: Path, duration_s: float, seed_from: Path | None = None,
                 first_cycle: int = 0, joiners: int = 2, seed: int = 1,
                 catchup_limit_s: float = 10) -> None:
        self.peers = "abcde"[:joiners + 1]
        self.rng = random.Random(seed)
        self.seed = seed
        self.catchup_limit_s = catchup_limit_s
        self.relay: str | None = None
        self.work = work
        self.duration_s = duration_s
        self.seed_from = seed_from
        self.first_cycle = first_cycle
        self.prefix = "diag-" if seed_from else ""
        self.processes: list[asyncio.subprocess.Process] = []
        self.holders: dict[str, asyncio.subprocess.Process] = {}
        self.daemons: dict[str, asyncio.subprocess.Process] = {}
        self.accepted: set[str] = set()
        self.counts = {p: 0 for p in self.peers}
        self.failures: list[dict[str, object]] = []
        self.checks: list[dict[str, object]] = []
        self.events = work / "events.jsonl"
        self.env = dict(os.environ, TEAMTYPE_BINARY=str(BINARY))
        self.tasks: list[asyncio.Task[None]] = []

    def event(self, kind: str, **data: object) -> None:
        with self.events.open("a") as out:
            out.write(json.dumps(dict(time=datetime.now(timezone.utc).isoformat(),
                                      monotonic_s=time.monotonic(), kind=kind, **data)) + "\n")

    async def command(self, args: Sequence[str | Path], cwd: Path | None = None,
                      timeout_s: float = 15) -> tuple[int, str]:
        proc = await asyncio.create_subprocess_exec(*map(str, args), cwd=cwd, env=self.env,
                    stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.STDOUT)
        try:
            output, _ = await asyncio.wait_for(proc.communicate(), timeout_s)
        except TimeoutError:
            proc.kill()
            await proc.wait()
            self.event("command_timeout", command=list(map(str, args)))
            return -1, "timeout"
        assert proc.returncode is not None
        return proc.returncode, output.decode(errors="replace")

    def ns(self, peer: str) -> list[str]:
        return ["nsenter", "-t", str(self.holders[peer].pid), "-U", "-n", "-m",
                f"--wd={self.work / peer}", "--preserve-credentials", "--"]

    async def spawn(self, args: Sequence[str | Path], logfile: str,
                    cwd: Path | None = None) -> asyncio.subprocess.Process:
        out = (self.work / logfile).open("ab", buffering=0)
        proc = await asyncio.create_subprocess_exec(*map(str, args), cwd=cwd, env=self.env,
                    stdin=asyncio.subprocess.DEVNULL, stdout=out, stderr=out,
                    start_new_session=True)
        out.close()
        self.processes.append(proc)
        self.event("spawn", pid=proc.pid, command=list(map(str, args)), cwd=str(cwd))
        return proc

    async def daemon_log(self, peer: str, proc: asyncio.subprocess.Process) -> None:
        assert proc.stdout is not None
        with (self.work / f"{peer}.log").open("a", buffering=1) as out:
            while line := await proc.stdout.readline():
                text = line.decode(errors="replace").rstrip()
                stamp = datetime.now(timezone.utc).isoformat()
                out.write(f"{stamp} {text}\n")
                if any(word in text.lower() for word in ("connected to peer", "connection to peer", "error", "panic")):
                    self.event("daemon", peer=peer, message=text)

    async def start_daemon(self, peer: str) -> None:
        if self.relay:
            config = self.work / peer / ".teamtype/config"
            existing = config.read_text() if config.exists() else ""
            _ = config.write_text(existing + f"iroh_relay={self.relay}\n")
        (self.work / f"{peer}.log").touch()
        args = [BINARY, "share", "--no-join-code", "--show-secret-address"] if peer == "a" else [BINARY, "join"]
        proc = await asyncio.create_subprocess_exec(*map(str, self.ns(peer) + args),
                    cwd=self.work / peer, env=self.env, stdin=asyncio.subprocess.DEVNULL,
                    stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.STDOUT,
                    limit=8 * 1024 * 1024,
                    start_new_session=True)
        self.processes.append(proc)
        self.daemons[peer] = proc
        self.tasks.append(asyncio.create_task(self.daemon_log(peer, proc)))
        self.event("daemon_start", peer=peer, pid=proc.pid, command=list(map(str, self.ns(peer) + args)))

    async def wait_for(self, predicate: Callable[[], object], timeout_s: float = 120) -> None:
        start = time.monotonic()
        while time.monotonic() - start < timeout_s:
            if predicate():
                return
            await asyncio.sleep(.2)
        raise RuntimeError("startup condition timed out")

    def contents(self) -> list[str]:
        try:
            return [(self.work / p / "shared.txt").read_text() for p in self.peers]
        except FileNotFoundError:
            return []

    async def setup(self) -> None:
        (self.work / "resolv.conf").write_text("nameserver 10.0.2.3\n")
        for p in self.peers:
            (self.work / p / ".teamtype").mkdir(parents=True)
            holder = await self.spawn(["unshare", "-rmn", "sh", "-c",
                'mount --bind "$1" /etc/resolv.conf && exec sleep infinity',
                "sh", str(self.work / "resolv.conf")], f"{p}.netns.log")
            self.holders[p] = holder
            await asyncio.sleep(.2)
            await self.spawn(["slirp4netns", "--configure", "--mtu=1500",
                              str(holder.pid), "tap0"], f"{p}.slirp.log")
            await asyncio.sleep(1)
            rc, output = await self.command(self.ns(p) + ["ip", "-j", "address"])
            self.event("namespace", peer=p, namespace=os.readlink(f"/proc/{holder.pid}/ns/net"),
                       rc=rc, addresses=output)
            if rc:
                raise RuntimeError(output)
        (self.work / "a/shared.txt").write_text("seed\n" + "".join(f"anchor-{p}\n" for p in self.peers))
        if self.seed_from:
            (self.work / "a/.teamtype/doc").write_bytes((self.seed_from / ".teamtype/doc").read_bytes())
            (self.work / "a/shared.txt").write_bytes((self.seed_from / "shared.txt").read_bytes())
        await self.start_daemon("a")
        def address():
            return re.search(r"peer=[^\s\x1b]+", (self.work / "a.log").read_text())
        await self.wait_for(address)
        match = address()
        assert match is not None
        for p in self.peers[1:]:
            (self.work / p / ".teamtype/config").write_text(match.group() + "\n")
            await self.start_daemon(p)
        await self.wait_for(lambda: len(self.contents()) == len(self.peers) and len(set(self.contents())) == 1)
        await self.spawn(["nvim", "--headless", "--clean", "-n", "--listen", str(self.work / "a.nvim"),
                          "--cmd", f"set runtimepath^={ROOT}/nvim-plugin", "shared.txt"],
                         "a.nvim.log", self.work / "a")
        await self.wait_for(lambda: (self.work / "a.nvim").is_socket())
        await asyncio.sleep(3)

    async def nvim(self, expression: str) -> tuple[int, str]:
        return await self.command(["nvim", "--server", self.work / "a.nvim", "--remote-expr", expression])

    async def edit_agent(self, peer: str, stop: asyncio.Event) -> None:
        while not stop.is_set():
            n = self.counts[peer] + 1
            marker = f"{self.prefix}agent-{peer}-{n:07d}"
            rc, output = await self.command([BINARY, "agent-edit", "--directory", self.work / peer,
                "--file", "shared.txt", "--old", f"anchor-{peer}\n",
                "--new", f"{marker}\nanchor-{peer}\n"], timeout_s=35)
            self.event("agent_edit", peer=peer, marker=marker, rc=rc, output=output)
            if rc == 0:
                self.accepted.add(marker)
                self.counts[peer] = n
            await asyncio.sleep(1)

    async def edit_nvim(self, stop: asyncio.Event) -> None:
        while not stop.is_set():
            marker = f"{self.prefix}nvim-a-{self.counts.get('nvim', 0) + 1:07d}"
            rc, output = await self.nvim(f"nvim_buf_set_lines(0, 1, 1, 0, ['{marker}'])")
            self.event("nvim_edit", marker=marker, rc=rc, output=output)
            if rc == 0:
                self.accepted.add(marker)
                self.counts["nvim"] = self.counts.get("nvim", 0) + 1
            await asyncio.sleep(2)

    async def link(self, peer: str, state: str) -> None:
        rc, output = await self.command(self.ns(peer) + ["ip", "link", "set", "tap0", state])
        self.event("link", peer=peer, state=state, rc=rc, output=output)
        if rc:
            raise RuntimeError(output)
        if state == "up":
            rc, output = await self.command(self.ns(peer) + ["ip", "route", "replace", "default",
                                                            "via", "10.0.2.2", "dev", "tap0"])
            self.event("route_restore", peer=peer, rc=rc, output=output)
            if rc:
                raise RuntimeError(output)

    async def fault(self, cycle: int) -> None:
        await asyncio.sleep(30)
        peer = self.rng.choice(self.peers)
        self.event("fault_plan", cycle=cycle, peer=peer, mode=cycle % 3)
        if cycle % 3 == 0:
            for _ in range(10):
                await self.link(peer, "down")
                await asyncio.sleep(1)
                await self.link(peer, "up")
                await asyncio.sleep(1)
        else:
            await self.link(peer, "down")
            await asyncio.sleep(30 if cycle % 3 == 1 else 90)
            await self.link(peer, "up")
        restored = time.monotonic()
        expected = self.accepted.copy()
        self.event("catchup_start", cycle=cycle, accepted=len(expected))
        while True:
            texts = self.contents()
            missing = {p: sorted(expected - set(t.splitlines())) for p, t in zip(self.peers, texts)}
            elapsed = time.monotonic() - restored
            if len(texts) == len(self.peers) and not any(missing.values()):
                self.event("catchup_end", cycle=cycle, ok=True, duration_s=elapsed)
                if elapsed >= self.catchup_limit_s:
                    self.failures.append(dict(cycle=cycle, error="slow catch-up", duration_s=elapsed))
                return
            if elapsed >= 120:
                self.event("catchup_end", cycle=cycle, ok=False, duration_s=elapsed, missing=missing)
                self.failures.append(dict(cycle=cycle, error="catch-up timed out", missing=missing))
                return
            await asyncio.sleep(.2)

    async def check(self, cycle: int) -> None:
        started = time.monotonic()
        self.event("check_start", cycle=cycle, accepted=len(self.accepted))
        result: dict[str, object]
        while True:
            texts = self.contents()
            rc, buf = await self.nvim('join(getline(1, "$"), "\\n")')
            equal = len(texts) == len(self.peers) and len(set(texts)) == 1
            lines = texts[0].splitlines() if texts else []
            missing = self.accepted - set(lines)
            duplicates = len(lines) - len(set(lines))
            buffer_equal = bool(texts) and rc == 0 and buf.rstrip("\n") == texts[0].rstrip("\n")
            elapsed = time.monotonic() - started
            if equal and not missing and not duplicates and buffer_equal:
                result = dict(cycle=cycle, ok=True, duration_s=elapsed, accepted=len(self.accepted))
                break
            if elapsed >= 120:
                result = dict(cycle=cycle, ok=False, duration_s=elapsed, files_equal=equal,
                    buffer_equal=buffer_equal, missing=sorted(missing), duplicates=duplicates,
                    hashes=[hashlib.sha256(t.encode()).hexdigest() for t in texts])
                for p, text in zip(self.peers, texts):
                    (self.work / f"failure-{cycle}-{p}.txt").write_text(text)
                (self.work / f"failure-{cycle}-buffer.txt").write_text(buf)
                self.failures.append(result)
                break
            await asyncio.sleep(.5)
        self.checks.append(result)
        self.event("check_end", **result)

    async def run(self) -> None:
        try:
            await self.setup()
            started = time.monotonic()
            self.event("soak_start", duration_s=self.duration_s, peers=self.peers, seed=self.seed, binary=str(BINARY))
            cycle = self.first_cycle
            while time.monotonic() - started < self.duration_s:
                previous_counts = self.counts.copy()
                stop = asyncio.Event()
                editors = [asyncio.create_task(self.edit_agent(p, stop)) for p in self.peers]
                editors.append(asyncio.create_task(self.edit_nvim(stop)))
                fault = asyncio.create_task(self.fault(cycle))
                await asyncio.sleep(min(180, max(0, self.duration_s - (time.monotonic() - started))))
                await fault
                stop.set()
                await asyncio.gather(*editors)
                for source in [*self.peers, "nvim"]:
                    if self.counts.get(source, 0) == previous_counts.get(source, 0):
                        result: dict[str, object] = dict(cycle=cycle, source=source, error="no successful edits in cycle")
                        self.failures.append(result)
                        self.event("progress_failure", **result)
                await self.check(cycle)
                for p, proc in self.daemons.items():
                    if proc.returncode is not None:
                        raise RuntimeError(f"daemon {p} exited: {proc.returncode}")
                cycle += 1
            self.event("soak_end", elapsed_s=time.monotonic() - started, counts=self.counts,
                       checks=len(self.checks), failures=len(self.failures))
            if self.failures:
                raise RuntimeError(f"{len(self.failures)} soak checks failed; see events.jsonl")
        finally:
            for proc in reversed(self.processes):
                if proc.returncode is None:
                    try:
                        os.killpg(proc.pid, signal.SIGTERM)
                    except ProcessLookupError:
                        pass
            await asyncio.gather(*(p.wait() for p in self.processes))
            await asyncio.gather(*self.tasks)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, required=True)
    parser.add_argument("--duration-s", type=float, default=10800)
    parser.add_argument("--seed-from", type=Path)
    parser.add_argument("--first-cycle", type=int, default=0)
    parser.add_argument("--joiners", type=int, choices=[2, 3, 4], default=2)
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--catchup-limit-s", type=float, default=10)
    args = parser.parse_args()
    args.work.mkdir(parents=True, exist_ok=True)
    asyncio.run(Soak(args.work.resolve(), args.duration_s, args.seed_from, args.first_cycle,
                     args.joiners, args.seed, args.catchup_limit_s).run())
