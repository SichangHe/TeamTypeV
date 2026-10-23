#!/usr/bin/env python3
"""Delay a real relay's HTTP upgrade by five seconds, then run an outage trial."""

import asyncio
import os
from pathlib import Path
import ssl
import sys

from .soak import Soak


async def main() -> None:
    work = Path(sys.argv[1])
    work.mkdir(parents=True, exist_ok=False)
    soak = Soak(work, 180, first_cycle=1, catchup_limit_s=120)
    tasks: set[asyncio.Task[None]] = set()

    async def proxy(reader: asyncio.StreamReader, writer: asyncio.StreamWriter) -> None:
        upstream = None
        try:
            header = await asyncio.wait_for(reader.readuntil(b"\r\n\r\n"), 10)
            if b"upgrade:" in header.lower():
                soak.event("relay_delay", delay_s=5, request=header.splitlines()[0].decode())
                await asyncio.sleep(5)
            remote, upstream = await asyncio.open_connection(
                "usw1-1.relay.n0.iroh.link", 443, ssl=ssl.create_default_context())
            upstream.write(header)
            await upstream.drain()

            async def copy(source: asyncio.StreamReader, target: asyncio.StreamWriter) -> None:
                while data := await source.read(65536):
                    target.write(data)
                    await target.drain()

            pumps = [asyncio.create_task(copy(reader, upstream)),
                     asyncio.create_task(copy(remote, writer))]
            try:
                _ = await asyncio.wait(pumps, return_when=asyncio.FIRST_COMPLETED)
            finally:
                for task in pumps:
                    _ = task.cancel()
                _ = await asyncio.gather(*pumps, return_exceptions=True)
        except (OSError, TimeoutError, asyncio.IncompleteReadError) as exc:
            soak.event("relay_proxy_error", error=str(exc))
        finally:
            writer.close()
            if upstream:
                upstream.close()

    def accept(reader: asyncio.StreamReader, writer: asyncio.StreamWriter) -> None:
        task = asyncio.create_task(proxy(reader, writer))
        tasks.add(task)
        task.add_done_callback(tasks.discard)

    server = await asyncio.start_server(accept, "0.0.0.0", 0)
    soak.relay = f"http://10.0.2.2:{server.sockets[0].getsockname()[1]}"
    try:
        async with server:
            await soak.run()
    finally:
        for task in tasks:
            _ = task.cancel()
        _ = await asyncio.gather(*tasks, return_exceptions=True)


if __name__ == "__main__":
    _ = os.environ.setdefault("RUST_LOG", "info,teamtype::peer=debug,iroh=debug")
    asyncio.run(main())
