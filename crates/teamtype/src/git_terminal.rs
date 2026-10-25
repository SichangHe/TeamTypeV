// SPDX-FileCopyrightText: 2026 Sichang He
// SPDX-License-Identifier: AGPL-3.0-or-later

//! Terminal Git uses the ordinary input spool with length-prefixed terminal events.
//! Independent spool readers handle controls and PTY input, so a blocked PTY write
//! cannot delay signals or resizing. Both readers use bounded frame buffers.

use std::io::{IsTerminal, Read, Write};
use std::os::fd::{AsRawFd, RawFd};
use std::os::unix::ffi::OsStringExt;
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::time::Duration;

use anyhow::{Context, Result, bail};
use nix::fcntl::{FcntlArg, OFlag, fcntl};
use nix::sys::signal::{Signal, killpg};
use nix::sys::termios::{
    SetArg, SpecialCharacterIndices, Termios, cfmakeraw, tcgetattr, tcsetattr,
};
use portable_pty::{CommandBuilder, PtySize, native_pty_system};
use serde::{Deserialize, Serialize};
use tokio::io::unix::AsyncFd;
use tokio::net::unix::OwnedWriteHalf;
use tokio::signal::unix::{Signal as SignalStream, SignalKind, signal};

use super::{INPUT_CHUNK, InputReader, Job, ProcessGroup, Response, send_output, write_frame};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub(super) struct Terminal {
    size: [u16; 2],
    term: String,
}

impl Terminal {
    pub fn detect() -> Result<Option<Self>> {
        if !std::io::stdin().is_terminal() || !std::io::stdout().is_terminal() {
            return Ok(None);
        }
        Ok(Some(Self {
            size: size()?,
            term: std::env::var("TERM").unwrap_or_else(|_| "xterm".into()),
        }))
    }

    fn pty_size(&self) -> PtySize {
        PtySize {
            rows: self.size[0],
            cols: self.size[1],
            ..PtySize::default()
        }
    }
}

#[derive(Serialize, Deserialize)]
enum Event {
    Input(Vec<u8>),
    Resize([u16; 2]),
    Signal(i32),
}

fn size() -> Result<[u16; 2]> {
    let output = std::process::Command::new("stty")
        .arg("size")
        .stdin(std::process::Stdio::inherit())
        .output()?;
    let text = std::str::from_utf8(&output.stdout)?;
    let mut values = text.split_whitespace().map(str::parse::<u16>);
    Ok([
        values.next().context("Missing terminal rows")??,
        values.next().context("Missing terminal columns")??,
    ])
}

struct RawTerminal(Termios);

impl Drop for RawTerminal {
    fn drop(&mut self) {
        let _ = tcsetattr(std::io::stdin(), SetArg::TCSANOW, &self.0);
    }
}

fn nonblocking(fd: RawFd) -> Result<()> {
    let flags = OFlag::from_bits_truncate(fcntl(fd, FcntlArg::F_GETFL)?);
    fcntl(fd, FcntlArg::F_SETFL(flags | OFlag::O_NONBLOCK))?;
    Ok(())
}

pub(super) struct Client {
    restore: RawTerminal,
    started: tokio::sync::watch::Receiver<bool>,
    tty: AsyncFd<std::fs::File>,
    resize: SignalStream,
    interrupt: SignalStream,
    quit: SignalStream,
    terminate: SignalStream,
    hangup: SignalStream,
}

impl Client {
    pub fn new(started: tokio::sync::watch::Receiver<bool>) -> Result<Self> {
        let resize = signal(SignalKind::window_change())?;
        let interrupt = signal(SignalKind::interrupt())?;
        let quit = signal(SignalKind::quit())?;
        let terminate = signal(SignalKind::terminate())?;
        let hangup = signal(SignalKind::hangup())?;
        let file = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .open(nix::unistd::ttyname(std::io::stdin())?)?;
        nonblocking(file.as_raw_fd())?;
        let tty = AsyncFd::new(file)?;
        let original = tcgetattr(std::io::stdin())?;
        let mut raw = original.clone();
        cfmakeraw(&mut raw);
        let restore = RawTerminal(original);
        tcsetattr(std::io::stdin(), SetArg::TCSANOW, &raw)?;
        Ok(Self {
            restore,
            started,
            tty,
            resize,
            interrupt,
            quit,
            terminate,
            hangup,
        })
    }

    pub async fn input(&mut self, writer: &mut OwnedWriteHalf) -> Result<i32> {
        let Self {
            restore,
            started,
            tty,
            resize,
            interrupt,
            quit,
            terminate,
            hangup,
        } = self;
        let mut bytes = vec![0; INPUT_CHUNK];
        loop {
            let event = tokio::select! {
                ready = tty.readable() => {
                    let mut ready = ready?;
                    let count = match ready.try_io(|tty| tty.get_ref().read(&mut bytes)) {
                        Ok(result) => result?,
                        Err(_) => continue,
                    };
                    if count == 0 { bail!("Terminal input closed"); }
                    Event::Input(bytes[..count].to_vec())
                }
                _ = resize.recv() => Event::Resize(size()?),
                _ = interrupt.recv() => Event::Signal(Signal::SIGINT as i32),
                _ = quit.recv() => Event::Signal(Signal::SIGQUIT as i32),
                _ = terminate.recv() => Event::Signal(Signal::SIGTERM as i32),
                _ = hangup.recv() => Event::Signal(Signal::SIGHUP as i32),
            };
            if !*started.borrow() {
                match &event {
                    Event::Signal(number) => return Ok(128 + number),
                    Event::Input(bytes) => {
                        for (index, signal) in [
                            (SpecialCharacterIndices::VINTR, Signal::SIGINT),
                            (SpecialCharacterIndices::VQUIT, Signal::SIGQUIT),
                        ] {
                            let byte = restore.0.control_chars[index as usize];
                            if byte != 0 && bytes.contains(&byte) {
                                return Ok(128 + signal as i32);
                            }
                        }
                    }
                    Event::Resize(_) => {}
                }
            }
            let bytes = postcard::to_allocvec(&event)?;
            let mut frame = (bytes.len() as u32).to_be_bytes().to_vec();
            frame.extend(bytes);
            for chunk in frame.chunks(INPUT_CHUNK) {
                write_frame(writer, &chunk).await?;
            }
        }
    }
}

/// Readiness registration; the separately owned master outlives this value.
struct Pty(RawFd);

impl AsRawFd for Pty {
    fn as_raw_fd(&self) -> RawFd {
        self.0
    }
}

async fn read_event(input: &mut InputReader, pending: &mut Vec<u8>) -> Result<Event> {
    loop {
        if pending.len() >= 4 {
            let len = u32::from_be_bytes(pending[..4].try_into()?) as usize;
            if len > INPUT_CHUNK + 64 {
                bail!("Terminal event too large");
            }
            if pending.len() >= 4 + len {
                let event = postcard::from_bytes(&pending[4..4 + len])?;
                pending.drain(..4 + len);
                return Ok(event);
            }
        }
        let mut bytes = vec![0; INPUT_CHUNK];
        let count = input.read(&mut bytes).await?;
        if count == 0 {
            bail!("Terminal input ended");
        }
        pending.extend_from_slice(&bytes[..count]);
    }
}

pub(super) async fn execute(
    job: &Job,
    program: PathBuf,
    root: &Path,
    cwd: &Path,
    terminal: &Terminal,
) -> Result<i32> {
    let pair = native_pty_system().openpty(terminal.pty_size())?;
    let mut command = CommandBuilder::new(program);
    for (key, _) in std::env::vars_os() {
        if key.as_encoded_bytes().starts_with(b"GIT_") {
            command.env_remove(key);
        }
    }
    command.args(
        job.request
            .args
            .iter()
            .cloned()
            .map(std::ffi::OsString::from_vec),
    );
    command.cwd(cwd);
    command.env("TERM", &terminal.term);
    command.env("GIT_CEILING_DIRECTORIES", root.parent().unwrap_or(root));
    let mut child: Box<dyn portable_pty::Child> = pair.slave.spawn_command(command)?;
    let child = child
        .downcast_mut::<std::process::Child>()
        .context("PTY did not spawn a Unix child")?;
    let mut group = ProcessGroup {
        pid: child.id(),
        terminating: false,
    };
    drop(pair.slave);
    let fd = pair
        .master
        .as_raw_fd()
        .context("PTY has no Unix descriptor")?;
    nonblocking(fd)?;
    let mut reader = pair.master.try_clone_reader()?;
    let mut writer = pair.master.take_writer()?;
    let mut master = pair.master;
    let pty = AsyncFd::new(Pty(fd))?;
    let mut input = job.input.reader().await?;
    let mut controls = job.input.reader().await?;
    send_output(&job.response, Response::Started).await?;
    let mut output = vec![0; INPUT_CHUNK];
    let mut tick = tokio::time::interval(Duration::from_millis(20));
    let mut status: Option<std::process::ExitStatus> = None;
    let mut eof = false;
    let mut pending = Vec::new();
    let mut pending_controls = Vec::new();
    let mut writing = Vec::new();
    let mut written = 0;
    let mut input_open = true;
    let result = async {
        let master = &mut master;
        loop {
            if eof && let Some(status) = &status {
                return Ok(status.code().unwrap_or_else(|| 128 + status.signal().unwrap_or(1)));
            }
            tokio::select! {
                () = job.response.closed() => bail!("Git client disconnected"),
                _ = tick.tick() => {
                    if status.is_none() && let Some(exited) = child.try_wait()? {
                        status = Some(exited);
                        group.terminate();
                    }
                }
                ready = pty.readable(), if !eof => {
                    let mut ready = ready?;
                    let count = match ready.try_io(|_| reader.read(&mut output)) {
                        Ok(Ok(count)) => count,
                        Ok(Err(error)) if error.raw_os_error() == Some(nix::libc::EIO) => 0,
                        Ok(Err(error)) => return Err(error.into()),
                        Err(_) => continue,
                    };
                    eof = count == 0;
                    if !eof { send_output(&job.response, Response::Stdout(output[..count].to_vec())).await?; }
                }
                ready = pty.writable(), if input_open && written < writing.len() => {
                    let mut ready = ready?;
                    match ready.try_io(|_| writer.write(&writing[written..])) {
                        Ok(Ok(0)) => bail!("PTY stopped accepting input"),
                        Ok(Ok(count)) => written += count,
                        Ok(Err(error)) if error.raw_os_error() == Some(nix::libc::EIO) => input_open = false,
                        Ok(Err(error)) => return Err(error.into()),
                        Err(_) => {}
                    }
                }
                event = read_event(&mut input, &mut pending), if input_open && status.is_none() && written == writing.len() => {
                    if let Event::Input(bytes) = event? {
                        writing = bytes;
                        written = 0;
                    }
                }
                event = read_event(&mut controls, &mut pending_controls), if status.is_none() => {
                    match event? {
                        Event::Input(_) => {}
                        Event::Resize(size) => master.resize(PtySize {
                            rows: size[0], cols: size[1], ..PtySize::default()
                        })?,
                        Event::Signal(number) => {
                            let signal = Signal::try_from(number)?;
                            if ![Signal::SIGINT, Signal::SIGQUIT, Signal::SIGTERM, Signal::SIGHUP].contains(&signal) {
                                bail!("Unsupported terminal signal");
                            }
                            let pid = master.process_group_leader().unwrap_or(group.pid as i32);
                            let _ = killpg(nix::unistd::Pid::from_raw(pid), signal);
                        }
                    }
                }
            }
        }
    }.await;
    group.terminate();
    let cleanup = tokio::time::timeout(Duration::from_secs(2), async {
        loop {
            let _ = child.try_wait();
            if killpg(nix::unistd::Pid::from_raw(group.pid as i32), None).is_err() {
                break;
            }
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    })
    .await;
    if cleanup.is_err() {
        group.signal(Signal::SIGKILL);
    }
    let _ = child.try_wait();
    result
}
