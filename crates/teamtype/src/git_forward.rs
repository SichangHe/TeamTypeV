// SPDX-FileCopyrightText: 2026 Sichang He
// SPDX-License-Identifier: AGPL-3.0-or-later

//! Git executes only on the sharer, after the requesting peer's document changes arrive.

use std::ffi::OsString;
use std::io::IsTerminal;
use std::os::unix::ffi::{OsStrExt, OsStringExt};
use std::os::unix::fs::PermissionsExt;
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::Stdio;
use std::sync::{
    Arc,
    atomic::{AtomicU64, Ordering},
};
use std::time::Duration;

use anyhow::{Context, Result, bail};
use automerge::ChangeHash;
use serde::{Deserialize, Serialize, de::DeserializeOwned};
use tokio::io::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt};
use tokio::net::{UnixListener, UnixStream};
use tokio::process::Command;
use tokio::sync::{broadcast, mpsc};
use tokio::time::timeout;

use crate::daemon::DocumentActorHandle;

#[path = "git_terminal.rs"]
mod terminal;

const MAX_FRAME: usize = 64 * 1024 * 1024;
const CONNECT_TIMEOUT: Duration = Duration::from_secs(10);
pub(crate) const OUTPUT_TIMEOUT: Duration = Duration::from_mins(3);
pub(crate) const INPUT_CHUNK: usize = 16384;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Request {
    pub id: u64,
    args: Vec<Vec<u8>>,
    cwd: Vec<u8>,
    pub heads: Vec<ChangeHash>,
    terminal: Option<terminal::Terminal>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Response {
    Accepted,
    Queued(String),
    Stdout(Vec<u8>),
    Stderr(Vec<u8>),
    Exit(i32, Vec<ChangeHash>),
    Error(String),
    Started,
}

impl Response {
    pub fn finished(&self) -> bool {
        matches!(self, Self::Exit(..) | Self::Error(_))
    }
}

#[derive(Clone, Debug)]
pub struct Job {
    pub request: Request,
    pub response: mpsc::Sender<Response>,
    pub input: Input,
}

#[derive(Clone, Debug)]
pub struct Input {
    file: Arc<tempfile::NamedTempFile>,
    complete: tokio::sync::watch::Receiver<bool>,
}

pub struct InputWriter {
    file: std::fs::File,
    complete: tokio::sync::watch::Sender<bool>,
}

impl Input {
    pub fn new() -> Result<(Self, InputWriter)> {
        let file = Arc::new(tempfile::NamedTempFile::new()?);
        let (complete, receiver) = tokio::sync::watch::channel(false);
        let writer = InputWriter {
            file: file.reopen()?,
            complete,
        };
        Ok((
            Self {
                file,
                complete: receiver,
            },
            writer,
        ))
    }

    pub async fn reader(&self) -> Result<InputReader> {
        Ok(InputReader {
            file: tokio::fs::File::open(self.file.path()).await?,
            complete: self.complete.clone(),
        })
    }
}

impl InputWriter {
    pub fn write(&mut self, bytes: &[u8]) -> Result<()> {
        use std::io::Write;
        if bytes.len() > INPUT_CHUNK {
            bail!("Git stdin chunk exceeds 16 KiB");
        }
        self.file.write_all(bytes)?;
        self.complete.send_replace(bytes.is_empty());
        Ok(())
    }
}

pub struct InputReader {
    file: tokio::fs::File,
    complete: tokio::sync::watch::Receiver<bool>,
}

impl InputReader {
    pub async fn read(&mut self, bytes: &mut [u8]) -> Result<usize> {
        loop {
            let complete = *self.complete.borrow_and_update();
            let count = self.file.read(bytes).await?;
            if count != 0 || complete {
                return Ok(count);
            }
            self.complete
                .changed()
                .await
                .context("Git stdin upload cancelled")?;
        }
    }
}

#[derive(Clone)]
pub struct GitHandle {
    pub outgoing: broadcast::Sender<Job>,
    queue: Arc<std::sync::OnceLock<mpsc::Sender<Job>>>,
    next_id: Arc<AtomicU64>,
}

impl Default for GitHandle {
    fn default() -> Self {
        Self::new()
    }
}

impl GitHandle {
    pub fn new() -> Self {
        Self {
            outgoing: broadcast::channel(32).0,
            queue: Arc::default(),
            next_id: Arc::default(),
        }
    }

    pub async fn enqueue(&self, job: Job) -> Result<()> {
        self.queue
            .get()
            .context("Git worker is not running")?
            .send(job)
            .await
            .context("Git worker stopped")
    }
}

pub fn excluded(path: &Path) -> bool {
    path.components().any(|component| {
        [".teamtype", ".git", ".hg", ".jj", ".bzr", ".pijul", ".svn"]
            .iter()
            .any(|name| component.as_os_str() == *name)
    })
}

fn git_program() -> Result<PathBuf> {
    std::env::split_paths(&std::env::var_os("PATH").unwrap_or_default())
        .filter(|path| !path.ends_with(".teamtype/bin"))
        .map(|path| path.join("git"))
        .filter_map(|path| path.canonicalize().ok())
        .find(|path| {
            std::fs::metadata(path)
                .is_ok_and(|meta| meta.is_file() && meta.permissions().mode() & 0o111 != 0)
        })
        .context("Git is not installed on the sharer")
}

pub fn remove_old_hook(root: &Path) {
    let mut hooks = vec![root.join(".git/hooks/reference-transaction")];
    if let Ok(repo) = git2::Repository::open(root) {
        hooks.push(repo.path().join("hooks/reference-transaction"));
        if let Ok(config) = repo.config()
            && let Ok(path) = config.get_path("core.hooksPath")
        {
            hooks.push(root.join(path).join("reference-transaction"));
        }
    }
    for hook in hooks {
        if std::fs::read_to_string(&hook).is_ok_and(|text| text.contains("Installed by teamtype"))
            && let Err(error) = std::fs::remove_file(&hook)
        {
            tracing::warn!(
                "Could not remove old Teamtype Git hook {}: {error}",
                hook.display()
            );
        }
    }
}

fn bind_socket(root: &Path) -> Result<(UnixListener, std::fs::File)> {
    let socket = root.join(".teamtype/git.sock");
    let lock = std::fs::File::create(socket.with_extension("lock"))?;
    lock.try_lock()
        .context("Another Git listener owns this shared directory")?;
    if socket.exists() {
        std::fs::remove_file(&socket)?;
    }
    let private = tempfile::tempdir_in(socket.parent().context("Missing socket directory")?)?;
    let private_socket = private.path().join("git.sock");
    let listener = UnixListener::bind(&private_socket)?;
    std::fs::set_permissions(&private_socket, std::fs::Permissions::from_mode(0o600))?;
    std::fs::rename(&private_socket, &socket)?;
    Ok((listener, lock))
}

pub fn start(handle: DocumentActorHandle) -> Result<()> {
    let (listener, lock) = bind_socket(handle.base_dir())?;
    if !handle.is_host() {
        install_wrapper(handle.base_dir())?;
    }
    let (queue, mut receiver) = mpsc::channel::<Job>(32);
    handle
        .git
        .queue
        .set(queue)
        .map_err(|_| anyhow::anyhow!("Git listener already started"))?;
    let worker_handle = handle.clone();
    tokio::spawn(async move {
        let mut waiting = std::collections::VecDeque::new();
        loop {
            let job = match waiting.pop_front() {
                Some(job) => job,
                None => match receiver.recv().await {
                    Some(job) => job,
                    None => break,
                },
            };
            if job.response.is_closed() {
                continue;
            }
            let command = job
                .request
                .args
                .iter()
                .map(|arg| String::from_utf8_lossy(arg))
                .collect::<Vec<_>>()
                .join(" ");
            let execution = execute(&worker_handle, &job);
            tokio::pin!(execution);
            let result = loop {
                tokio::select! {
                    result = &mut execution => break result,
                    Some(queued) = receiver.recv(), if waiting.len() < 32 => {
                        let _ = queued.response.try_send(Response::Queued(command.clone()));
                        waiting.push_back(queued);
                    }
                }
            };
            if let Err(error) = result {
                worker_handle.git_finished().await;
                let _ = timeout(
                    CONNECT_TIMEOUT,
                    job.response.send(Response::Error(format!("{error:#}"))),
                )
                .await;
            }
        }
    });
    tokio::spawn(async move {
        let _lock = lock;
        while let Ok((socket, _)) = listener.accept().await {
            let handle = handle.clone();
            tokio::spawn(async move {
                if let Err(error) = serve(socket, handle).await {
                    tracing::debug!("Git client disconnected: {error:#}");
                }
            });
        }
    });
    Ok(())
}

// 🧑 "Is there a way to get git working directly by having something like a virtual environment?"
fn install_wrapper(root: &Path) -> Result<()> {
    let bin = root.join(".teamtype/bin");
    std::fs::create_dir_all(&bin)?;
    let exe = wrapper_executable(&std::env::current_exe()?);
    let quoted = exe
        .to_str()
        .context("Executable path is not UTF-8")?
        .replace('\'', "'\\''");
    let wrapper = bin.join("git");
    std::fs::write(
        &wrapper,
        format!("#!/bin/sh\nexec '{quoted}' git -- \"$@\"\n"),
    )?;
    std::fs::set_permissions(wrapper, std::fs::Permissions::from_mode(0o755))?;
    let path = bin.to_str().context("Shared path is not UTF-8")?;
    std::fs::write(
        root.join(".teamtype/activate"),
        include_str!("git_activate.sh")
            .replace("@BIN@", &format!("'{}'", path.replace('\'', "'\\''"))),
    )?;
    std::fs::write(
        root.join(".teamtype/activate.fish"),
        include_str!("git_activate.fish").replace(
            "@BIN@",
            &format!("'{}'", path.replace('\\', "\\\\").replace('\'', "\\'")),
        ),
    )?;
    tracing::info!(
        "Git runs on the sharer. Use `teamtype git ...`, or source {} (fish: activate.fish).",
        root.join(".teamtype/activate").display()
    );
    Ok(())
}

fn wrapper_executable(path: &Path) -> PathBuf {
    PathBuf::from(OsString::from_vec(
        path.as_os_str()
            .as_bytes()
            .strip_suffix(b" (deleted)")
            .unwrap_or_else(|| path.as_os_str().as_bytes())
            .to_vec(),
    ))
}

async fn serve(mut socket: UnixStream, handle: DocumentActorHandle) -> Result<()> {
    let mut request: Request = read_frame(&mut socket).await?;
    let (input, mut input_writer) = Input::new()?;
    request.id = handle.git.next_id.fetch_add(1, Ordering::Relaxed);
    request.heads = handle.git_heads().await;
    let (response, mut responses) = mpsc::channel(8);
    let job = Job {
        request,
        response,
        input,
    };
    if handle.is_host() {
        job.response.send(Response::Accepted).await?;
        handle.git.enqueue(job).await?;
    } else if handle.git.outgoing.send(job).is_err() {
        write_frame(
            &mut socket,
            &Response::Error("The sharer is offline; reconnect before running Git".into()),
        )
        .await?;
        return Ok(());
    }
    let (mut reader, mut writer) = socket.into_split();
    let output = async {
        let first = timeout(CONNECT_TIMEOUT, responses.recv()).await;
        let response = match first {
        Ok(Some(response)) => response,
        _ => Response::Error("The sharer is offline or did not answer the Git request; it may have run. Check status before retrying".into()),
    };
        write_frame(&mut writer, &response).await?;
        if response.finished() {
            return Ok(());
        }
        loop {
            let Some(response) = responses.recv().await else {
                break;
            };
            if let Response::Exit(_, heads) = &response {
                let ready = timeout(CONNECT_TIMEOUT, async {
                    while !handle.git_ready(heads.clone()).await? {
                        tokio::time::sleep(Duration::from_millis(10)).await;
                    }
                    Ok::<(), anyhow::Error>(())
                })
                .await
                .context("Git finished but its file changes did not arrive")
                .and_then(|result| result);
                if let Err(error) = ready {
                    write_frame(
                        &mut writer,
                        &Response::Stderr(
                            format!("Warning: {error:#}; local files may still be synchronizing\n")
                                .into_bytes(),
                        ),
                    )
                    .await?;
                }
            }
            timeout(OUTPUT_TIMEOUT, write_frame(&mut writer, &response))
                .await
                .context("Git output was not consumed for three minutes")??;
            if response.finished() {
                return Ok(());
            }
        }
        write_frame(
            &mut writer,
            &Response::Error(
                "Connection to the sharer was lost; Git may have run. Check status before retrying"
                    .into(),
            ),
        )
        .await
    };
    tokio::select! {
        result = async {
            receive_input(&mut reader, &mut input_writer).await?;
            reader.read_u8().await?;
            Ok(())
        } => result,
        result = output => result,
    }
}

// 🧑 "Maybe we just intercept all the git stuff and forward them to the server?"
async fn execute(handle: &DocumentActorHandle, job: &Job) -> Result<()> {
    if let Err(error) = validate_args(&job.request.args) {
        job.response
            .send(Response::Stderr(format!("{error}\n").into_bytes()))
            .await?;
        job.response.send(Response::Exit(129, vec![])).await?;
        return Ok(());
    }
    if !handle.is_host() {
        bail!("Only the sharer executes Git");
    }
    timeout(CONNECT_TIMEOUT, async {
        while !handle.git_ready(job.request.heads.clone()).await? {
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
        Ok::<(), anyhow::Error>(())
    })
    .await
    .context("The joiner's edits did not reach the sharer; Git was not run")??;
    let root = handle.base_dir().canonicalize()?;
    remove_old_hook(&root);
    let repository = git2::Repository::open(&root)
        .context("The shared directory must have its own Git repository")?;
    if repository
        .workdir()
        .and_then(|path| path.canonicalize().ok())
        .as_ref()
        != Some(&root)
    {
        bail!("The shared directory must have its own Git repository");
    }
    let cwd = root
        .join(OsString::from_vec(job.request.cwd.clone()))
        .canonicalize().context("Git working directory does not exist on the sharer; empty directories are not synchronized")?;
    if !cwd.starts_with(&root) {
        bail!("Git working directory must be inside the shared directory");
    }
    if let Some(terminal) = &job.request.terminal {
        let code = terminal::execute(job, git_program()?, &root, &cwd, terminal).await?;
        handle.git_finished().await;
        job.response
            .send(Response::Exit(code, handle.git_heads().await))
            .await?;
        return Ok(());
    }
    let mut command = group_command(git_program()?);
    for (key, _) in std::env::vars_os() {
        if key.as_bytes().starts_with(b"GIT_") {
            command.env_remove(key);
        }
    }
    let mut child = command
        .args(["--no-pager", "-c", "color.ui=false"])
        .args(job.request.args.iter().cloned().map(OsString::from_vec))
        .current_dir(cwd)
        .env("GIT_TERMINAL_PROMPT", "0")
        .env("GIT_CEILING_DIRECTORIES", root.parent().unwrap_or(&root))
        .env("GIT_ASKPASS", "false")
        .env("SSH_ASKPASS", "false")
        .env("SSH_ASKPASS_REQUIRE", "force")
        .env("GIT_SSH_COMMAND", "ssh -o BatchMode=yes")
        .env("GIT_EDITOR", "false")
        .env("GIT_SEQUENCE_EDITOR", "false")
        .env("GIT_PAGER", "cat")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .context("Could not start Git on the sharer")?;
    let mut group = ProcessGroup {
        pid: child.id().context("Missing Git PID")?,
        terminating: false,
    };
    let mut stdin = child.stdin.take().context("Missing Git stdin")?;
    let mut input = job.input.reader().await?;
    let input_task = tokio::spawn(async move {
        let mut bytes = vec![0; INPUT_CHUNK];
        while let Ok(count) = input.read(&mut bytes).await {
            if count == 0 || stdin.write_all(&bytes[..count]).await.is_err() {
                break;
            }
        }
    });
    let mut stdout = child.stdout.take().context("Missing Git stdout")?;
    let mut stderr = child.stderr.take().context("Missing Git stderr")?;
    let mut out = [0; 16384];
    let mut err = [0; 16384];
    let (mut out_open, mut err_open) = (true, true);
    let mut status = None;
    let result = tokio::select! {
        result = async {
            while out_open || err_open {
                tokio::select! {
                    result = child.wait(), if status.is_none() => {
                        status = Some(result?);
                        group.terminate();
                    }
                    count = stdout.read(&mut out), if out_open => {
                        let count = count?;
                        out_open = count != 0;
                        if out_open {
                            send_output(&job.response, Response::Stdout(out[..count].to_vec())).await?;
                        }
                    }
                    count = stderr.read(&mut err), if err_open => {
                        let count = count?;
                        err_open = count != 0;
                        if err_open {
                            send_output(&job.response, Response::Stderr(err[..count].to_vec())).await?;
                        }
                    }
                }
            }
            if let Some(status) = status {
                Ok(status)
            } else {
                child.wait().await.map_err(anyhow::Error::from)
            }
        } => result,
        () = job.response.closed() => Err(anyhow::anyhow!("Git client disconnected")),
    };
    input_task.abort();
    let status = match result {
        Ok(status) => status,
        Err(error) => {
            group.terminate();
            let stopped = timeout(Duration::from_secs(2), async {
                loop {
                    let _ = child.try_wait();
                    if nix::sys::signal::killpg(nix::unistd::Pid::from_raw(group.pid as i32), None)
                        .is_err()
                    {
                        break;
                    }
                    tokio::time::sleep(Duration::from_millis(20)).await;
                }
            })
            .await;
            if stopped.is_err() {
                group.signal(nix::sys::signal::Signal::SIGKILL);
            }
            let _ = child.wait().await;
            return Err(error);
        }
    };
    handle.git_finished().await;
    let heads = handle.git_heads().await;
    job.response
        .send(Response::Exit(
            status
                .code()
                .unwrap_or_else(|| 128 + status.signal().unwrap_or(1)),
            heads,
        ))
        .await?;
    Ok(())
}

async fn read_frame<R: AsyncRead + Unpin, T: DeserializeOwned>(reader: &mut R) -> Result<T> {
    let len = reader.read_u32().await? as usize;
    if len > MAX_FRAME {
        bail!("Git request exceeds 64 MiB");
    }
    let mut bytes = vec![0; len];
    reader.read_exact(&mut bytes).await?;
    Ok(postcard::from_bytes(&bytes)?)
}

async fn write_frame<W: AsyncWrite + Unpin + Send, T: Serialize + Sync>(
    writer: &mut W,
    value: &T,
) -> Result<()> {
    let bytes = postcard::to_allocvec(value)?;
    if bytes.len() > MAX_FRAME {
        bail!("Git request exceeds 64 MiB");
    }
    writer.write_u32(bytes.len() as u32).await?;
    writer.write_all(&bytes).await?;
    Ok(())
}

pub async fn client(directory: Option<&Path>, args: Vec<OsString>) -> Result<i32> {
    let current = std::env::current_dir()?;
    let root = match directory {
        Some(directory) => directory.canonicalize()?,
        None => current
            .ancestors()
            .find(|dir| dir.join(".teamtype").is_dir())
            .context("No shared directory found; run inside it or use --directory")?
            .to_path_buf(),
    };
    let cwd = current
        .strip_prefix(&root)
        .unwrap_or_else(|_| Path::new(""));
    let mut socket = UnixStream::connect(root.join(".teamtype/git.sock"))
        .await
        .context("Teamtype daemon is offline; start share or join before running Git")?;
    let request = Request {
        id: 0,
        args: args.into_iter().map(OsString::into_vec).collect(),
        cwd: cwd.as_os_str().as_bytes().to_vec(),
        heads: vec![],
        terminal: terminal::Terminal::detect()?,
    };
    let (started, running) = tokio::sync::watch::channel(false);
    let mut terminal = request
        .terminal
        .as_ref()
        .map(|_| terminal::Client::new(running))
        .transpose()?;
    write_frame(&mut socket, &request).await?;
    let (mut reader, mut writer) = socket.into_split();
    let input = async {
        if let Some(terminal) = &mut terminal {
            return terminal.input(&mut writer).await;
        } else if std::io::stdin().is_terminal() {
            write_frame(&mut writer, &Vec::<u8>::new()).await?;
        } else {
            let (sender, mut chunks) = mpsc::channel(1);
            std::thread::spawn(move || {
                use std::io::Read;
                loop {
                    let mut bytes = vec![0; INPUT_CHUNK];
                    let chunk = std::io::stdin().read(&mut bytes).map(|count| {
                        bytes.truncate(count);
                        bytes
                    });
                    let done = chunk.as_ref().map_or(true, Vec::is_empty);
                    if sender.blocking_send(chunk).is_err() || done {
                        break;
                    }
                }
            });
            while let Some(chunk) = chunks.recv().await {
                let bytes = chunk?;
                if write_frame(&mut writer, &bytes).await.is_err() || bytes.is_empty() {
                    break;
                }
            }
        }
        std::future::pending::<Result<i32>>().await
    };
    let output = async {
        let mut stdout = tokio::io::stdout();
        let mut stderr = tokio::io::stderr();
        loop {
            match read_frame(&mut reader)
                .await
                .context("Lost connection to the Git daemon")?
            {
                Response::Accepted => {}
                Response::Started => {
                    started.send_replace(true);
                }
                Response::Queued(command) => {
                    let newline = if request.terminal.is_some() {
                        "\r\n"
                    } else {
                        "\n"
                    };
                    stderr
                        .write_all(format!("Git queued behind: {command}{newline}").as_bytes())
                        .await?;
                    stderr.flush().await?;
                }
                Response::Stdout(bytes) => {
                    if let Err(error) = async {
                        stdout.write_all(&bytes).await?;
                        stdout.flush().await
                    }
                    .await
                    {
                        if error.kind() == std::io::ErrorKind::BrokenPipe {
                            return Ok(141);
                        }
                        return Err(error.into());
                    }
                }
                Response::Stderr(bytes) => {
                    let bytes = if request.terminal.is_some() {
                        bytes
                            .split(|byte| *byte == b'\n')
                            .collect::<Vec<_>>()
                            .join(b"\r\n".as_slice())
                    } else {
                        bytes
                    };
                    if let Err(error) = async {
                        stderr.write_all(&bytes).await?;
                        stderr.flush().await
                    }
                    .await
                    {
                        if error.kind() == std::io::ErrorKind::BrokenPipe {
                            return Ok(141);
                        }
                        return Err(error.into());
                    }
                }
                Response::Exit(code, _) => return Ok(code),
                Response::Error(error) => bail!("{error}"),
            }
        }
    };
    tokio::select! {
        result = input => result,
        result = output => result,
    }
}

struct ProcessGroup {
    pid: u32,
    terminating: bool,
}

impl ProcessGroup {
    fn signal(&self, signal: nix::sys::signal::Signal) {
        let _ = nix::sys::signal::killpg(nix::unistd::Pid::from_raw(self.pid as i32), signal);
    }
    fn terminate(&mut self) {
        if self.terminating {
            return;
        }
        self.terminating = true;
        self.signal(nix::sys::signal::Signal::SIGTERM);
        let pid = self.pid;
        tokio::spawn(async move {
            tokio::time::sleep(Duration::from_secs(2)).await;
            let _ = nix::sys::signal::killpg(
                nix::unistd::Pid::from_raw(pid as i32),
                nix::sys::signal::Signal::SIGKILL,
            );
        });
    }
}

impl Drop for ProcessGroup {
    fn drop(&mut self) {
        self.terminate();
    }
}

fn group_command(program: impl AsRef<std::ffi::OsStr>) -> Command {
    let mut command = Command::new(program);
    command.process_group(0);
    command
}

async fn send_output(sender: &mpsc::Sender<Response>, response: Response) -> Result<()> {
    timeout(OUTPUT_TIMEOUT, sender.send(response))
        .await
        .context("Git output was not consumed for three minutes")??;
    Ok(())
}

#[cfg(test)]
async fn stream_input<R: AsyncRead + Unpin, W: AsyncWrite + Unpin + Send>(
    reader: &mut R,
    writer: &mut W,
) -> Result<()> {
    let mut bytes = vec![0; INPUT_CHUNK];
    loop {
        let count = reader.read(&mut bytes).await?;
        write_frame(writer, &bytes[..count].to_vec()).await?;
        if count == 0 {
            return Ok(());
        }
    }
}

async fn receive_input<R: AsyncRead + Unpin>(
    reader: &mut R,
    writer: &mut InputWriter,
) -> Result<()> {
    loop {
        let bytes: Vec<u8> = read_frame(reader).await?;
        writer.write(&bytes)?;
        if bytes.is_empty() {
            return Ok(());
        }
    }
}

fn validate_args(args: &[Vec<u8>]) -> Result<()> {
    for arg in args {
        if !arg.starts_with(b"-") {
            return Ok(());
        }
        if ![
            b"--no-pager".as_slice(),
            b"--paginate",
            b"-p",
            b"-P",
            b"--no-optional-locks",
            b"--no-replace-objects",
            b"--literal-pathspecs",
            b"--glob-pathspecs",
            b"--noglob-pathspecs",
            b"--icase-pathspecs",
            b"--version",
            b"--help",
            b"-h",
        ]
        .contains(&arg.as_slice())
        {
            bail!(
                "Git global option {} is not allowed when forwarding",
                String::from_utf8_lossy(arg)
            );
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::peer::sync::{Connection, PeerMessage, SyncActor};

    struct SlowConnection {
        writer: tokio::net::unix::OwnedWriteHalf,
        received: mpsc::Receiver<PeerMessage>,
        reader_task: tokio::task::JoinHandle<()>,
    }

    impl SlowConnection {
        fn new(socket: UnixStream) -> Self {
            let (mut reader, writer) = socket.into_split();
            let (sender, received) = mpsc::channel(1);
            let reader_task = tokio::spawn(async move {
                while let Ok(message) = read_frame(&mut reader).await {
                    if sender.send(message).await.is_err() {
                        break;
                    }
                }
            });
            Self {
                writer,
                received,
                reader_task,
            }
        }
    }

    impl Drop for SlowConnection {
        fn drop(&mut self) {
            self.reader_task.abort();
        }
    }

    #[async_trait::async_trait]
    impl Connection<PeerMessage> for SlowConnection {
        async fn send(&mut self, message: PeerMessage) -> Result<()> {
            let bytes = postcard::to_allocvec(&message)?;
            tokio::time::sleep(Duration::from_micros(bytes.len() as u64)).await;
            write_frame(&mut self.writer, &message).await
        }

        async fn next(&mut self) -> Result<PeerMessage> {
            self.received.recv().await.context("Test peer disconnected")
        }
    }

    #[tokio::test]
    async fn disconnect_cancels_idle_stdin_upload() -> Result<()> {
        upload_cleanup(false).await
    }

    #[tokio::test]
    async fn exit_cancels_unacknowledged_stdin_upload() -> Result<()> {
        upload_cleanup(true).await
    }

    async fn upload_cleanup(exit: bool) -> Result<()> {
        let root = tempfile::tempdir()?;
        std::fs::create_dir(root.path().join(".teamtype"))?;
        let config = crate::config::AppConfig {
            base_dir: root.path().to_path_buf(),
            peer: Some(crate::config::Peer::SecretAddress(String::new())),
            ..Default::default()
        };
        let handle = DocumentActorHandle::new(&config, true, false, false);
        let (local, mut remote) = UnixStream::pair()?;
        let actor = tokio::spawn(
            SyncActor::new(handle.clone(), Box::new(SlowConnection::new(local))).run(),
        );
        assert!(matches!(
            read_frame(&mut remote).await?,
            PeerMessage::Hello(_)
        ));
        let (input, mut writer) = Input::new()?;
        let path = input.file.path().to_path_buf();
        if exit {
            writer.write(b"unacknowledged")?;
        }
        let (response, mut responses) = mpsc::channel(8);
        handle
            .git
            .outgoing
            .send(Job {
                request: Request {
                    id: 42,
                    args: vec![b"status".to_vec()],
                    cwd: vec![],
                    heads: vec![],
                    terminal: None,
                },
                response,
                input,
            })
            .map_err(|_| anyhow::anyhow!("No sync subscriber"))?;
        let result = timeout(Duration::from_secs(3), async {
            loop {
                if matches!(read_frame(&mut remote).await?, PeerMessage::GitRequest(_)) {
                    break;
                }
            }
            write_frame(
                &mut remote,
                &PeerMessage::GitResponse(42, Response::Accepted),
            )
            .await?;
            assert!(matches!(responses.recv().await, Some(Response::Accepted)));
            if exit {
                loop {
                    if matches!(read_frame(&mut remote).await?, PeerMessage::GitInput(42, _)) {
                        break;
                    }
                }
                write_frame(
                    &mut remote,
                    &PeerMessage::GitResponse(42, Response::Exit(0, vec![])),
                )
                .await?;
                assert!(matches!(responses.recv().await, Some(Response::Exit(0, _))));
            } else {
                drop(remote);
            }
            assert!(responses.recv().await.is_none());
            while path.exists() {
                tokio::task::yield_now().await;
            }
            Ok::<(), anyhow::Error>(())
        })
        .await;
        actor.abort();
        result??;
        Ok(())
    }

    #[tokio::test]
    async fn slow_stdin_upload_keeps_document_sync_responsive() -> Result<()> {
        let host_root = tempfile::tempdir()?;
        let join_root = tempfile::tempdir()?;
        for root in [host_root.path(), join_root.path()] {
            std::fs::create_dir(root.join(".teamtype"))?;
        }
        git2::Repository::init(host_root.path())?;
        std::fs::write(host_root.path().join("file"), "initial")?;
        let host_config = crate::config::AppConfig {
            base_dir: host_root.path().to_path_buf(),
            ..Default::default()
        };
        let join_config = crate::config::AppConfig {
            base_dir: join_root.path().to_path_buf(),
            peer: Some(crate::config::Peer::SecretAddress(String::new())),
            ..Default::default()
        };
        let host = DocumentActorHandle::new(&host_config, true, true, false);
        let join = DocumentActorHandle::new(&join_config, true, false, false);
        start(host.clone())?;
        let (a, b) = UnixStream::pair()?;
        let host_sync =
            tokio::spawn(SyncActor::new(host.clone(), Box::new(SlowConnection::new(a))).run());
        let join_sync =
            tokio::spawn(SyncActor::new(join.clone(), Box::new(SlowConnection::new(b))).run());
        timeout(Duration::from_secs(3), async {
            while std::fs::read(join_root.path().join("file")).ok().as_deref() != Some(b"initial") {
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
        })
        .await?;
        let (mut socket, server) = UnixStream::pair()?;
        let serving = tokio::spawn(serve(server, join));
        write_frame(
            &mut socket,
            &Request {
                id: 0,
                args: vec![b"hash-object".to_vec(), b"--stdin".to_vec()],
                cwd: vec![],
                heads: vec![],
                terminal: None,
            },
        )
        .await?;
        let input = vec![42; 8 * 1024 * 1024];
        stream_input(&mut input.as_slice(), &mut socket).await?;
        tokio::time::sleep(Duration::from_millis(100)).await;
        std::fs::write(host_root.path().join("file"), "during upload")?;
        host.git_heads().await;
        timeout(Duration::from_secs(2), async {
            while std::fs::read(join_root.path().join("file")).ok().as_deref()
                != Some(b"during upload")
            {
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
        })
        .await
        .context("Stdin upload blocked document synchronization")?;
        assert!(matches!(read_frame(&mut socket).await?, Response::Accepted));
        let started = tokio::time::Instant::now();
        let mut output = Vec::new();
        timeout(Duration::from_secs(20), async {
            loop {
                match read_frame(&mut socket).await? {
                    Response::Stdout(bytes) => output.extend(bytes),
                    Response::Exit(code, _) => {
                        assert_eq!(code, 0);
                        break;
                    }
                    Response::Error(error) => bail!("{error}"),
                    _ => {}
                }
            }
            Ok::<(), anyhow::Error>(())
        })
        .await??;
        assert!(started.elapsed() > Duration::from_secs(6));
        assert_eq!(
            String::from_utf8(output)?.trim(),
            git2::Oid::hash_object(git2::ObjectType::Blob, &input)?.to_string()
        );
        serving.await??;
        host_sync.abort();
        join_sync.abort();
        Ok(())
    }

    #[tokio::test]
    async fn stdin_waits_for_delayed_bytes_and_eof() -> Result<()> {
        let (mut producer, mut reader) = tokio::io::duplex(INPUT_CHUNK);
        let producing = tokio::spawn(async move {
            producer.write_all(b"before").await?;
            tokio::time::sleep(Duration::from_millis(250)).await;
            producer.write_all(b"after").await
        });
        let (mut writer, mut receiver) = tokio::io::duplex(INPUT_CHUNK);
        let sending = tokio::spawn(async move { stream_input(&mut reader, &mut writer).await });
        let (input, mut spool) = Input::new()?;
        receive_input(&mut receiver, &mut spool).await?;
        assert_eq!(std::fs::read(input.file.path())?, b"beforeafter");
        producing.await??;
        sending.await??;
        Ok(())
    }

    #[tokio::test]
    async fn cancellation_escalates_only_after_grace() -> Result<()> {
        let mut child = group_command("sh")
            .args(["-c", "trap '' TERM; echo ready; sleep 30"])
            .stdout(Stdio::piped())
            .spawn()?;
        let mut stdout = child.stdout.take().context("Missing test stdout")?;
        let mut ready = [0; 6];
        stdout.read_exact(&mut ready).await?;
        assert_eq!(&ready, b"ready\n");
        let group = ProcessGroup {
            pid: child.id().context("Missing test PID")?,
            terminating: false,
        };
        let started = tokio::time::Instant::now();
        drop(group);
        let status = timeout(Duration::from_secs(4), child.wait()).await??;
        assert_eq!(status.signal(), Some(9));
        assert!(started.elapsed() >= Duration::from_secs(2));
        Ok(())
    }

    #[tokio::test]
    async fn exit_barrier_delay_warns_and_preserves_git_exit_code() -> Result<()> {
        let root = tempfile::tempdir()?;
        std::fs::create_dir(root.path().join(".teamtype"))?;
        let config = crate::config::AppConfig {
            base_dir: root.path().to_path_buf(),
            peer: Some(crate::config::Peer::SecretAddress(String::new())),
            ..Default::default()
        };
        let handle = DocumentActorHandle::new(&config, true, false, false);
        let mut requests = handle.git.outgoing.subscribe();
        let (mut client, server) = UnixStream::pair()?;
        let serving = tokio::spawn(serve(server, handle));
        write_frame(
            &mut client,
            &Request {
                id: 0,
                args: vec![b"status".to_vec()],
                cwd: vec![],
                heads: vec![],
                terminal: None,
            },
        )
        .await?;
        write_frame(&mut client, &Vec::<u8>::new()).await?;
        let job = requests.recv().await?;
        job.response.send(Response::Accepted).await?;
        job.response
            .send(Response::Exit(0, vec![ChangeHash([7; 32])]))
            .await?;
        assert!(matches!(read_frame(&mut client).await?, Response::Accepted));
        let response: Response =
            timeout(Duration::from_secs(12), read_frame(&mut client)).await??;
        assert!(
            matches!(response, Response::Stderr(bytes) if String::from_utf8_lossy(&bytes).contains("file changes did not arrive"))
        );
        assert!(matches!(
            read_frame(&mut client).await?,
            Response::Exit(0, _)
        ));
        serving.await??;
        Ok(())
    }

    #[test]
    fn upgraded_binary_path_and_help() {
        assert_eq!(
            wrapper_executable(Path::new("/bin/teamtype (deleted)")),
            PathBuf::from("/bin/teamtype")
        );
        assert!(validate_args(&[b"-h".to_vec()]).is_ok());
    }

    #[test]
    fn removes_hook_created_after_startup() -> Result<()> {
        let root = tempfile::tempdir()?;
        let repo = git2::Repository::init(root.path())?;
        remove_old_hook(root.path());
        let hook = repo.path().join("hooks/reference-transaction");
        std::fs::write(&hook, "# Installed by teamtype\nexit 1\n")?;
        remove_old_hook(root.path());
        assert!(!hook.exists());
        std::fs::create_dir(root.path().join("custom-hooks"))?;
        repo.config()?.set_str("core.hooksPath", "custom-hooks")?;
        let custom = root.path().join("custom-hooks/reference-transaction");
        std::fs::write(&custom, "# Installed by teamtype\n")?;
        remove_old_hook(root.path());
        assert!(!custom.exists());
        Ok(())
    }

    #[test]
    fn rejects_global_execution_and_location_options() {
        for option in [
            "-C",
            "-C/",
            "-c",
            "-ccore.fsmonitor=evil",
            "--git-dir=/",
            "--work-tree=/",
            "--exec-path=/",
            "--namespace=x",
            "--config-env=x=y",
            "--super-prefix=x",
            "--bare",
        ] {
            assert!(
                validate_args(&[option.as_bytes().to_vec(), b"status".to_vec()]).is_err(),
                "{option}"
            );
        }
        assert!(validate_args(&[b"--no-pager".to_vec(), b"log".to_vec(), b"-c".to_vec()]).is_ok());
    }

    #[tokio::test]
    async fn socket_is_private_and_cannot_be_stolen() -> Result<()> {
        let root = tempfile::tempdir()?;
        std::fs::create_dir(root.path().join(".teamtype"))?;
        let (listener, lock) = bind_socket(root.path())?;
        let socket = root.path().join(".teamtype/git.sock");
        assert_eq!(
            std::fs::metadata(&socket)?.permissions().mode() & 0o777,
            0o600
        );
        assert!(bind_socket(root.path()).is_err());
        let _client = UnixStream::connect(&socket).await?;
        let _accepted = listener.accept().await?;
        drop(listener);
        drop(lock);
        let _replacement = bind_socket(root.path())?;
        Ok(())
    }

    #[cfg(target_os = "linux")]
    #[tokio::test]
    async fn socket_is_published_by_rename_after_permissions_are_set() -> Result<()> {
        use notify::Watcher;

        let root = tempfile::tempdir()?;
        let dir = root.path().join(".teamtype");
        std::fs::create_dir(&dir)?;
        let (events, received) = std::sync::mpsc::channel();
        let mut watcher = notify::recommended_watcher(move |event| {
            let _ = events.send(event);
        })?;
        watcher.watch(&dir, notify::RecursiveMode::NonRecursive)?;
        let _listener = bind_socket(root.path())?;
        let socket = dir.join("git.sock");
        loop {
            let event = received.recv_timeout(Duration::from_secs(2))??;
            if event.paths.contains(&socket) {
                assert!(
                    matches!(
                        event.kind,
                        notify::EventKind::Modify(notify::event::ModifyKind::Name(_))
                    ),
                    "Socket became visible before publication: {event:?}"
                );
                assert_eq!(
                    std::fs::metadata(socket)?.permissions().mode() & 0o777,
                    0o600
                );
                break;
            }
        }
        Ok(())
    }
}
