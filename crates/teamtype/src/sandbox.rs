// SPDX-FileCopyrightText: 2024 blinry <mail@blinry.org>
// SPDX-FileCopyrightText: 2024 zormit <nt4u@kpvn.de>
// SPDX-FileCopyrightText: 2026 axelmartensson <axel.martensson@hotmail.com>
// SPDX-FileCopyrightText: 2026 Caleb Maclennan <caleb@alerque.com>
//
// SPDX-License-Identifier: AGPL-3.0-or-later

//! 👮🚨🚓
//! The functions in this module are supposed to prevent file I/O outside the base directory.
//! All our file I/O should go through them.

use std::fs::{self, File};
use std::io::{Read, Write};
use std::os::fd::OwnedFd;
use std::os::unix::fs::PermissionsExt;
use std::path::{Component, Path, PathBuf};

use anyhow::bail;
use anyhow::{Context, Result};
use ignore::WalkBuilder;
use path_clean::PathClean;
use rustix::fs::{AtFlags, CWD, Mode, OFlags};

use crate::config::AppConfig;

pub fn read_file(absolute_base_dir: &Path, absolute_file_path: &Path) -> Result<Vec<u8>> {
    let mut file = open_beneath(absolute_base_dir, absolute_file_path, OFlags::RDONLY)?;
    let mut bytes = Vec::new();
    file.read_to_end(&mut bytes)?;
    Ok(bytes)
}

/// Writes content to a file, creating the parent directories, if they don't exist.
pub fn write_file(
    absolute_base_dir: &Path,
    absolute_file_path: &Path,
    content: &[u8],
) -> Result<()> {
    let canonical_file_path =
        check_inside_base_dir_and_canonicalize(absolute_base_dir, absolute_file_path)?;

    // Create the parent directory(s), if necessary.
    let parent_dir = canonical_file_path
        .parent()
        .expect("Failed to get parent directory");
    create_dir_all(absolute_base_dir, parent_dir)?;

    // `absolute_and_canonicalized` treats a dangling symlink as a missing file, so the final
    // component must not be followed: it could point outside the base directory.
    let mut file = open_beneath(
        absolute_base_dir,
        &canonical_file_path,
        OFlags::WRONLY | OFlags::CREATE | OFlags::TRUNC,
    )?;
    file.write_all(content)?;
    Ok(())
}

/// Atomically replaces a file and returns the bytes it replaced.
/// Keeping the displaced file prevents a concurrent Git checkout from disappearing between
/// the daemon's last read and its write. Existing permissions are preserved.
pub fn replace_file(
    absolute_base_dir: &Path,
    absolute_file_path: &Path,
    content: &[u8],
) -> Result<Option<Vec<u8>>> {
    replace_file_keeping(absolute_base_dir, absolute_file_path, content, None, None)
        .map(|(displaced, _)| displaced)
}

/// Like `replace_file`. With a `keep_prefix`, the displaced file also stays in `.teamtypev` under
/// a name starting with it, and its path is returned: a kill before the caller has saved the
/// displaced bytes elsewhere then cannot lose them. `base` (the content the caller last read) is
/// stored next to it as `<name>.base` before the swap. The caller removes both afterwards
/// (`remove_displaced`).
pub fn replace_file_keeping(
    absolute_base_dir: &Path,
    absolute_file_path: &Path,
    content: &[u8],
    keep_prefix: Option<&str>,
    base: Option<&[u8]>,
) -> Result<(Option<Vec<u8>>, Option<PathBuf>)> {
    let path = check_inside_base_dir_and_canonicalize(absolute_base_dir, absolute_file_path)?;
    let parent = path.parent().context("File has no parent")?;
    create_dir_all(absolute_base_dir, parent)?;
    let metadata_dir = absolute_base_dir.join(".teamtypev");
    create_dir_all(absolute_base_dir, &metadata_dir)?;
    let mut staged = tempfile::Builder::new()
        .prefix(keep_prefix.unwrap_or(".tmp"))
        .tempfile_in(&metadata_dir)?;
    staged.write_all(content)?;
    let sidecar = match (keep_prefix, base) {
        (Some(_), Some(base)) => {
            let mut name = staged.path().as_os_str().to_owned();
            name.push(".base");
            let sidecar = PathBuf::from(name);
            fs::write(&sidecar, base)?;
            Some(sidecar)
        }
        _ => None,
    };
    let (dir, name) = open_parent_beneath(absolute_base_dir, &path)?;
    if let Ok(stat) = rustix::fs::statat(&dir, &name, AtFlags::SYMLINK_NOFOLLOW) {
        // `st_mode` is `u16` on macOS and `u32` elsewhere.
        #[cfg(target_vendor = "apple")]
        let mode = u32::from(stat.st_mode);
        #[cfg(not(target_vendor = "apple"))]
        let mode = stat.st_mode;
        staged
            .as_file()
            .set_permissions(fs::Permissions::from_mode(mode & 0o7777))?;
    }
    #[cfg(any(
        target_os = "linux",
        target_os = "android",
        target_vendor = "apple",
        target_os = "redox"
    ))]
    let result = loop {
        match rustix::fs::renameat_with(
            CWD,
            staged.path(),
            &dir,
            &name,
            rustix::fs::RenameFlags::EXCHANGE,
        ) {
            Ok(()) => {
                let displaced = fs::read(staged.path());
                let kept = match keep_prefix {
                    Some(_) => Some(staged.into_temp_path().keep()?),
                    None => None,
                };
                break displaced
                    .map(|displaced| (Some(displaced), kept))
                    .map_err(Into::into);
            }
            Err(rustix::io::Errno::NOENT) => match rustix::fs::renameat_with(
                CWD,
                staged.path(),
                &dir,
                &name,
                rustix::fs::RenameFlags::NOREPLACE,
            ) {
                Ok(()) => {
                    // The staged name is gone; do not let `staged` delete what now sits there.
                    let _ = staged.into_temp_path().keep();
                    break Ok((None, None));
                }
                Err(rustix::io::Errno::EXIST) => {}
                Err(error) => break Err(error.into()),
            },
            Err(error) => break Err(error.into()),
        }
    };
    #[cfg(not(any(
        target_os = "linux",
        target_os = "android",
        target_vendor = "apple",
        target_os = "redox"
    )))]
    let result: Result<(Option<Vec<u8>>, Option<PathBuf>)> = Err(anyhow::anyhow!(
        "Atomic file exchange is unsupported on this platform"
    ));
    if !matches!(result, Ok((_, Some(_))))
        && let Some(sidecar) = sidecar
    {
        let _ = fs::remove_file(sidecar);
    }
    result
}

/// Removes a displaced file kept by `replace_file_keeping` and its stored base.
pub fn remove_displaced(kept: &Path) {
    let _ = fs::remove_file(kept);
    let mut name = kept.as_os_str().to_owned();
    name.push(".base");
    let _ = fs::remove_file(PathBuf::from(name));
}

pub fn append_file(
    absolute_base_dir: &Path,
    absolute_file_path: &Path,
    content: &[u8],
) -> Result<()> {
    let mut file = open_beneath(
        absolute_base_dir,
        absolute_file_path,
        OFlags::WRONLY | OFlags::APPEND,
    )?;
    file.write_all(content)?;
    Ok(())
}

pub fn rename_file(
    absolute_base_dir: &Path,
    absolute_file_path_old: &Path,
    absolute_file_path_new: &Path,
) -> Result<()> {
    let (old_dir, old_name) = open_parent_beneath(absolute_base_dir, absolute_file_path_old)?;
    let (new_dir, new_name) = open_parent_beneath(absolute_base_dir, absolute_file_path_new)?;
    rustix::fs::renameat(&old_dir, &old_name, &new_dir, &new_name)?;
    Ok(())
}

pub fn remove_file(absolute_base_dir: &Path, absolute_file_path: &Path) -> Result<()> {
    let (dir, name) = open_parent_beneath(absolute_base_dir, absolute_file_path)?;
    rustix::fs::unlinkat(&dir, &name, AtFlags::empty())?;
    Ok(())
}

/// Removes a file and returns the bytes that were removed. The file is first renamed into
/// `.teamtypev`, so bytes an outside process writes to that name later make a new file, and the
/// bytes returned are exactly those that were removed (unlike read-then-unlink, which loses a
/// write landing between the two).
pub fn remove_file_returning(
    absolute_base_dir: &Path,
    absolute_file_path: &Path,
) -> Result<Vec<u8>> {
    let path = check_inside_base_dir_and_canonicalize(absolute_base_dir, absolute_file_path)?;
    let metadata_dir = absolute_base_dir.join(".teamtypev");
    create_dir_all(absolute_base_dir, &metadata_dir)?;
    let (dir, name) = open_parent_beneath(absolute_base_dir, &path)?;
    let taken = tempfile::Builder::new()
        .prefix(".removed")
        .tempfile_in(&metadata_dir)?
        .into_temp_path();
    // Replaces the reserved empty temporary file.
    rustix::fs::renameat(&dir, &name, CWD, &*taken)?;
    let bytes = fs::read(&*taken);
    match bytes {
        Ok(bytes) => {
            fs::remove_file(&*taken)?;
            // Already moved; the path guard has nothing left to delete.
            let _ = taken.keep();
            Ok(bytes)
        }
        Err(error) => {
            // Not a regular file we can read: put it back.
            let _ = rustix::fs::renameat(CWD, &*taken, &dir, &name);
            let _ = taken.keep();
            Err(error.into())
        }
    }
}

pub fn create_dir(absolute_base_dir: &Path, absolute_dir_path: &Path) -> Result<()> {
    let canonical_dir_path =
        check_inside_base_dir_and_canonicalize(absolute_base_dir, absolute_dir_path)?;
    let has_dir = canonical_dir_path.exists() && canonical_dir_path.is_dir();
    if !has_dir {
        fs::create_dir(&canonical_dir_path)?;
        let permissions = fs::Permissions::from_mode(0o700);
        fs::set_permissions(canonical_dir_path, permissions)?;
    }
    Ok(())
}

pub fn create_dir_all(absolute_base_dir: &Path, absolute_dir_path: &Path) -> Result<()> {
    let (mut dir, relative) = open_base_and_relative(absolute_base_dir, absolute_dir_path)?;
    for component in relative.components() {
        match rustix::fs::mkdirat(&dir, component.as_os_str(), Mode::from_raw_mode(0o777)) {
            Ok(()) | Err(rustix::io::Errno::EXIST) => {}
            Err(error) => return Err(error.into()),
        }
        dir = open_dir_nofollow(&dir, component.as_os_str())?;
    }
    Ok(())
}

pub fn exists(absolute_base_dir: &Path, absolute_file_path: &Path) -> Result<bool> {
    let canonical_file_path =
        check_inside_base_dir_and_canonicalize(absolute_base_dir, absolute_file_path)?;
    Ok(canonical_file_path.exists())
}

pub fn enumerate_non_ignored_files(app_config: &AppConfig) -> Vec<PathBuf> {
    let walk = WalkBuilder::new(&app_config.base_dir)
        .add_custom_ignore_filename(".teamtypevignore")
        .standard_filters(true)
        .hidden(false)
        .require_git(false)
        // Interestingly, the standard filters don't seem to ignore .git.
        .filter_entry(move |dir_entry| {
            let name = dir_entry
                .path()
                .file_name()
                .expect("Failed to get file name from path.")
                .to_str()
                .expect("Failed to convert OsStr to str");
            !crate::git_forward::EXCLUDED_NAMES.contains(&name) && !name.ends_with('~')
        })
        .build();

    let mut files: Vec<PathBuf> = walk
        .filter_map(Result::ok)
        .filter(|dir_entry| {
            !dir_entry
                .file_type()
                .expect("Couldn't get file type of dir entry")
                .is_dir()
        })
        .map(|dir_entry| dir_entry.path().to_path_buf())
        .collect();

    // 🧑 "fix the ignore issue": a file that Git tracks must reach the peers, or their Git
    // sees it as deleted.
    let known: std::collections::HashSet<PathBuf> = files.iter().cloned().collect();
    let config_dir = app_config.base_dir.join(".teamtypev");
    files.extend(
        (if app_config.is_host() {
            crate::config::git_tracked_files(&app_config.base_dir)
        } else {
            vec![]
        })
        .into_iter()
        .filter(|path| {
            !known.contains(path)
                && !path.starts_with(&config_dir)
                && !crate::git_forward::excluded(
                    path.strip_prefix(&app_config.base_dir).unwrap_or(path),
                )
        }),
    );

    files
}

// TODO: Don't build the list of ignored files on every call.
// TODO: Allow calling this for non-existing files.
pub fn ignored(app_config: &AppConfig, absolute_file_path: &Path) -> Result<bool> {
    let canonical_file_path =
        check_inside_base_dir_and_canonicalize(&app_config.base_dir, absolute_file_path)?;

    Ok(!enumerate_non_ignored_files(app_config)
        .into_iter()
        .map(|path_buf| absolute_and_canonicalized(&path_buf))
        .collect::<Result<Vec<_>>>()?
        .contains(&canonical_file_path))
}

/// Opens the canonical base directory and returns the checked path relative to it.
fn open_base_and_relative(base_dir: &Path, path: &Path) -> Result<(OwnedFd, PathBuf)> {
    let canonical_path = check_inside_base_dir_and_canonicalize(base_dir, path)?;
    let canonical_base_dir = absolute_and_canonicalized(base_dir)?;
    let relative = canonical_path
        .strip_prefix(&canonical_base_dir)?
        .to_path_buf();
    let dir = rustix::fs::openat(
        CWD,
        &canonical_base_dir,
        OFlags::DIRECTORY | OFlags::RDONLY | OFlags::CLOEXEC,
        Mode::empty(),
    )?;
    Ok((dir, relative))
}

fn open_dir_nofollow(dir: &OwnedFd, name: &std::ffi::OsStr) -> Result<OwnedFd> {
    Ok(rustix::fs::openat(
        dir,
        name,
        OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::RDONLY | OFlags::CLOEXEC,
        Mode::empty(),
    )?)
}

/// Opens the parent directory of a checked path one component at a time without following
/// symlinks, so a concurrent swap of a directory for a symlink between the check and the
/// syscall cannot redirect the operation outside the base directory. Returns the final name.
fn open_parent_beneath(base_dir: &Path, path: &Path) -> Result<(OwnedFd, PathBuf)> {
    let (mut dir, relative) = open_base_and_relative(base_dir, path)?;
    let name = relative
        .file_name()
        .context("Path has no file name inside the base directory")?
        .into();
    if let Some(parent) = relative.parent() {
        for component in parent.components() {
            dir = open_dir_nofollow(&dir, component.as_os_str())?;
        }
    }
    Ok((dir, name))
}

/// Opens a checked path beneath the base directory; no component, including the last, is a
/// followed symlink.
fn open_beneath(base_dir: &Path, path: &Path, flags: OFlags) -> Result<File> {
    let (dir, name) = open_parent_beneath(base_dir, path)?;
    let fd = rustix::fs::openat(
        &dir,
        &name,
        flags | OFlags::NOFOLLOW | OFlags::CLOEXEC,
        Mode::from_raw_mode(0o666),
    )?;
    Ok(File::from(fd))
}

fn check_inside_base_dir_and_canonicalize(base_dir: &Path, path: &Path) -> Result<PathBuf> {
    let canonical_base_dir = absolute_and_canonicalized(base_dir)?;
    let canonical_path = absolute_and_canonicalized(path)?;

    if !canonical_path.starts_with(&canonical_base_dir) {
        let canonical_path_str = &canonical_path.display();
        let canonical_base_dir_str = &canonical_base_dir.display();
        bail!(
            "File path {canonical_path_str} is not inside the base directory {canonical_base_dir_str}"
        );
    }

    Ok(canonical_path)
}

pub(crate) fn absolute_and_canonicalized(path: &Path) -> Result<PathBuf> {
    if !path.is_absolute() {
        bail!("Path is not absolute.");
    }

    // Remove any ".." and "." from the path.
    let canonical_path = path.clean();
    let mut suffix_path = PathBuf::new();
    let mut prefix_path = canonical_path;

    for component in path.components().rev() {
        if prefix_path.exists() {
            break;
        }
        prefix_path.pop();
        if let Component::Normal(os_str) = component {
            suffix_path = if suffix_path.components().count() != 0 {
                Path::new(os_str).join(&suffix_path)
            } else {
                Path::new(os_str).to_path_buf()
            };
        } else {
            bail!("Got unexpected Component variant while canonicalizing");
        }
    }

    let mut canonical_path = prefix_path
        .canonicalize()
        .context("Failed to canonicalize path, probably the file disappeared already")?;

    if suffix_path.components().count() != 0 {
        canonical_path = canonical_path.join(suffix_path);
    }

    Ok(canonical_path)
}

#[cfg(test)]
mod tests {
    /// Produces an ordinary replacement failure without permissions or mount setup.
    #[test]
    fn replacement_failure_preserves_original_bytes() -> Result<()> {
        let dir = tempdir()?;
        fs::write(dir.path().join(".teamtypev"), b"occupied")?;
        let path = dir.path().join("file.txt");
        fs::write(&path, b"original")?;
        assert!(replace_file(dir.path(), &path, b"shared").is_err());
        assert_eq!(fs::read(path)?, b"original");
        Ok(())
    }

    #[test]
    fn joiner_does_not_enumerate_stale_tracked_ignored_files() -> Result<()> {
        let root = tempdir()?;
        let repo = git2::Repository::init(root.path())?;
        fs::write(root.path().join(".gitignore"), "stale\n")?;
        fs::write(root.path().join("stale"), "old index entry")?;
        let mut index = repo.index()?;
        index.add_path(Path::new("stale"))?;
        index.write()?;
        let mut config = AppConfig {
            base_dir: root.path().to_path_buf(),
            ..Default::default()
        };
        assert!(enumerate_non_ignored_files(&config).contains(&root.path().join("stale")));
        config.peer = Some(crate::config::Peer::SecretAddress(String::new()));
        assert!(!enumerate_non_ignored_files(&config).contains(&root.path().join("stale")));
        Ok(())
    }
    use std::os::unix::fs::symlink;

    use tempfile::{TempDir, tempdir};

    use super::*;

    fn temp_dir_setup() -> TempDir {
        let dir = tempdir().expect("Failed to create temp directory");
        let project_dir = dir.path().join("project");
        fs::create_dir(&project_dir).expect("Failed to create directory");
        fs::write(project_dir.join("a"), b"This is a file").expect("Failed to write file");
        fs::create_dir(project_dir.join("dir")).expect("Failed to create directory");
        fs::write(project_dir.join("dir").join("b"), b"This is b file")
            .expect("Failed to write file");
        fs::write(
            dir.path().join("file-outside-of-project"),
            b"This is a file outside of project",
        )
        .expect("Failed to write file");

        dir
    }

    #[test]
    fn does_canonicalize_symlink_dir() {
        let dir = temp_dir_setup();
        let linked_project = dir.path().join("ln_project");
        let project = dir.path().join("project");
        symlink(&project, &linked_project).unwrap();
        assert_eq!(
            absolute_and_canonicalized(&linked_project).unwrap(),
            project.canonicalize().unwrap()
        );
    }

    #[test]
    fn does_canonicalize_symlink_file() {
        let dir = temp_dir_setup();
        let linked_project = dir.path().join("ln_project");
        let project = dir.path().join("project");
        symlink(&project, &linked_project).unwrap();

        let ln_file = linked_project.join("c");

        assert_eq!(
            absolute_and_canonicalized(&ln_file).unwrap().to_str(),
            project.canonicalize().unwrap().join("c").to_str()
        );
    }

    #[test]
    fn does_canonicalize_symlink_notexisting_file() {
        let dir = temp_dir_setup();
        let linked_project = dir.path().join("ln_project");
        let project = dir.path().join("project");
        symlink(&project, &linked_project).unwrap();

        let file = project.join("a");
        let ln_file = linked_project.join("a");

        // tests whether it does not end on slash
        assert_eq!(
            absolute_and_canonicalized(&file).unwrap().to_str(),
            file.canonicalize().unwrap().to_str()
        );

        assert_eq!(
            absolute_and_canonicalized(&ln_file).unwrap().to_str(),
            ln_file.canonicalize().unwrap().to_str()
        );
    }

    #[test]
    fn can_read_in_dir() {
        let dir = temp_dir_setup();
        let project_dir = dir.path().join("project");

        assert!(read_file(&project_dir, &project_dir.join("a")).is_ok());
        assert!(read_file(&project_dir, &project_dir.join("dir").join("b")).is_ok());
        assert!(read_file(&project_dir, &project_dir.join("dir").join("..").join("a")).is_ok());
        assert!(
            read_file(
                &project_dir,
                &project_dir.join(".").join("dir").join(".").join("b")
            )
            .is_ok()
        );
    }

    #[test]
    fn can_not_read_outside_dir() {
        let dir = temp_dir_setup();
        let project_dir = dir.path().join("project");

        // Not a file.
        assert!(read_file(&project_dir, &project_dir).is_err());

        // Not a file *and* now within base dir.
        assert!(read_file(&project_dir, &project_dir.join("..")).is_err());

        // Definitely not within base dir.
        assert!(read_file(&project_dir, Path::new("/etc/passwd")).is_err());

        // File path is not absolute.
        assert!(read_file(&project_dir, Path::new("project/a")).is_err());

        // Base dir is not absolute.
        assert!(read_file(Path::new("project"), &project_dir.join("a")).is_err());

        // File not exist.
        assert!(read_file(&project_dir, &project_dir.join("nonexistent")).is_err());
    }

    #[test]
    fn obeys_teamtypevignore() {
        let dir = temp_dir_setup();
        let project_dir = dir.path().join("project");
        let teamtypevignore = project_dir.join(".teamtypevignore");

        fs::write(&teamtypevignore, b"a\n").expect("Failed to write .teamtypevignore");

        let app_config = AppConfig {
            base_dir: project_dir.clone(),
            ..Default::default()
        };

        assert!(
            ignored(&app_config, &project_dir.join("a")).unwrap(),
            "a should be ignored"
        );
        assert!(
            !ignored(&app_config, &project_dir.join("dir/b")).unwrap(),
            "b should be not ignored"
        );

        fs::write(&teamtypevignore, b"a\ndir\n").expect("Failed to write .teamtypevignore");

        assert!(
            ignored(&app_config, &project_dir.join("dir/b")).unwrap(),
            "now b should be ignored"
        );
    }

    #[test]
    fn fail_check_inside_base_dir() {
        let dir = temp_dir_setup();
        let project_dir = dir.path().join("project");

        // Not within the base dir.
        assert!(
            read_file(
                &project_dir,
                &project_dir.join("..").join("file-outside-of-project")
            )
            .is_err()
        );

        // It "starts" with the base dir, but it's not inside it.
        assert!(
            check_inside_base_dir_and_canonicalize(
                &project_dir,
                Path::new(&format!(
                    "{}{}",
                    project_dir.as_path().to_str().unwrap(),
                    "2/file"
                ))
            )
            .is_err()
        );
    }
}

#[cfg(test)]
mod dangling_symlink_tests {
    use super::*;
    #[test]
    fn write_does_not_follow_dangling_symlink() {
        let dir = tempfile::tempdir().unwrap();
        let base = dir.path().join("project");
        fs::create_dir(&base).unwrap();
        let outside = dir.path().join("outside-new");
        std::os::unix::fs::symlink(&outside, base.join("link")).unwrap();
        let r = write_file(&base, &base.join("link"), b"pwned");
        assert!(r.is_err(), "write succeeded");
        assert!(!outside.exists(), "escaped: wrote outside");
    }
    #[test]
    fn dangling_dir_symlink_create_escapes() {
        let dir = tempfile::tempdir().unwrap();
        let base = dir.path().join("project");
        fs::create_dir(&base).unwrap();
        let outside = dir.path().join("outdir");
        std::os::unix::fs::symlink(&outside, base.join("d")).unwrap();
        let _ = write_file(&base, &base.join("d/f"), b"pwned");
        assert!(!outside.exists(), "escaped: created dir outside");
    }
}

#[cfg(all(test, target_os = "linux"))]
mod toctou_tests {
    use super::*;
    use std::sync::Arc;
    use std::sync::atomic::{AtomicBool, Ordering};

    /// A concurrent local actor swaps a checked directory for a symlink to outside the base
    /// directory between the sandbox check and the syscall.
    #[test]
    fn read_does_not_escape_when_dir_is_swapped_for_symlink() {
        let dir = tempfile::tempdir().unwrap();
        let base = dir.path().join("project");
        let outside = dir.path().join("outside");
        fs::create_dir_all(base.join("d")).unwrap();
        fs::create_dir(&outside).unwrap();
        fs::write(base.join("d/x"), b"inside").unwrap();
        fs::write(outside.join("x"), b"SECRET").unwrap();
        std::os::unix::fs::symlink(&outside, base.join("s")).unwrap();
        let stop = Arc::new(AtomicBool::new(false));
        let adversary = {
            let (stop, a, b) = (stop.clone(), base.join("d"), base.join("s"));
            std::thread::spawn(move || {
                while !stop.load(Ordering::Relaxed) {
                    rustix::fs::renameat_with(CWD, &a, CWD, &b, rustix::fs::RenameFlags::EXCHANGE)
                        .unwrap();
                }
            })
        };
        let mut escaped = false;
        for _ in 0..20_000 {
            if let Ok(bytes) = read_file(&base, &base.join("d/x"))
                && bytes == b"SECRET"
            {
                escaped = true;
                break;
            }
        }
        stop.store(true, Ordering::Relaxed);
        adversary.join().unwrap();
        assert!(!escaped, "escaped: read a file outside the base directory");
    }
}

#[cfg(test)]
mod walk_contract_tests {
    use super::*;

    /// The trusted contract of the `ignore` walk used by the proof: it yields only paths below
    /// the base directory, built from directory entry names, and never descends into a symlink.
    #[test]
    fn walk_does_not_follow_symlinks() {
        let dir = tempfile::tempdir().unwrap();
        let base = dir.path().join("project");
        let outside = dir.path().join("outside");
        fs::create_dir_all(base.join("d")).unwrap();
        fs::create_dir(&outside).unwrap();
        fs::write(base.join("d/x"), b"x").unwrap();
        fs::write(outside.join("secret"), b"s").unwrap();
        std::os::unix::fs::symlink(&outside, base.join("dirlink")).unwrap();
        std::os::unix::fs::symlink(outside.join("secret"), base.join("filelink")).unwrap();
        let config = AppConfig {
            base_dir: base.clone(),
            ..Default::default()
        };
        let files = enumerate_non_ignored_files(&config);
        for file in &files {
            let relative = file.strip_prefix(&base).unwrap();
            assert!(
                relative
                    .components()
                    .all(|c| matches!(c, Component::Normal(_)))
            );
            assert!(
                *file == base.join("dirlink") || !file.starts_with(base.join("dirlink")),
                "descended: {file:?}"
            );
        }
        assert!(files.contains(&base.join("d/x")));
        // The symlink itself is yielded; reading it must still fail the sandbox check.
        assert!(files.contains(&base.join("filelink")));
        assert!(read_file(&base, &base.join("filelink")).is_err());
    }
}
