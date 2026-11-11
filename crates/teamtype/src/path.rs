// SPDX-FileCopyrightText: 2024 blinry <mail@blinry.org>
// SPDX-FileCopyrightText: 2024 zormit <nt4u@kpvn.de>
// SPDX-FileCopyrightText: 2026 Caleb Maclennan <caleb@alerque.com>
//
// SPDX-License-Identifier: AGPL-3.0-or-later

use std::path::{self, Path, PathBuf};

use anyhow::Context;
use anyhow::bail;
use automerge::Prop;
use derive_more::{AsRef, Deref, Display};
use serde::{Deserialize, Serialize};
use url::Url;

use crate::sandbox;

/// Paths like these are guaranteed to be absolute.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, Eq, Hash, Deref, AsRef, Display)]
#[as_ref(Path)]
#[display("'{}'", self.0.display())]
#[must_use]
pub struct AbsolutePath(PathBuf);

impl AbsolutePath {
    pub fn from_parts(base: &Path, relative_path: &RelativePath) -> Result<Self, anyhow::Error> {
        let path = base.join(relative_path);
        Self::try_from(path)
    }

    pub fn to_file_uri(&self) -> FileUri {
        Url::from_file_path(&self.0)
            .map(|url| FileUri(url.to_string()))
            .expect("Should be able to create File URI from absolute path")
    }
}

impl TryFrom<PathBuf> for AbsolutePath {
    type Error = anyhow::Error;

    fn try_from(path: PathBuf) -> Result<Self, Self::Error> {
        if !path.is_absolute() {
            bail!("Path '{}' is not absolute", path.display());
        }

        Ok(Self(path))
    }
}

impl TryFrom<&str> for AbsolutePath {
    type Error = anyhow::Error;

    fn try_from(path: &str) -> Result<Self, Self::Error> {
        Path::new(&path).to_path_buf().try_into()
    }
}

/// Paths like these are relative to the shared directory.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, Eq, Hash, Deref, AsRef, Display)]
#[as_ref(Path)]
#[display("'{}'", self.0.display())]
#[must_use]
pub struct RelativePath(PathBuf);

impl RelativePath {
    // TODO: This doesn't check the parameter in any way. Should it?
    pub fn new(path: &str) -> Self {
        Self(path.into())
    }

    pub fn try_from_absolute(base_dir: &Path, path: &AbsolutePath) -> Result<Self, anyhow::Error> {
        let shared_dir = path::absolute(base_dir).with_context(|| {
            format!(
                "Failed to get absolute path for shared directory '{}'",
                base_dir.display()
            )
        })?;
        // A symlink such as macOS's `/var` -> `/private/var` can make the two spellings differ.
        let canonical = || {
            Some((
                sandbox::absolute_and_canonicalized(&shared_dir).ok()?,
                sandbox::absolute_and_canonicalized(path).ok()?,
            ))
        };
        let relative_path = match path.strip_prefix(&shared_dir) {
            Ok(relative_path) => Ok(relative_path.to_path_buf()),
            Err(error) => canonical()
                .and_then(|(dir, path)| Some(path.strip_prefix(dir).ok()?.to_path_buf()))
                .ok_or(error),
        }
        .with_context(|| {
            format!(
                "The path {path} is not in the shared directory '{}'. Your plugin probably doesn't support opening files from multiple TeamTypeV directories.",
                shared_dir.display()
            )
        })?;

        if relative_path.iter().count() == 0 {
            bail!("base_dir was equal to path when computing relative path");
        }
        // `/base/../x` strips to `../x`, which would become a shared document key.
        if relative_path
            .components()
            .any(|component| !matches!(component, path::Component::Normal(_)))
        {
            bail!("The path {path} contains `.` or `..` components");
        }

        Ok(Self(relative_path))
    }

    pub fn try_from_path(base_dir: &Path, path: &Path) -> Result<Self, anyhow::Error> {
        let absolute_path = AbsolutePath::try_from(path.to_path_buf())?;
        Self::try_from_absolute(base_dir, &absolute_path)
    }
}

impl From<&RelativePath> for Prop {
    fn from(val: &RelativePath) -> Self {
        Self::Map(val.0.display().to_string())
    }
}

// TODO: Wrap the newtype around url::Url instead?
#[derive(Debug, Clone, PartialEq, Eq, Hash, Deref)]
#[must_use]
pub struct FileUri(String);

impl FileUri {
    pub fn to_absolute_path(&self) -> AbsolutePath {
        let path_buf = Url::parse(self)
            .expect("Should be able to parse file:// URL as Url")
            .to_file_path()
            .expect("Should be able to convert Url to PathBuf");
        AbsolutePath::try_from(path_buf).expect("File URI should contain an absolute path")
    }
}

impl TryFrom<String> for FileUri {
    type Error = anyhow::Error;

    fn try_from(string: String) -> Result<Self, Self::Error> {
        // TODO: Could be written simpler?
        if string.starts_with("file:///") {
            // Use the url crate to properly URL encode the path (spaces should be "%20", for example).
            Ok(Self(
                Url::parse(&string)
                    .expect("Should be able to parse file:// URL")
                    .to_string(),
            ))
        } else {
            bail!("File URI '{string}' does not start with 'file:///'");
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_file_path_for_uri_fails_not_absolute() {
        assert!(AbsolutePath::try_from("this/is/absolutely/not/absolute").is_err());
    }

    #[test]
    fn test_file_path_for_uri_fails_not_within_base_dir() {
        let base_dir = Path::new("/an/absolute/path");
        let path = AbsolutePath::try_from("/a/very/different/path").unwrap();

        assert!(RelativePath::try_from_absolute(base_dir, &path,).is_err());
    }

    #[test]
    fn test_file_path_for_uri_fails_not_within_base_dir_suffix() {
        let base_dir = Path::new("/an/absolute/path");
        let path = AbsolutePath::try_from("/an/absolute/path2/file").unwrap();

        assert!(RelativePath::try_from_absolute(base_dir, &path,).is_err());
    }

    #[test]
    fn test_relative_path_rejects_dotdot() {
        let base_dir = Path::new("/an/absolute/path");
        let path = AbsolutePath::try_from("/an/absolute/path/../escape").unwrap();
        assert!(RelativePath::try_from_absolute(base_dir, &path).is_err());
    }

    #[test]
    fn test_file_path_for_uri_fails_only_base_dir() {
        let base_dir = Path::new("/an/absolute/path");
        let path = AbsolutePath::try_from("/an/absolute/path").unwrap();

        assert!(RelativePath::try_from_absolute(base_dir, &path,).is_err());
    }

    #[test]
    fn test_file_path_for_uri_works() {
        let base_dir = Path::new("/an/absolute/path");

        let file_paths = vec!["file1", "sub/file3", "sub"];
        for &expected in &file_paths {
            let uri =
                FileUri::try_from(format!("file://{}/{}", base_dir.display(), expected)).unwrap();
            let absolute_path = uri.to_absolute_path();
            let relative_path = RelativePath::try_from_absolute(base_dir, &absolute_path).unwrap();

            assert_eq!(RelativePath::new(expected), relative_path);
        }
    }

    #[test]
    fn test_relative_path_through_symlinked_base_dir() {
        let dir = tempfile::tempdir().unwrap();
        let real = dir.path().join("real");
        std::fs::create_dir(&real).unwrap();
        let link = dir.path().join("link");
        std::os::unix::fs::symlink(&real, &link).unwrap();
        let path = AbsolutePath::try_from(real.join("new.txt")).unwrap();
        assert_eq!(
            RelativePath::try_from_absolute(&link, &path).unwrap(),
            RelativePath::new("new.txt")
        );
    }

    #[test]
    fn test_uri_roundtrip_keeps_reserved_characters() {
        for path in ["/a#b", "/a?b", "/a%20b", "/a b"] {
            let path = AbsolutePath::try_from(path).unwrap();
            assert_eq!(path.to_file_uri().to_absolute_path(), path);
        }
    }

    #[test]
    fn test_uri_encoding_works_with_spaces() {
        let uri = FileUri::try_from("file:///a/b/file with spaces".to_string()).unwrap();
        assert_eq!("file:///a/b/file%20with%20spaces", uri.0);
    }

    #[test]
    fn test_uri_decoding_works_with_spaces() {
        let uri = FileUri::try_from("file:///a/b/file with spaces".to_string()).unwrap();
        let absolute_path = AbsolutePath::try_from("/a/b/file with spaces").unwrap();
        assert_eq!(absolute_path, uri.to_absolute_path());
    }
}
