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
#[serde(try_from = "PathBuf")]
#[as_ref(Path)]
#[display("'{}'", self.0.display())]
#[must_use]
pub struct AbsolutePath(PathBuf);

impl AbsolutePath {
    pub fn from_parts(base: &Path, relative_path: &RelativePath) -> Result<Self, anyhow::Error> {
        // `join` would let an absolute part replace `base` and `..` climb out of it.
        Self::try_from(base.join(RelativePath::checked(&relative_path.0)?))
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
        // A URL cannot spell `..`: `/a/..` would come back as `/`.
        if path.components().any(|c| c == path::Component::ParentDir) {
            bail!("Path '{}' contains `..`", path.display());
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
#[serde(try_from = "PathBuf")]
#[as_ref(Path)]
#[display("'{}'", self.0.display())]
#[must_use]
pub struct RelativePath(PathBuf);

impl RelativePath {
    /// For names that are known to be valid, such as literals.
    pub fn new(path: &str) -> Self {
        Self(path.into())
    }

    /// Checks a name that did not come from us, such as a key a peer put in the document.
    pub fn try_new(path: &str) -> Result<Self, anyhow::Error> {
        Self::try_from(PathBuf::from(path))
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

impl RelativePath {
    fn checked(path: &Path) -> Result<&Path, anyhow::Error> {
        // `a/./b`, `a//b` and `a/` are other spellings of `a/b`: one key per file.
        if path.as_os_str().is_empty()
            || path.components().collect::<PathBuf>().as_os_str() != path.as_os_str()
            || path
                .components()
                .any(|component| !matches!(component, path::Component::Normal(_)))
        {
            bail!("'{}' is not a plain relative path", path.display());
        }
        Ok(path)
    }
}

impl TryFrom<PathBuf> for RelativePath {
    type Error = anyhow::Error;

    fn try_from(path: PathBuf) -> Result<Self, Self::Error> {
        Self::checked(&path)?;
        Ok(Self(path))
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
        if let Some(rest) = string.strip_prefix("file:///") {
            // The parser resolves dot segments, also as `%2e`, before we could see them.
            if rest.split('/').any(|segment| {
                matches!(
                    segment.to_ascii_lowercase().as_str(),
                    "." | ".." | "%2e" | "%2e%2e" | ".%2e" | "%2e."
                )
            }) {
                bail!("File URI '{string}' contains a dot segment");
            }
            // A bare `#` or `?` would silently drop the rest of the path: a different file.
            // A raw `\` would be read as `/`.
            if string.contains(['#', '?', '\\']) {
                bail!("File URI '{string}' contains an unencoded `#`, `?` or `\\`");
            }
            // Use the url crate to properly URL encode the path (spaces should be "%20", for example).
            let url =
                Url::parse(&string).with_context(|| format!("Invalid file URI '{string}'"))?;
            // `to_absolute_path` relies on this succeeding.
            let path = url
                .to_file_path()
                .map_err(|()| anyhow::anyhow!("File URI '{string}' is not a local path"))?;
            let _ = AbsolutePath::try_from(path)?;
            Ok(Self(url.to_string()))
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
        assert!(AbsolutePath::try_from("/an/absolute/path/../escape").is_err());
        let path = AbsolutePath::try_from("/an/absolute/path/x").unwrap();
        assert!(RelativePath::try_from_absolute(base_dir, &path).is_ok());
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

    use std::{ffi::OsString, os::unix::ffi::OsStringExt};

    /// `/d/<name>` roundtrips through a URI, and is rejected exactly when it has a `..` component.
    fn roundtrips(name: &[u8]) -> bool {
        let has_dotdot = name.split(|b| *b == b'/').any(|segment| segment == b"..");
        let mut bytes = b"/d/".to_vec();
        bytes.extend_from_slice(name);
        let Ok(path) = AbsolutePath::try_from(PathBuf::from(OsString::from_vec(bytes))) else {
            return has_dotdot;
        };
        if has_dotdot {
            return false;
        }
        path.to_file_uri().to_absolute_path() == path
    }

    #[test]
    fn test_uri_roundtrip_all_single_bytes_and_pairs() {
        let failures: Vec<_> = (0..=255u8)
            .flat_map(|a| (0..=255u8).map(move |b| [a, b]))
            .flat_map(|pair| [vec![pair[0]], pair.to_vec()])
            .filter(|name| !roundtrips(name))
            .collect();
        assert!(
            failures.is_empty(),
            "{} failures, first: {:?}",
            failures.len(),
            failures.first()
        );
    }

    #[test]
    fn test_uri_roundtrip_random_names() {
        use rand::{RngExt, SeedableRng, rngs::StdRng};
        let mut rng = StdRng::seed_from_u64(7);
        let alphabet = b"#?%\\\n\r\t /.:@[]{}\"'<>|^`~\x00\x7f\xc3\xa9\xff\xed\xa0\x80ab0";
        for _ in 0..200_000 {
            let len = rng.random_range(1..24);
            let name: Vec<u8> = std::iter::repeat_with(|| {
                if rng.random_bool(0.5) {
                    alphabet[rng.random_range(0..alphabet.len())]
                } else {
                    rng.random()
                }
            })
            .take(len)
            .collect();
            assert!(roundtrips(&name), "{name:?}");
        }
    }

    #[test]
    fn test_untrusted_paths_are_checked() {
        assert!(serde_json::from_str::<AbsolutePath>("\"relative\"").is_err());
        assert!(serde_json::from_str::<AbsolutePath>("\"/a/../b\"").is_err());
        for bad in [
            "/outside",
            "../x",
            "a/../../x",
            "",
            ".",
            "a/./b",
            "a//b",
            "a/",
            "a/.",
        ] {
            assert!(RelativePath::try_new(bad).is_err(), "{bad}");
            assert!(serde_json::from_str::<RelativePath>(&format!("{bad:?}")).is_err());
            let unchecked = RelativePath::new(bad);
            assert!(AbsolutePath::from_parts(Path::new("/shared"), &unchecked).is_err());
        }
        let ok = RelativePath::try_new("a/b c#?").unwrap();
        assert_eq!(
            AbsolutePath::from_parts(Path::new("/shared"), &ok).unwrap(),
            AbsolutePath::try_from("/shared/a/b c#?").unwrap()
        );
    }

    #[test]
    fn test_file_uri_with_fragment_or_query_is_rejected() {
        for uri in ["file:///a#b", "file:///a?b", "file:///a/b#"] {
            assert!(FileUri::try_from(uri.to_string()).is_err(), "{uri}");
        }
    }

    #[test]
    fn test_dotdot_paths_are_rejected_not_rewritten() {
        for path in ["/a/../b", "/a/b/..", "/.."] {
            assert!(AbsolutePath::try_from(path).is_err(), "{path}");
        }
    }

    #[test]
    fn test_malformed_file_uris_are_errors_not_panics() {
        for uri in [
            "file:///a\\b",
            "file://host/a",
            "file:///[",
            "file:///a/%",
            "file://///",
            "file:///a/%2e%2e/b",
            "file:///..",
            "file:///d/a/./b",
            "file://[::1]/a",
            "file:///a b\\",
        ] {
            let result = std::panic::catch_unwind(|| {
                FileUri::try_from(uri.to_string()).map(|uri| uri.to_absolute_path())
            });
            assert!(result.is_ok(), "panicked on {uri}");
            println!("{uri} -> {:?}", result.ok());
        }
        assert!(FileUri::try_from("file:///a\\b".to_string()).is_err());
        assert!(FileUri::try_from("file://host/a".to_string()).is_err());
        for uri in [
            "file:///a/%2e%2e/b",
            "file:///..",
            "file:///d/a/./b",
            "file:///d/%2E./x",
        ] {
            assert!(FileUri::try_from(uri.to_string()).is_err(), "{uri}");
        }
    }
}
