// SPDX-FileCopyrightText: 2026 Sichang He
//
// SPDX-License-Identifier: AGPL-3.0-or-later

//! The help pages behind `teamtypev guide`. The same files are included in the book, so the
//! command line and the website cannot disagree.

/// A help page: its names (the first is the main one), a one-line summary, and its text.
pub struct Topic {
    pub names: &'static [&'static str],
    pub summary: &'static str,
    pub text: &'static str,
}

pub static TOPICS: &[Topic] = &[
    Topic {
        names: &["files", "images", "ignore"],
        summary: "A file or image does not show up for the other person",
        text: include_str!("guide/files.md"),
    },
    Topic {
        names: &["slow", "perf"],
        summary: "Joining or syncing feels slow; what to send",
        text: include_str!("guide/slow.md"),
    },
];

impl Topic {
    /// The text without the book's authorship line.
    fn terminal_text(&self) -> String {
        self.text
            .lines()
            .filter(|line| !line.starts_with("(authored by agents"))
            .collect::<Vec<_>>()
            .join("\n")
            + "\n"
    }
}

/// The topic called `name`.
pub fn find(name: &str) -> Option<&'static Topic> {
    TOPICS.iter().find(|topic| {
        topic
            .names
            .iter()
            .any(|candidate| candidate.eq_ignore_ascii_case(name))
    })
}

/// The text of `teamtypev guide [topic]`, or the list of topics for an unknown name.
pub fn page(topic: Option<&str>) -> Result<String, String> {
    topic.map_or_else(
        || Ok(index()),
        |name| {
            find(name)
                .map(Topic::terminal_text)
                .ok_or_else(|| format!("No help page called '{name}'.\n\n{}", index()))
        },
    )
}

/// The list of topics.
pub fn index() -> String {
    use std::fmt::Write;
    let mut out =
        String::from("TeamTypeV help pages. Show one with `teamtypev guide <topic>`:\n\n");
    for topic in TOPICS {
        let _ = writeln!(
            out,
            "  {:<8} {}   (also: {})",
            topic.names[0],
            topic.summary,
            topic.names[1..].join(", ")
        );
    }
    out += "\nThe full manual is the book in the repository: https://github.com/SichangHe/TeamTypeV/tree/main/book/src\n";
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_topic_is_found_by_each_of_its_names() {
        for topic in TOPICS {
            for name in topic.names {
                assert!(std::ptr::eq(find(name).unwrap(), topic), "{name}");
                assert!(find(&name.to_uppercase()).is_some(), "{name}");
            }
            assert!(topic.text.starts_with("# "), "{}", topic.names[0]);
        }
    }

    #[test]
    fn the_files_page_names_the_fix_for_hidden_images() {
        let text = page(Some("images")).unwrap();
        assert!(text.contains(".teamtypevignore"));
        assert!(text.contains("!*.png"));
        assert!(text.contains(".gitignore"));
        assert!(text.contains("restart"));
        assert!(!text.contains("authored by agents"));
    }

    #[test]
    fn an_unknown_topic_lists_the_known_ones() {
        let error = page(Some("nonsense")).unwrap_err();
        assert!(error.contains("No help page called 'nonsense'"));
        for topic in TOPICS {
            assert!(error.contains(topic.names[0]), "{error}");
        }
        assert!(page(None).unwrap().contains("teamtypev guide <topic>"));
    }
}
