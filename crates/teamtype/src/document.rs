// SPDX-FileCopyrightText: 2024 blinry <mail@blinry.org>
// SPDX-FileCopyrightText: 2024 zormit <nt4u@kpvn.de>
// SPDX-FileCopyrightText: 2026 Caleb Maclennan <caleb@alerque.com>
//
// SPDX-License-Identifier: AGPL-3.0-or-later

use std::borrow::Cow;
use std::collections::HashMap;

use anyhow::bail;
use anyhow::{Context, Result};
use automerge::{
    AutoCommit, ChangeHash, ObjId, ObjType, Patch, PatchAction, PatchLog, Prop, ReadDoc,
    ScalarValue, Value,
    sync::{Message as AutomergeSyncMessage, State as AutomergeSyncState, SyncDoc},
    transaction::Transactable,
};
use dissimilar::Chunk;
use tracing::{debug, info, warn};

use crate::{
    path::RelativePath,
    types::{EditorTextDelta, PatchEffect, TextDelta},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Content {
    String(String),
    Bytes(Vec<u8>),
}

/// Encapsulates the Automerge `AutoCommit` and provides a generic interface,
/// s.t. we don't need to worry about automerge internals elsewhere.
///
/// The interface allows us to apply changes to the CRDT in two ways:
/// - synchronization with other CRDTs through sync messages
/// - applying a delta (coming from an editor) directly
///
/// Furthermore, there's a way to retrieve and initialize the content.
#[derive(Debug)]
#[must_use]
pub struct Document {
    files: HashMap<RelativePath, Content>,
    doc: AutoCommit,
}

impl Default for Document {
    fn default() -> Self {
        // We're baking a single static initial state into the binary rather than generating new documents
        // from a random seed in each client so that documents created by independent peers can be merged.
        // See build.rs for how to force a rebuild of this initial state, but be aware updating the initial
        // state is a breaking change that will make TeamTypeV peers incompatible with each other.
        // See https://automerge.org/docs/cookbook/modeling-data/#setting-up-an-initial-document-structure
        let initial_automerge_doc_bytes = include_bytes!("initial_automerge_doc.bin");
        Self::load(initial_automerge_doc_bytes)
    }
}

impl Document {
    // TODO: use sth like try_load + Result to bubble up potential errors.
    /// Loads every intact change; a torn tail (a crash while appending) is dropped.
    pub fn try_load(bytes: &[u8]) -> Result<Self> {
        let doc = AutoCommit::load_with_options(
            bytes,
            automerge::LoadOptions::new().on_partial_load(automerge::OnPartialLoad::Ignore),
        )?;
        let mut result = Self {
            files: HashMap::default(),
            doc,
        };
        result.update_files();
        Ok(result)
    }

    pub fn load(bytes: &[u8]) -> Self {
        let doc =
            AutoCommit::load(bytes).expect("Failed to load Automerge document from given bytes");
        let mut result = Self {
            files: HashMap::default(),
            doc,
        };
        result.update_files();
        result
    }

    #[must_use]
    pub fn save(&mut self) -> Vec<u8> {
        self.doc.save()
    }

    #[must_use]
    pub fn save_incremental(&mut self) -> Vec<u8> {
        self.doc.save_incremental()
    }

    #[must_use]
    pub fn actor_id(&self) -> String {
        self.doc.get_actor().to_hex_string()
    }

    #[must_use]
    pub fn receive_sync_message_log_patches(
        &mut self,
        message: AutomergeSyncMessage,
        peer_state: &mut AutomergeSyncState,
    ) -> Vec<Patch> {
        let before = self.visible_text_objects();
        let mut patch_log = PatchLog::active();
        self.doc
            .sync()
            .receive_sync_message_log_patches(peer_state, message, &mut patch_log)
            .expect("Failed to apply sync message to Automerge document");
        let patches =
            self.replaced_text_objects_as_puts(self.doc.make_patches(&mut patch_log), &before);

        // Update files cache.
        for patch in &patches {
            match PatchEffect::from_patch(patch) {
                PatchEffect::FileChange(file_text_delta) => {
                    let old_text = if let Some(Content::String(old_text)) =
                        self.files.get(&file_text_delta.file_path)
                    {
                        old_text
                    } else {
                        // File does not exist yet, create an empty one.
                        self.files.insert(
                            file_text_delta.file_path.clone(),
                            Content::String(String::new()),
                        );
                        // And set old_text to the empty string.
                        ""
                    };
                    // We're not in a good position here to "reject" the sync message, so let's
                    // panic on errors.
                    let new_text = file_text_delta.delta.apply_to(old_text).expect("If Automerge and our file cache work correctly, this delta should always apply");
                    self.files
                        .insert(file_text_delta.file_path, Content::String(new_text));
                }
                PatchEffect::FileRemoval(path) => {
                    // A removal is also reported when a peer's file of the same name replaced
                    // ours. That file starts empty and later patches fill it; without an entry
                    // here an empty one would be missing from the cache but present in the doc.
                    if self.text_obj(&path).is_ok() {
                        self.files.insert(path, Content::String(String::new()));
                    } else {
                        self.files.remove(&path);
                    }
                }
                PatchEffect::FileBytes(path, bytes) => {
                    self.files.insert(path, Content::Bytes(bytes));
                }
                PatchEffect::NoEffect => {
                    // Nothing to do.
                }
            }
        }

        patches
    }

    fn visible_text_objects(&self) -> HashMap<RelativePath, ObjId> {
        self.files
            .keys()
            .filter_map(|path| Some((path.clone(), self.text_obj(path).ok()?)))
            .collect()
    }

    /// When peers concurrently create the same path, Automerge may switch the visible text object
    /// but report only `Conflict` followed by the new object's text as edits of the old one.
    /// A receiver would insert that text into the old text. Report the switch as what it is: a
    /// new text object at that path, like `PutMap`.
    fn replaced_text_objects_as_puts(
        &self,
        patches: Vec<Patch>,
        before: &HashMap<RelativePath, ObjId>,
    ) -> Vec<Patch> {
        patches
            .into_iter()
            .map(|mut patch| {
                if let PatchAction::Conflict {
                    prop: Prop::Map(key),
                } = &patch.action
                    && let Ok(now) = self.text_obj(&RelativePath::new(key))
                    && before
                        .get(&RelativePath::new(key))
                        .is_some_and(|was| *was != now)
                {
                    patch.action = PatchAction::PutMap {
                        key: key.clone(),
                        value: (Value::Object(ObjType::Text), now),
                        conflict: true,
                    };
                }
                patch
            })
            .collect()
    }

    #[must_use]
    pub fn generate_sync_message(
        &mut self,
        peer_state: &mut AutomergeSyncState,
    ) -> Option<AutomergeSyncMessage> {
        self.doc.sync().generate_sync_message(peer_state)
    }

    pub fn apply_delta_to_doc(
        &mut self,
        delta: &TextDelta,
        file_path: &RelativePath,
    ) -> Result<()> {
        // Update Automerge document.
        let text_obj = self
            .text_obj(file_path)
            .expect("Couldn't get automerge text object, so not able to modify it");
        let mut offset = 0isize;

        let Some(Content::String(text)) = self.current_file_content(file_path) else {
            bail!("File {file_path} not initialized before applying delta");
        };
        // Clone so that `self` is no longer borrowed.
        let text = text.clone();

        // TODO: Can we avoid/handle this panic, same as the one below?
        let ed_delta = EditorTextDelta::try_from_delta(delta.clone(), &text)?;

        for op in &ed_delta.0 {
            // TODO: Can we avoid/handle this panic, e.g. by undoing previous deltas of this set?
            let (start, length) = op.range.as_relative(&text)?;
            self.doc
                .splice_text(
                    text_obj.clone(),
                    ((start as isize) + offset) as usize,
                    length as isize,
                    &op.replacement,
                )
                .expect("Failed to splice Automerge text object");
            offset -= length as isize;
            offset += op.replacement.chars().count() as isize;
        }

        // Update cached content.
        let Some(Content::String(old_text)) = self.files.get(file_path) else {
            bail!("Did not find text content in files cache at file_path");
        };
        let new_text = delta.apply_to(old_text)?;
        self.files
            .insert(file_path.clone(), Content::String(new_text));

        Ok(())
    }

    pub fn current_file_content(&self, file_path: &RelativePath) -> Option<&Content> {
        self.files.get(file_path)
    }

    // TODO: Refactor such that file_content_at can also return bytes (and get rid of get_bytes_at)
    pub fn file_content_at(
        &self,
        file_path: &RelativePath,
        heads: &[ChangeHash],
    ) -> Result<String> {
        self.text_obj_at(file_path, heads).map(|to| {
            self.doc
                .text_at(to, heads)
                .expect("Failed to get string from Automerge text object")
        })
    }

    /// Used to get the contents of a binary file at a specific state.
    pub fn get_bytes_at(&self, file_path: &RelativePath, heads: &[ChangeHash]) -> Result<Vec<u8>> {
        let file_map = self
            .top_level_map_obj("files")
            .expect("Failed to get files Map object");

        // If the content hasn't changed, don't write to the file. This prevents irrelevant watcher events.

        match self.doc.get_at(&file_map, file_path, heads) {
            Ok(Some((Value::Scalar(Cow::Owned(ScalarValue::Bytes(bytes))), _))) => Ok(bytes),
            Ok(Some((Value::Scalar(Cow::Borrowed(ScalarValue::Bytes(bytes))), _))) => {
                // TODO: Potentially memory-heavy operation. Figure out how to deal with Cows. Moo.
                Ok(bytes.clone())
            }
            _ => {
                bail!("Failed to provide contents of binary file at {file_path}");
            }
        }
    }

    // This function is used to integrate text that was changed while the daemon was offline.
    // We need to calculate the patches compared to the current CRDT content, and apply them.
    pub fn update_text(
        &mut self,
        desired_text: &str,
        file_path: &RelativePath,
    ) -> Option<TextDelta> {
        if self.text_obj(file_path).is_ok() {
            let Some(Content::String(current_text)) = self.current_file_content(file_path) else {
                panic!("Failed to get {file_path} text object");
            };

            let chunks = dissimilar::diff(current_text, desired_text);
            if let [] | [Chunk::Equal(_)] = chunks.as_slice() {
                return None;
            }

            let text_delta: TextDelta = chunks.into();
            info!("Detected change of {file_path}. Updating.");
            debug!("Full delta of this update: {text_delta}");
            self.apply_delta_to_doc(&text_delta, file_path).expect("Failed to apply delta to document while updating text. Probably the delta doesn't fit the document content.");

            self.files.insert(
                file_path.clone(),
                Content::String(String::from(desired_text)),
            );

            Some(text_delta)
        } else {
            // The file doesn't exist in the CRDT yet, so we need to initialize it.
            self.set_file(Content::String(desired_text.to_string()), file_path);
            None
        }
    }

    pub fn remove_file(&mut self, file_path: &RelativePath) {
        if !self.file_exists(file_path) {
            debug!("Failed to get {file_path} key object, so I can't remove it from the CRDT.");
            return;
        }

        info!("Removing {file_path} from the TeamTypeV history.");

        // Remove from Automerge document.
        let file_map = self
            .top_level_map_obj("files")
            .expect("Failed to get files Map object");
        self.doc
            .delete(file_map, file_path)
            .expect("Failed to delete text object");

        // Remove from files cache.
        self.files.remove(file_path);
    }

    pub fn set_file(&mut self, content: Content, file_path: &RelativePath) {
        match content {
            Content::String(ref text) => {
                info!("Initializing {file_path} in the TeamTypeV history.");
                self.files
                    .insert(file_path.clone(), Content::String(text.clone()));

                // Now it should definitely work?
                let file_map = self
                    .top_level_map_obj("files")
                    .expect("Failed to get files Map object");

                let text_obj = self
                    .doc
                    .put_object(file_map, file_path, ObjType::Text)
                    .expect("Failed to initialize text object in Automerge document");
                self.doc
                    .splice_text(text_obj, 0, 0, text)
                    .expect("Failed to splice text into Automerge text object");
            }
            Content::Bytes(ref bytes) => {
                // If the content hasn't changed, don't write to the file. This prevents irrelevant watcher events.
                if let Some(Content::Bytes(current_bytes)) = self.current_file_content(file_path)
                    && current_bytes == bytes
                {
                    return;
                }

                // Update Automerge document.
                let file_map = self
                    .top_level_map_obj("files")
                    .expect("Failed to get files Map object");

                // If the file was not in the document before, log this.
                if !self.file_exists(file_path) {
                    info!("Initializing binary {file_path} in the TeamTypeV history.");
                }

                self.doc
                    .put(file_map, file_path, bytes.clone())
                    .expect("Failed to initialize bytes object in Automerge document");
            }
        }
        // Update file cache.
        self.files.insert(file_path.clone(), content);
    }

    fn update_files(&mut self) {
        if let Ok(file_map) = self.top_level_map_obj("files") {
            for file_path in self.doc.keys(&file_map) {
                match self.doc.get(&file_map, &file_path) {
                    Ok(Some((Value::Object(ObjType::Text), text_obj))) => {
                        let string = self
                            .doc
                            .text(&text_obj)
                            .expect("Should be able to retrieve text");
                        self.files
                            .insert(RelativePath::new(&file_path), Content::String(string));
                    }
                    Ok(Some((Value::Scalar(Cow::Owned(ScalarValue::Bytes(bytes))), _))) => {
                        self.files
                            .insert(RelativePath::new(&file_path), Content::Bytes(bytes));
                    }
                    Ok(Some((Value::Scalar(Cow::Borrowed(ScalarValue::Bytes(bytes))), _))) => {
                        // TODO: Potentially memory-heavy operation. Figure out how to deal with Cows. Moo.
                        self.files
                            .insert(RelativePath::new(&file_path), Content::Bytes(bytes.clone()));
                    }
                    _ => {
                        // A peer can put anything under a key; only text and bytes are files.
                        warn!("Ignoring unsupported value at {file_path} in the document");
                    }
                }
            }
        }
    }

    fn top_level_map_obj(&self, name: &str) -> Result<ObjId> {
        let file_map = self.doc.get(automerge::ROOT, name);
        if let Ok(Some((Value::Object(ObjType::Map), file_map))) = file_map {
            Ok(file_map)
        } else {
            bail!("Automerge document doesn't have a {name} Map object")
        }
    }

    fn text_obj(&self, file_path: &RelativePath) -> Result<ObjId> {
        let file_map = self.top_level_map_obj("files")?;
        let text_obj = self
            .doc
            .get(file_map, file_path)
            .with_context(|| format!("Failed to get {file_path} key from Automerge document"))?;
        if let Some((Value::Object(ObjType::Text), text_obj)) = text_obj {
            Ok(text_obj)
        } else {
            bail!(
                "Automerge document doesn't have a {file_path} Text object, so I can't provide it"
            )
        }
    }

    fn text_obj_at(&self, file_path: &RelativePath, heads: &[ChangeHash]) -> Result<ObjId> {
        // I hope this one is always there...
        let file_map = self.top_level_map_obj("files")?;

        let text_obj = self
            .doc
            .get_at(file_map, file_path, heads)
            .with_context(|| format!("Failed to get {file_path} key from Automerge document"))?;
        if let Some((Value::Object(ObjType::Text), text_obj)) = text_obj {
            Ok(text_obj)
        } else {
            bail!(
                "Automerge document doesn't have a {file_path} Text object, so I can't provide it"
            )
        }
    }

    #[must_use]
    pub fn files(&self) -> Vec<RelativePath> {
        self.files.keys().map(Clone::clone).collect()
    }

    #[must_use]
    pub fn file_exists(&self, file_path: &RelativePath) -> bool {
        self.files.contains_key(file_path)
    }

    #[must_use]
    pub fn has_changes(&self, heads: &[ChangeHash]) -> bool {
        heads
            .iter()
            .all(|head| self.doc.get_change_by_hash(head).is_some())
    }

    pub fn get_heads(&mut self) -> Vec<ChangeHash> {
        self.doc.get_heads()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::factories::*;

    impl Document {
        fn assert_file_content(&self, file_path: &RelativePath, content: &str) {
            assert_eq!(
                self.current_file_content(file_path),
                Some(Content::String(content.to_string())).as_ref()
            );
        }
    }

    #[test]
    fn can_initialize_content() {
        let mut document = Document::default();
        let text = "To be or not to be, that is the question";
        let file = RelativePath::new("text");

        document.set_file(Content::String(text.to_string()), &file);

        document.assert_file_content(&file, text);
    }

    #[test]
    fn can_initialize_content_multifile() {
        let mut document = Document::default();

        let text = "To be or not to be, that is the question";
        let text2 = "2b||!2b, that is the question";

        let file1 = RelativePath::new("text");
        let file2 = RelativePath::new("text2");

        document.set_file(Content::String(text.to_string()), &file1);
        document.set_file(Content::String(text2.to_string()), &file2);

        document.assert_file_content(&file1, text);
        document.assert_file_content(&file2, text2);
    }

    #[test]
    fn retrieve_content_file_nonexistent_errs() {
        let document = Document::default();
        assert!(
            document
                .current_file_content(&RelativePath::new("text"))
                .is_none()
        );
    }

    fn apply_delta_to_doc_works(initial: &str, delta: &TextDelta, expected: &str) {
        let mut document = Document::default();
        let file = RelativePath::new("text");

        document.set_file(Content::String(initial.to_string()), &file);
        document.apply_delta_to_doc(delta, &file).unwrap();

        document.assert_file_content(&file, expected);
    }

    #[test]
    fn can_apply_delta_basic_insertion() {
        let delta = insert(0, "foobar");
        apply_delta_to_doc_works("", &delta, "foobar");
    }

    #[test]
    fn can_apply_delta_basic_deletion() {
        let delta = delete(3, 3);
        apply_delta_to_doc_works("foobar", &delta, "foo");
    }

    #[test]
    fn can_apply_delta_basic_replacement() {
        let delta = replace(1, 2, "uu");
        apply_delta_to_doc_works("foobar", &delta, "fuubar");
    }

    #[test]
    fn can_apply_delta_multiple_ops() {
        let initial_text = "To be or not to be, that is the question";

        let mut delta = insert(3, "m");
        delta.delete(1); // "b"
        delta.retain(5); // "e or "
        delta.delete(4); // "not "
        delta.retain(3); // "to "
        delta.delete(2); // "be"
        delta.insert("you");

        apply_delta_to_doc_works(
            initial_text,
            &delta,
            "To me or to you, that is the question",
        );
    }

    #[test]
    fn apply_delta_only_changes_specified_file() {
        let mut document = Document::default();

        let file1 = RelativePath::new("text");
        let file2 = RelativePath::new("text2");

        document.set_file(Content::String(String::new()), &file1);
        document.set_file(Content::String(String::new()), &file2);

        let delta = insert(0, "foobar");
        document.apply_delta_to_doc(&delta, &file1).unwrap();

        document.assert_file_content(&file1, "foobar");
        document.assert_file_content(&file2, "");
    }

    /// Exchanges sync messages until both sides are idle; returns patches `b` received.
    fn sync(a: &mut Document, b: &mut Document) -> Vec<Patch> {
        let (mut sa, mut sb) = (AutomergeSyncState::new(), AutomergeSyncState::new());
        let mut received = vec![];
        loop {
            let (ma, mb) = (
                a.generate_sync_message(&mut sa),
                b.generate_sync_message(&mut sb),
            );
            if ma.is_none() && mb.is_none() {
                return received;
            }
            if let Some(m) = ma {
                received.extend(b.receive_sync_message_log_patches(m, &mut sb));
            }
            if let Some(m) = mb {
                let _ = a.receive_sync_message_log_patches(m, &mut sa);
            }
        }
    }

    #[test]
    fn replaced_text_object_clears_stale_text() {
        let file = RelativePath::new("file");
        let (mut a, mut b) = (Document::default(), Document::default());
        a.set_file(Content::String("old".into()), &file);
        sync(&mut a, &mut b);
        a.remove_file(&file);
        assert!(a.update_text("new", &file).is_none());
        let patches = sync(&mut a, &mut b);
        b.assert_file_content(&file, "new");
        let mut editor = "old".to_owned();
        for effect in PatchEffect::from_crdt_patches(&patches) {
            match effect {
                PatchEffect::FileRemoval(_) => editor.clear(),
                PatchEffect::FileChange(d) => editor = d.delta.apply_to(&editor).unwrap(),
                PatchEffect::FileBytes(..) | PatchEffect::NoEffect => {}
            }
        }
        assert_eq!(editor, "new");
    }

    /// A peer can put any value under a `files` key. The daemon must not crash on it; the cache
    /// must keep equalling what a reload of the CRDT reads, and a file replaced by an
    /// unsupported value counts as removed.
    #[test]
    fn unsupported_values_from_peers_do_not_crash_and_keep_cache_equal_to_crdt() {
        let (mut a, mut b) = (Document::default(), Document::default());
        let keep = RelativePath::new("keep");
        let gone = RelativePath::new("gone");
        a.set_file(Content::String("t".into()), &keep);
        a.set_file(Content::String("old".into()), &gone);
        sync(&mut a, &mut b);
        b.assert_file_content(&gone, "old");

        let files = a.top_level_map_obj("files").unwrap();
        a.doc.put(&files, "gone", 7_i64).unwrap();
        a.doc.put(&files, "int", 5_i64).unwrap();
        a.doc.put_object(&files, "map", ObjType::Map).unwrap();
        let patches = sync(&mut a, &mut b);
        let effects = PatchEffect::from_crdt_patches(&patches);
        assert!(
            effects
                .iter()
                .any(|e| matches!(e, PatchEffect::FileRemoval(p) if *p == gone))
        );

        b.assert_file_content(&keep, "t");
        for name in ["gone", "int", "map"] {
            let path = RelativePath::new(name);
            assert_eq!(b.current_file_content(&path), None, "{name}");
            assert_cache_matches_crdt(&mut b, &path);
        }
    }

    /// Loading a document that holds an unsupported value must not crash either.
    #[test]
    fn loading_a_document_with_unsupported_values_skips_them() {
        let mut a = Document::default();
        a.set_file(Content::String("t".into()), &RelativePath::new("keep"));
        let files = a.top_level_map_obj("files").unwrap();
        a.doc.put(&files, "int", 5_i64).unwrap();
        let bytes = a.save();
        let loaded = Document::load(&bytes);
        assert_eq!(loaded.current_file_content(&RelativePath::new("int")), None);
        loaded.assert_file_content(&RelativePath::new("keep"), "t");
    }

    /// The cache must equal what the CRDT itself holds, which a reload reads without the cache.
    fn assert_cache_matches_crdt(document: &mut Document, file: &RelativePath) {
        let reloaded = Document::load(&document.save());
        assert_eq!(
            document.current_file_content(file),
            reloaded.current_file_content(file)
        );
    }

    fn from_hex(hex: &str) -> Vec<u8> {
        (0..hex.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).unwrap())
            .collect()
    }

    /// Two peers delete and recreate the same file concurrently. A third peer that first learned
    /// of one new file receives the other's: Automerge reports the text of the object that lost
    /// the conflict, which is not visible. Applying it made the cache differ from the CRDT, so
    /// the daemon wrote the wrong text to disk and sent it to editors. The document and the sync
    /// message are recorded from a failing randomized run, because the conflict winner depends on
    /// the order of random actor ids.
    #[test]
    fn text_of_a_losing_concurrent_object_does_not_leak_into_cache() {
        let file = RelativePath::new("a");
        let before = from_hex(&[
            "856f4a83b8a93fce00c40304105a5c84bfe7686d4a70fb453f52c8d00710786b682fd7094c2084883c7c987890b61090",
            "6db396d90f5b03d8c442f10994899c10d3650676b65f9ed8754664fb8784d276021d57196e7727e3089b4ea6556c3664",
            "6ee26f7d583d56aa00cf20e8bfc6f68ae3e57393e18e213e64f5c212d1934b03ee7bc1b91cf7642313c7be96f81a2c7e",
            "ea0701080307130723024004430656020e01080208110a130b1525210a230b340242085609573280010b81011d83011d",
            "7f01020202007f037a0100017f017f7a02100f7f010206007f0005017b000100020106070002030110027f0300020301",
            "10047f2200067f0200010d02000100057c002060050c017f6f7d0566696c657306737461746573112e7465616d747970",
            "652f686973746f72790201610011020102027f0310027f0304017c1e7e01640d017f11051102007f010204110102007f",
            "970402001116ff31316564643164663434336334623333313566363861616364313635353935660a0a6f6e650a74776f",
            "0a74687265650a7803007f0103000d027e01000200660200020002000200020002000200020002000200020002000200",
            "64217200010001000100010001000100010001000100010001000100010205",
        ].concat());
        let message = from_hex(&[
            "43031d57196e7727e3089b4ea6556c36646ee26f7d583d56aa00cf20e8bfc6f68ae36582a9b6ced62794e688846c04f5",
            "1f4a779279daa5273c0f6f399e1642b50144ad24f4e6ac98a5dd282adb2e20060c9b7cea1eef2cb197212f5375551c96",
            "fd2d0001011d57196e7727e3089b4ea6556c36646ee26f7d583d56aa00cf20e8bfc6f68ae30a050a0716a26b004dd66a",
            "018404856f4a83dcbc7f3500f90304105a5c84bfe7686d4a70fb453f52c8d00710786b682fd7094c2084883c7c987890",
            "b610906db396d90f5b03d8c442f10994899c10d3650676b65f9ed8754664fb8784d276031d57196e7727e3089b4ea655",
            "6c36646ee26f7d583d56aa00cf20e8bfc6f68ae36582a9b6ced62794e688846c04f51f4a779279daa5273c0f6f399e16",
            "42b50144ad24f4e6ac98a5dd282adb2e20060c9b7cea1eef2cb197212f5375551c96fd2d070109030a13092302400443",
            "0856020e01090208110a130c1525210c230d340242085609573380010e81011e83011e7e010203007f0202037f010200",
            "0201027f7f017802100e01027e020108007f0007017f0003017d7e020308070002040110027e00030002040110040222",
            "00077f0200010d02000200067c002060050c017e6f007d0566696c657306737461746573112e7465616d747970652f68",
            "6973746f72790301610012020102027e000310027e000304017b1e007e01640d017e1100061202007f01030412010200",
            "7f970403001216ff31316564643164663434336334623333313566363861616364313635353935660a0a6f6e650a7477",
            "6f0a74687265650a787803007d01000102000d027f010200630003000200020002000200020002000200020002000200",
            "0200020002006321036f0001000100010001000100010001000100010001000100010001050704020284",
        ].concat());
        let mut observer = Document::load(&before);
        assert_cache_matches_crdt(&mut observer, &file);
        let message = AutomergeSyncMessage::decode(&message).unwrap();
        let _ = observer.receive_sync_message_log_patches(message, &mut AutomergeSyncState::new());
        assert_cache_matches_crdt(&mut observer, &file);
    }

    #[test]
    fn fuzz_cache_stays_in_step_with_crdt() {
        use rand::{RngExt, SeedableRng, rngs::StdRng};
        let file = RelativePath::new("file");
        for seed in 0..500u64 {
            let mut rng = StdRng::seed_from_u64(seed);
            let mut docs: Vec<Document> =
                std::iter::repeat_with(Document::default).take(3).collect();
            let mut states = vec![vec![AutomergeSyncState::new(); 3]; 3];
            let mut wire: Vec<Vec<Vec<AutomergeSyncMessage>>> = vec![vec![vec![]; 3]; 3];
            let mut log = vec![];
            for _ in 0..25 {
                let p = rng.random_range(0..3);
                let q = rng.random_range(0..3);
                match rng.random_range(0..7) {
                    6 => {
                        if let Some(Content::String(t)) = docs[p].current_file_content(&file) {
                            let at = rng.random_range(0..=t.chars().count());
                            let mut d = TextDelta::default();
                            d.retain(at);
                            d.insert("z");
                            log.push(format!("{p}: insert z at {at}"));
                            docs[p].apply_delta_to_doc(&d, &file).unwrap();
                        }
                    }
                    0 => {
                        let t = ["", "x", "xx", "y"][rng.random_range(0..4)];
                        log.push(format!("{p}: update_text {t:?}"));
                        let _ = docs[p].update_text(t, &file);
                    }
                    1 => {
                        log.push(format!("{p}: remove"));
                        docs[p].remove_file(&file);
                    }
                    2 => {
                        let t = ["", "x", "xx", "y"][rng.random_range(0..4)];
                        log.push(format!("{p}: set_file {t:?}"));
                        docs[p].set_file(Content::String(t.into()), &file);
                    }
                    3 if p != q => {
                        if let Some(m) = docs[p].generate_sync_message(&mut states[p][q]) {
                            wire[p][q].push(m);
                        }
                    }
                    _ if p != q && !wire[p][q].is_empty() => {
                        let m = wire[p][q].remove(0);
                        log.push(format!("{q}: receive from {p}"));
                        let patches =
                            docs[q].receive_sync_message_log_patches(m, &mut states[q][p]);
                        if PatchEffect::from_crdt_patches(&patches)
                            .iter()
                            .any(|e| matches!(e, PatchEffect::FileRemoval(_)))
                            && !docs[q].file_exists(&file)
                            && rng.random_bool(0.5)
                        {
                            log.push(format!("{q}: bring back empty"));
                            docs[q].update_text("", &file);
                        }
                        let reloaded = Document::load(&docs[q].save());
                        assert_eq!(
                            docs[q].current_file_content(&file),
                            reloaded.current_file_content(&file),
                            "seed {seed}: {log:#?}"
                        );
                    }
                    _ => {}
                }
            }
        }
    }

    /// Delivery order and batching must not matter: the same set of changes, applied as one
    /// batch, one by one in a random order (Automerge queues changes whose dependencies are
    /// missing), or in random-sized batches, gives the same heads and the same file content,
    /// and the incrementally maintained cache equals what a reload reads from the CRDT.
    /// This exercises Automerge's convergence, which the verification track
    /// (`teamtype_probe/automerge`) models only abstractly.
    #[test]
    fn fuzz_batching_and_order_do_not_change_result() {
        use rand::{RngExt, SeedableRng, rngs::StdRng, seq::SliceRandom};
        let files = [RelativePath::new("a"), RelativePath::new("b")];
        for seed in 0..300u64 {
            let mut rng = StdRng::seed_from_u64(seed);
            let mut docs: Vec<Document> =
                std::iter::repeat_with(Document::default).take(3).collect();
            for _ in 0..30 {
                let p = rng.random_range(0..3);
                let file = &files[rng.random_range(0..2)];
                let text = ["", "left", "xx", "right"][rng.random_range(0..4)];
                match rng.random_range(0..6) {
                    0 => docs[p].remove_file(file),
                    1 => docs[p].set_file(Content::String(text.into()), file),
                    2 => {
                        let q = rng.random_range(0..3);
                        if p != q {
                            let (mut left, mut right) = (
                                Document::load(&docs[q].save()),
                                Document::load(&docs[p].save()),
                            );
                            let _ = sync(&mut left, &mut right);
                            docs[p] = right;
                            docs[q] = left;
                        }
                    }
                    _ => {
                        let _ = docs[p].update_text(text, file);
                    }
                }
            }
            let mut all = Document::default();
            for d in &mut docs {
                let _ = sync(d, &mut all);
            }
            let changes: Vec<_> = all.doc.get_changes(&[]).into_iter().collect();
            let reference_heads = all.get_heads();
            let mut variants: Vec<Document> = vec![];
            // One batch.
            let mut batch = Document::default();
            batch.doc.apply_changes(changes.clone()).unwrap();
            variants.push(batch);
            // One by one, shuffled.
            let mut shuffled = Document::default();
            let mut order = changes.clone();
            order.shuffle(&mut rng);
            for c in order {
                shuffled.doc.apply_changes(vec![c]).unwrap();
            }
            variants.push(shuffled);
            // Random-sized batches of a shuffled order.
            let mut chunked = Document::default();
            let mut order = changes.clone();
            order.shuffle(&mut rng);
            while !order.is_empty() {
                let n = rng.random_range(1..=order.len());
                let rest = order.split_off(n);
                chunked
                    .doc
                    .apply_changes(std::mem::replace(&mut order, rest))
                    .unwrap();
            }
            variants.push(chunked);
            for (i, v) in variants.iter_mut().enumerate() {
                assert_eq!(v.get_heads(), reference_heads, "seed {seed} variant {i}");
                let reloaded = Document::load(&v.save());
                let want = Document::load(&all.save());
                for f in &files {
                    assert_eq!(
                        reloaded.current_file_content(f),
                        want.current_file_content(f),
                        "seed {seed} variant {i} file {f}"
                    );
                }
            }
        }
    }

    /// Three peers edit and exchange sync messages that stay in flight for a while. After the
    /// network drains and every pair syncs to quiescence, all peers hold the same heads and the
    /// same file content, and each peer's cache equals what a reload reads from its CRDT.
    #[test]
    fn fuzz_peers_converge_with_messages_in_flight() {
        use rand::{RngExt, SeedableRng, rngs::StdRng};
        let files = [RelativePath::new("a"), RelativePath::new("b")];
        for seed in 0..300u64 {
            let mut rng = StdRng::seed_from_u64(seed);
            let mut docs: Vec<Document> =
                std::iter::repeat_with(Document::default).take(3).collect();
            let mut states = vec![vec![AutomergeSyncState::new(); 3]; 3];
            let mut wire: Vec<Vec<Vec<AutomergeSyncMessage>>> = vec![vec![vec![]; 3]; 3];
            for _ in 0..40 {
                let (from, to) = (rng.random_range(0..3), rng.random_range(0..3));
                let file = &files[rng.random_range(0..2)];
                let text = ["", "x", "xx", "y"][rng.random_range(0..4)];
                match rng.random_range(0..7) {
                    0 => docs[from].remove_file(file),
                    1 => docs[from].set_file(Content::String(text.into()), file),
                    2 => {
                        let _ = docs[from].update_text(text, file);
                    }
                    3 if from != to => {
                        if let Some(m) = docs[from].generate_sync_message(&mut states[from][to]) {
                            wire[from][to].push(m);
                        }
                    }
                    _ if from != to && !wire[from][to].is_empty() => {
                        let m = wire[from][to].remove(0);
                        let _ = docs[to].receive_sync_message_log_patches(m, &mut states[to][from]);
                    }
                    _ => {}
                }
            }
            // Drain what is in flight, then sync every pair repeatedly until nothing changes.
            for from in 0..3 {
                for to in 0..3 {
                    for m in std::mem::take(&mut wire[from][to]) {
                        let _ = docs[to].receive_sync_message_log_patches(m, &mut states[to][from]);
                    }
                }
            }
            for _ in 0..3 {
                for i in 0..3 {
                    for j in 0..3 {
                        if i != j {
                            let (low, high) = (i.min(j), i.max(j));
                            let (left, right) = docs.split_at_mut(high);
                            let _ = sync(&mut left[low], &mut right[0]);
                        }
                    }
                }
            }
            let heads: Vec<_> = docs.iter_mut().map(Document::get_heads).collect();
            assert_eq!(heads[0], heads[1], "seed {seed}");
            assert_eq!(heads[1], heads[2], "seed {seed}");
            for file in &files {
                let want = Document::load(&docs[0].save());
                for (n, doc) in docs.iter_mut().enumerate() {
                    assert_eq!(
                        doc.current_file_content(file),
                        want.current_file_content(file),
                        "seed {seed} peer {n} file {file}"
                    );
                    assert_cache_matches_crdt(doc, file);
                }
            }
        }
    }

    /// This set of tests has some documentation character to show to ourselves,
    /// what happens under the hood when sync'ing.
    mod automerge_interna {
        use super::*;

        #[test]
        fn test_generate_sync_message() {
            let mut document = Document::default();
            let mut state = AutomergeSyncState::new();
            assert!(document.generate_sync_message(&mut state).is_some());
            // Stops for now and waits for a response
            assert!(document.generate_sync_message(&mut state).is_none());

            document.set_file(Content::String(String::new()), &RelativePath::new("text"));
            // We have progressed our state, so update all peers about that.
            assert!(document.generate_sync_message(&mut state).is_some());
            // Again, stop, until peers tell us if they want more information.
            assert!(document.generate_sync_message(&mut state).is_none());
        }
    }

    #[test]
    fn torn_persisted_document_loads_its_intact_prefix() {
        let mut d = Document::default();
        d.set_file(Content::String("hello".into()), &RelativePath::new("a"));
        let mut bytes = d.save();
        d.set_file(Content::String("world".into()), &RelativePath::new("b"));
        bytes.extend(d.save_incremental());
        // A crash while appending leaves any prefix of the second chunk.
        for cut in 1..bytes.len() {
            let _ = Document::try_load(&bytes[..cut]);
        }
        let torn = Document::try_load(&bytes[..bytes.len() - 3]).expect("prefix loads");
        assert_eq!(
            torn.current_file_content(&RelativePath::new("a")),
            Some(&Content::String("hello".into()))
        );
        assert!(Document::try_load(b"garbage").is_err());
    }
}
