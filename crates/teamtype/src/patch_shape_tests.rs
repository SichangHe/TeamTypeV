// SPDX-FileCopyrightText: 2026 TeamType contributors
//
// SPDX-License-Identifier: AGPL-3.0-or-later

// Executable check, on real Automerge, of the assumption of the Verus proof
// `teamtype_probe/drain_fable_tt/replace-proof`: the patches `Document::receive_sync_message_log_patches`
// returns, read by their path-based meaning (types.rs shapes only; PutMap(Text) makes a fresh empty
// text, SpliceText/DeleteSeq edit the text at the path, DeleteMap removes, PutMap(Bytes) sets bytes),
// replay the visible files before the message into the visible files after it. Messages come from
// randomized runs with concurrent replacements, deletions, byte files and batching, so one message
// often replaces a path several times.

use std::collections::HashMap;

use automerge::{
    ObjType, Patch, PatchAction, Prop, ScalarValue, Value,
    sync::{Message as AutomergeSyncMessage, State as AutomergeSyncState},
};
use rand::{RngExt, SeedableRng, rngs::StdRng};

use crate::{
    document::{Content, Document},
    path::RelativePath,
};

type Files = HashMap<String, Content>;

fn snapshot(doc: &Document, names: &[&str]) -> Files {
    names
        .iter()
        .filter_map(|n| {
            doc.current_file_content(&RelativePath::new(n))
                .map(|c| ((*n).to_string(), c.clone()))
        })
        .collect()
}

fn key_of(patch: &Patch) -> String {
    match &patch.path[..] {
        [_, (_, Prop::Map(key))] => key.clone(),
        other => panic!("path outside the grammar: {other:?}"),
    }
}

/// The path-based meaning that the proof (`sem`) gives to each patch shape. Panics on a shape or
/// a replay step the proof's assumption excludes.
fn replay(mut files: Files, patches: &[Patch]) -> Files {
    for patch in patches {
        match (patch.path.len(), &patch.action) {
            (0, PatchAction::PutMap { key, .. }) if key == "files" => {}
            (1, PatchAction::PutMap { key, value, .. }) => match value {
                (Value::Object(ObjType::Text), _) => {
                    files.insert(key.clone(), Content::String(String::new()));
                }
                (Value::Scalar(s), _) => match s.as_ref() {
                    ScalarValue::Bytes(b) => {
                        files.insert(key.clone(), Content::Bytes(b.clone()));
                    }
                    other => panic!("scalar outside the grammar: {other:?}"),
                },
                other => panic!("PutMap value outside the grammar: {other:?}"),
            },
            (1, PatchAction::DeleteMap { key }) => {
                files.remove(key);
            }
            (1, PatchAction::Conflict { prop: Prop::Map(_) }) => {}
            (2, PatchAction::SpliceText { index, value, .. }) => {
                let Some(Content::String(text)) = files.get_mut(&key_of(patch)) else {
                    panic!("SpliceText at a path without text: {patch:?}");
                };
                let at = text
                    .char_indices()
                    .nth(*index)
                    .map_or(text.len(), |(b, _)| b);
                assert!(
                    *index <= text.chars().count(),
                    "splice out of range: {patch:?}"
                );
                text.insert_str(at, &value.make_string());
            }
            (2, PatchAction::DeleteSeq { index, length }) => {
                let Some(Content::String(text)) = files.get_mut(&key_of(patch)) else {
                    panic!("DeleteSeq at a path without text: {patch:?}");
                };
                let mut chars: Vec<char> = text.chars().collect();
                assert!(
                    index + length <= chars.len(),
                    "delete out of range: {patch:?}"
                );
                chars.drain(*index..index + length);
                *text = chars.into_iter().collect();
            }
            other => panic!("patch shape outside the grammar: {other:?}"),
        }
    }
    files
}

#[test]
fn emitted_patches_replay_to_the_new_state() {
    let names = ["a", "b"];
    let mut multi_replacement_messages = 0;
    let mut conflict_puts = 0;
    let mut messages = 0;
    for seed in 0..600u64 {
        let mut rng = StdRng::seed_from_u64(seed);
        let mut docs: Vec<Document> = std::iter::repeat_with(Document::default).take(3).collect();
        let mut states = vec![vec![AutomergeSyncState::new(); 3]; 3];
        let mut wire: Vec<Vec<Vec<AutomergeSyncMessage>>> = vec![vec![vec![]; 3]; 3];
        for _ in 0..90 {
            let p = rng.random_range(0..3);
            let q = rng.random_range(0..3);
            let file = RelativePath::new(names[rng.random_range(0..2)]);
            let text = ["", "x", "xx", "yz", "left", "right"][rng.random_range(0..6)];
            match rng.random_range(0..16) {
                0..=2 => docs[p].set_file(Content::String(text.into()), &file),
                3 => docs[p].set_file(Content::Bytes(text.as_bytes().to_vec()), &file),
                4 => docs[p].remove_file(&file),
                5 | 6 => {
                    let _ = docs[p].update_text(text, &file);
                }
                7..=9 if p != q => {
                    if let Some(m) = docs[p].generate_sync_message(&mut states[p][q]) {
                        wire[p][q].push(m);
                    }
                }
                _ if p != q && !wire[p][q].is_empty() => {
                    let m = wire[p][q].remove(0);
                    let before = snapshot(&docs[q], &names);
                    let patches = docs[q].receive_sync_message_log_patches(m, &mut states[q][p]);
                    let after = snapshot(&Document::load(&docs[q].save()), &names);
                    let replayed = replay(before, &patches);
                    assert_eq!(replayed, after, "seed {seed}: patches {patches:#?}");
                    messages += 1;
                    let mut puts: HashMap<&str, usize> = HashMap::new();
                    for patch in &patches {
                        if let PatchAction::PutMap {
                            key,
                            value: (Value::Object(ObjType::Text), _),
                            conflict,
                        } = &patch.action
                        {
                            *puts.entry(key).or_default() += 1;
                            conflict_puts += usize::from(*conflict);
                        }
                    }
                    multi_replacement_messages += usize::from(puts.values().any(|n| *n >= 2));
                }
                _ => {}
            }
        }
    }
    eprintln!(
        "messages {messages}, with two or more text PutMaps of one path {multi_replacement_messages}, text PutMaps with conflict flag {conflict_puts}"
    );
    assert!(messages > 1000, "too few messages to mean anything");
    assert!(
        conflict_puts > 0,
        "no conflicting replacement was exercised"
    );
}

/// The recorded case where Automerge reports `Conflict` plus the new object's text for a switched
/// visible text object (see `document.rs` `text_of_a_losing_concurrent_object_does_not_leak_into_cache`).
/// Without `replaced_text_objects_as_puts` the replay of the patches is wrong; with it, right.
#[test]
fn recorded_conflict_flip_replays_to_the_new_state() {
    fn from_hex(hex: &str) -> Vec<u8> {
        (0..hex.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).expect("hex"))
            .collect()
    }
    let names = ["a"];
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
    let mut doc = Document::load(&before);
    let before = snapshot(&doc, &names);
    let message = AutomergeSyncMessage::decode(&message).expect("recorded message");
    let patches = doc.receive_sync_message_log_patches(message, &mut AutomergeSyncState::new());
    let after = snapshot(&Document::load(&doc.save()), &names);
    assert_eq!(replay(before, &patches), after, "patches {patches:#?}");
}
