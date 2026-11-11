// SPDX-License-Identifier: AGPL-3.0-or-later

// Checks, on the real Automerge sync state machine as `peer/sync.rs` drives it, the assumptions of
// the liveness proof (`teamtype_probe/liveness_proof`): peers connected by reliable FIFO streams
// whose connections may drop (dropping the messages in flight and resetting both ends' sync state),
// editing at random and generating a message after every change, converge once edits and drops
// stop, within a bounded number of messages. `RECONNECT_KEEPS_STATE=1` (negative control) keeps the
// old sync state across a drop, which the real code never does; the test then fails (stalls).

use std::collections::VecDeque;

use automerge::sync::State as SyncState;
use rand::{RngExt, SeedableRng, rngs::StdRng};

use crate::document::{Content, Document};
use crate::path::RelativePath;

struct Edge {
    from: usize,
    to: usize,
    state: SyncState,
    queue: VecDeque<Vec<u8>>,
}

struct Net {
    docs: Vec<Document>,
    /// Edges come in pairs (2k, 2k + 1) = one connection.
    edges: Vec<Edge>,
    sent: usize,
}

impl Net {
    fn new(peers: usize, links: &[(usize, usize)]) -> Self {
        let mut edges = vec![];
        for &(a, b) in links {
            for (from, to) in [(a, b), (b, a)] {
                edges.push(Edge {
                    from,
                    to,
                    state: SyncState::new(),
                    queue: VecDeque::new(),
                });
            }
        }
        let mut net = Self {
            docs: std::iter::repeat_with(Document::default)
                .take(peers)
                .collect(),
            edges,
            sent: 0,
        };
        net.generate_all();
        net
    }

    /// `SyncActor::generate_sync_message` on one edge (run on every document change ping).
    fn generate(&mut self, e: usize) {
        let from = self.edges[e].from;
        let mut state = std::mem::take(&mut self.edges[e].state);
        let message = self.docs[from].generate_sync_message(&mut state);
        self.edges[e].state = state;
        if let Some(message) = message {
            self.edges[e].queue.push_back(message.encode());
            self.sent += 1;
        }
    }

    fn generate_all(&mut self) {
        for e in 0..self.edges.len() {
            self.generate(e);
        }
    }

    fn generate_from(&mut self, peer: usize) {
        for e in 0..self.edges.len() {
            if self.edges[e].from == peer {
                self.generate(e);
            }
        }
    }

    /// Delivers the oldest message on edge `e`; the receiver then generates on all its edges.
    fn deliver(&mut self, e: usize) {
        let Some(bytes) = self.edges[e].queue.pop_front() else {
            return;
        };
        let to = self.edges[e].to;
        let message = automerge::sync::Message::decode(&bytes).expect("decode");
        // the receiver's sync state about this peer is the one its own (reverse) edge generates with
        let reverse = e ^ 1;
        let mut state = std::mem::take(&mut self.edges[reverse].state);
        let _ = self.docs[to].receive_sync_message_log_patches(message, &mut state);
        self.edges[reverse].state = state;
        self.generate_from(to);
    }

    /// The connection (edges 2k and 2k + 1) drops and is re-established: in-flight messages are
    /// lost, both ends start a fresh sync state, and both generate their first message.
    fn reconnect(&mut self, pair: usize) {
        for e in [2 * pair, 2 * pair + 1] {
            self.edges[e].queue.clear();
            if std::env::var("RECONNECT_KEEPS_STATE").is_err() {
                self.edges[e].state = SyncState::new();
            }
        }
        self.generate(2 * pair);
        self.generate(2 * pair + 1);
    }

    fn edit(&mut self, rng: &mut StdRng, peer: usize) {
        let path = RelativePath::new(["a", "b"][rng.random_range(0..2usize)]);
        let old = match self.docs[peer].current_file_content(&path) {
            Some(Content::String(text)) => text.clone(),
            _ => String::new(),
        };
        let mut chars: Vec<char> = old.chars().collect();
        let at = rng.random_range(0..=chars.len());
        if !chars.is_empty() && rng.random_range(0..3) == 0 {
            chars.remove(at.min(chars.len() - 1));
        } else {
            chars.insert(at, char::from(b'a' + rng.random_range(0..26u8)));
        }
        let new: String = chars.into_iter().collect();
        self.docs[peer].update_text(&new, &path);
        self.generate_from(peer);
    }

    fn in_flight(&self) -> bool {
        self.edges.iter().any(|edge| !edge.queue.is_empty())
    }

    fn texts(&self, peer: usize) -> Vec<Option<Content>> {
        ["a", "b"]
            .iter()
            .map(|name| {
                self.docs[peer]
                    .current_file_content(&RelativePath::new(name))
                    .cloned()
            })
            .collect()
    }
}

fn run(seed: u64) -> usize {
    let mut rng = StdRng::seed_from_u64(seed);
    let peers = rng.random_range(2..=4usize);
    // a random tree (connected), plus sometimes an extra link
    let mut links: Vec<(usize, usize)> = (1..peers).map(|p| (rng.random_range(0..p), p)).collect();
    if peers > 2 && rng.random_range(0..2) == 0 {
        links.push((0, peers - 1));
        links.dedup();
    }
    let mut net = Net::new(peers, &links);
    for _ in 0..rng.random_range(20..120) {
        match rng.random_range(0..10) {
            0..=2 => {
                let peer = rng.random_range(0..peers);
                net.edit(&mut rng, peer);
            }
            3 if std::env::var("NO_DROPS").is_err() => {
                net.reconnect(rng.random_range(0..links.len()));
            }
            3 => {}
            _ => {
                let e = rng.random_range(0..net.edges.len());
                net.deliver(e);
            }
        }
    }
    // edits and drops stop; messages keep being delivered
    let before = net.sent;
    let mut steps = 0;
    while net.in_flight() {
        let e = rng.random_range(0..net.edges.len());
        net.deliver(e);
        steps += 1;
        assert!(
            steps < 20_000,
            "seed {seed}: no quiescence after {steps} deliveries"
        );
    }
    // the real daemon only generates on a document change ping, so generating again here is extra:
    // count how often it still yields something at quiescence
    let mut extra = 0;
    for e in 0..net.edges.len() {
        net.generate(e);
    }
    while net.in_flight() {
        extra += 1;
        let e = rng.random_range(0..net.edges.len());
        net.deliver(e);
        assert!(extra < 20_000, "seed {seed}: extra generates never settle");
    }
    if extra > 0 && std::env::var("DEBUG").is_ok() {
        eprintln!("seed {seed}: {extra} extra deliveries after quiescence");
    }
    if std::env::var("DEBUG").is_ok() {
        eprintln!("seed {seed} peers {peers} links {links:?}");
        for p in 0..peers {
            eprintln!(
                "peer {p} heads {:?} texts {:?}",
                net.docs[p].get_heads(),
                net.texts(p)
            );
        }
        for (i, edge) in net.edges.iter().enumerate() {
            eprintln!("edge {i} {}->{} state {:?}", edge.from, edge.to, edge.state);
        }
    }
    for p in 1..peers {
        assert_eq!(
            net.docs[0].get_heads(),
            net.docs[p].get_heads(),
            "seed {seed}: heads differ"
        );
        assert_eq!(
            net.texts(0),
            net.texts(p),
            "seed {seed}: peers 0 and {p} differ"
        );
    }
    net.sent - before
}

#[test]
fn real_sync_converges_after_edits_and_connection_drops_stop() {
    let seeds: u64 = std::env::var("SYNC_SEEDS")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(300);
    for seed in 0..seeds {
        run(seed);
    }
}
