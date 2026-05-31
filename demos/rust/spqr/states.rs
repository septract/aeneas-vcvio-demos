//! SPQR typestate — the SCKA construction's transition structure (the protocol's
//! *state machine*), as an Aeneas-extractable control-flow skeleton.
//!
//! This mirrors `src/v1/chunked/states.rs` @`f2589fe` — the 11-state `States` enum
//! and its `send`/`recv` transitions — which is the **construction whose security the
//! SCKA game is about**: the security property (forward secrecy + post-compromise
//! "healing") is a game over *this* state sequence, asking which epoch keys stay
//! pseudorandom given an adversarial schedule of sends/recvs/compromises. The two
//! security-critical artifacts the game binds to are here verbatim:
//!   - **when an `output_key` (epoch secret) is established** — the `bool` returned by
//!     `send_step`/`recv_step` (the CT-sender derives it at `HeaderReceived → Ct1Sampled`;
//!     the EK-sender at `EkSentCt1Received → NoHeaderReceived`), and
//!   - **`vulnerable_epoch`** — which epoch (if any) is exposed in each state, the
//!     leakage predicate the post-compromise argument tracks (`#[cfg(test)]` upstream as
//!     `SckaVulnerability::vulnerable_epochs`; it is the *specification* of compromise,
//!     not production control flow).
//!
//! ## Why a skeleton, and what the boundaries are
//!
//! The upstream state machine is built pervasively on constructs outside the Aeneas
//! fragment — every state struct embeds a stateful `PolyEncoder`/`PolyDecoder`
//! (`Vec`/`SortedSet`/protobuf), and the transitions use `R: Rng` generics, `Result`,
//! `Box`, `Vec::split_off`, and the `Encoder`/`Decoder` traits. None of that extracts.
//! So this node captures the transition **structure** — the state graph, message-payload
//! emission, output-key timing, epoch advance, and vulnerability predicate — with the
//! cryptographic operations as **typed boundaries**:
//!   - the per-chunk codec decode outcome is the input `Decode` (StillReceiving / … / Done);
//!     the codec itself is the separately-extracted RS decoder (`spqr/gf.rs`,
//!     `lagrange_interpolate`/`compute_at`/`decode_value_at`);
//!   - the symmetric output-key derivation is the separately-extracted chain step
//!     (`crypto/sha256.rs`, `spqr_chain_next`);
//!   - the MAC is the separately-extracted authenticator (`spqr/authenticator.rs`);
//!   - **ML-KEM-768** (encaps/decaps, sizes below) is the assumed **IND-CCA floor** — it is
//!     introduced on the proof side as a VCVio `KeyEncapMech`, not extracted here.
//! (Each `demos/rust/*.rs` extracts as a standalone crate, so those verified primitives
//! cannot be *called* across crates regardless; they bind to the game by signature.)
//!
//! Divergence class for this node: **structure-faithful** — the transition graph,
//! payload/key timing, and `vulnerable_epoch` are reproduced exactly; the crypto payloads
//! carried by each state are abstracted to the boundaries above (so NOT the per-byte
//! `[type-only]` identity the primitive nodes carry). XREF tags mark each correspondence.

// ML-KEM-768 message sizes (SPQR `incremental_mlkem768`), for reference — the assumed
// IND-CCA floor's public-key / ciphertext / shared-secret widths the codec transports.
// NB these are the INCREMENTAL split: the encapsulation key is pk1 (= HEADER_SIZE = 64) ‖ pk2,
// with pk2 = 1152 (`pk2_len()`, F* model `res = 1152`; `ek.len() == 1152` throughout send_ek/
// send_ct) — NOT the monolithic 1184-byte ML-KEM-768 ek (= 1152 + 32-byte seed).
pub const ENCAPSULATION_KEY_SIZE: usize = 1152;
pub const CIPHERTEXT1_SIZE: usize = 960;
pub const CIPHERTEXT2_SIZE: usize = 128;
pub const SHARED_SECRET_SIZE: usize = 32;

/// The 11 protocol states. The first five are the EK-sender's (`send_ek`), the last six
/// the CT-sender's (`send_ct`). XREF: spqr states.rs:16-29 @f2589fe (`enum States`)
/// [structure-faithful: the inner per-state structs' crypto fields are abstracted].
#[derive(Clone, Copy)]
pub enum StateKind {
    KeysUnsampled,
    KeysSampled,
    HeaderSent,
    Ct1Received,
    EkSentCt1Received,
    NoHeaderReceived,
    HeaderReceived,
    Ct1Sampled,
    EkReceivedCt1Sampled,
    Ct1Acknowledged,
    Ct2Sampled,
}

/// A protocol state: which variant, plus the current epoch (`state.epoch()` upstream).
#[derive(Clone, Copy)]
pub struct State {
    pub kind: StateKind,
    pub epoch: u64,
}

/// The kind of message a transition emits / receives. XREF: spqr states.rs:31-39 @f2589fe
/// (`enum MessagePayload`) [structure-faithful: the `Chunk` payloads are abstracted].
#[derive(Clone, Copy)]
pub enum PayloadKind {
    NoneP,
    Hdr,
    Ek,
    EkCt1Ack,
    Ct1Ack(bool),
    Ct1,
    Ct2,
}

/// The per-chunk decode outcome — the typed boundary to the RS decoder: did adding this chunk
/// complete the decode (`receiving.decoded_message()` returned `Some`) or not? This is exactly
/// what the codec reports; it carries NO `ct1_ack` information (that bit is derived from the
/// payload tag, mirroring the upstream dispatcher, and combined with this in `Ct1Sampled` — see
/// `recv_ek_dispatch`). So the transition graph is faithfully constrained: a non-ack payload
/// can never reach an ack-only successor.
/// XREF: spqr send_ek.rs / send_ct.rs `*RecvChunk` @f2589fe — the 2-way `decoded_message()`
/// `Some`/`None`; the `Ct1Sampled` 4-way `Ct1SampledRecvChunk` is the genuine product
/// `(decode-done × ct1_ack)`, reconstructed here from this `Decode` × the payload-derived ack.
/// [boundary: the decoder is `spqr/gf.rs`].
#[derive(Clone, Copy)]
pub enum Decode {
    StillReceiving,
    Done,
}

/// Initialise party A (the EK sender). XREF: spqr states.rs:58-60 @f2589fe (`init_a`).
pub fn init_a() -> State {
    State {
        kind: StateKind::KeysUnsampled,
        epoch: 0,
    }
}

/// Initialise party B (the CT sender). XREF: spqr states.rs:62-64 @f2589fe (`init_b`).
pub fn init_b() -> State {
    State {
        kind: StateKind::NoHeaderReceived,
        epoch: 0,
    }
}

/// The send transition: returns the next state, the emitted message-payload kind, and
/// whether an `output_key` (epoch secret) is established by this step. The graph is
/// deterministic in the state; randomness only feeds the abstracted crypto payload.
///
/// XREF: spqr states.rs:115-273 @f2589fe (`States::send`) [structure-faithful: each `match`
/// arm's next-state + `MessagePayload` + `key: Some/None` reproduced; the `key: Some` at
/// `HeaderReceived → Ct1Sampled` is the CT-sender's epoch-secret derivation].
pub fn send_step(s: State) -> (State, PayloadKind, bool) {
    let ep = s.epoch;
    match s.kind {
        StateKind::KeysUnsampled => (
            State { kind: StateKind::KeysSampled, epoch: ep },
            PayloadKind::Hdr,
            false,
        ),
        StateKind::KeysSampled => (
            State { kind: StateKind::KeysSampled, epoch: ep },
            PayloadKind::Hdr,
            false,
        ),
        StateKind::HeaderSent => (
            State { kind: StateKind::HeaderSent, epoch: ep },
            PayloadKind::Ek,
            false,
        ),
        StateKind::Ct1Received => (
            State { kind: StateKind::Ct1Received, epoch: ep },
            PayloadKind::EkCt1Ack,
            false,
        ),
        StateKind::EkSentCt1Received => (
            State { kind: StateKind::EkSentCt1Received, epoch: ep },
            PayloadKind::Ct1Ack(true),
            false,
        ),
        StateKind::NoHeaderReceived => (
            State { kind: StateKind::NoHeaderReceived, epoch: ep },
            PayloadKind::NoneP,
            false,
        ),
        StateKind::HeaderReceived => (
            State { kind: StateKind::Ct1Sampled, epoch: ep },
            PayloadKind::Ct1,
            true, // the CT-sender derives the epoch secret here
        ),
        StateKind::Ct1Sampled => (
            State { kind: StateKind::Ct1Sampled, epoch: ep },
            PayloadKind::Ct1,
            false,
        ),
        StateKind::EkReceivedCt1Sampled => (
            State { kind: StateKind::EkReceivedCt1Sampled, epoch: ep },
            PayloadKind::Ct1,
            false,
        ),
        StateKind::Ct1Acknowledged => (
            State { kind: StateKind::Ct1Acknowledged, epoch: ep },
            PayloadKind::NoneP,
            false,
        ),
        StateKind::Ct2Sampled => (
            State { kind: StateKind::Ct2Sampled, epoch: ep },
            PayloadKind::Ct2,
            false,
        ),
    }
}

/// The receive transition: given the current state, the message epoch and payload kind,
/// and the codec decode outcome `dec`, returns `Some((next_state, emits_output_key))`, or
/// `None` for the `Err` cases. Epochs only advance at `Ct2Sampled` on receiving epoch
/// `ep+1` (a new round); the EK-sender establishes its epoch secret at
/// `EkSentCt1Received → NoHeaderReceived`.
///
/// Error model: upstream `recv` returns `Err` from **two** sources, both represented as `None`
/// here — the `EpochOutOfRange` guard (the `Greater` arms), *and* the `?`-propagated
/// authentication/chain rejection inside the four `recv_*_chunk(...)?` arms
/// (`recv_ct2_chunk` `send_ek.rs:207`; `recv_hdr_chunk`/`recv_ek_chunk` `send_ct.rs:98,178,267`
/// — MAC mismatch, `KeyTrimmed`, `SendKeyEpochDecreased`). The latter is the typed boundary
/// `accept` (the verdict the MAC/chain check returns, e.g. `authenticator::compare = 0`).
/// Crucially, upstream's `?` lives INSIDE the `if let Some(decoded)` branch, so it fires only
/// when the decode COMPLETES: `accept` is consulted only when `dec = Done` (→ `None` on
/// `!accept`); while `dec = StillReceiving` the chunk is merely buffered and the state is
/// unchanged regardless of `accept`. This lets the SCKA game quantify over forged/replayed
/// ciphertexts being rejected, without admitting a reject the real protocol never produces.
///
/// XREF: spqr states.rs:275-532 @f2589fe (`States::recv`) [structure-faithful: the
/// `msg.epoch.cmp(&state.epoch())` three-way branch, payload match, and `*RecvChunk`
/// dispatch reproduced; `Err(EpochOutOfRange)` → `None` and the `?`-propagated auth/chain
/// `Err` → `None` gated by the `accept` boundary; `key = Some(sec)` at the EK-sender's
/// `Done` → `emits_output_key = true`].
pub fn recv_step(s: State, msg_epoch: u64, payload: PayloadKind, dec: Decode, accept: bool)
    -> Option<(State, bool)>
{
    let ep = s.epoch;
    match s.kind {
        // ── send_ek ──────────────────────────────────────────────────────────────
        StateKind::KeysUnsampled => {
            if msg_epoch > ep {
                None
            } else {
                Some((s, false))
            }
        }
        StateKind::KeysSampled => {
            if msg_epoch > ep {
                None
            } else if msg_epoch < ep {
                Some((s, false))
            } else {
                match payload {
                    PayloadKind::Ct1 => Some((State { kind: StateKind::HeaderSent, epoch: ep }, false)),
                    _ => Some((s, false)),
                }
            }
        }
        StateKind::HeaderSent => {
            if msg_epoch > ep {
                None
            } else if msg_epoch < ep {
                Some((s, false))
            } else {
                match payload {
                    PayloadKind::Ct1 => match dec {
                        Decode::Done => Some((State { kind: StateKind::Ct1Received, epoch: ep }, false)),
                        _ => Some((s, false)),
                    },
                    _ => Some((s, false)),
                }
            }
        }
        StateKind::Ct1Received => {
            if msg_epoch > ep {
                None
            } else if msg_epoch < ep {
                Some((s, false))
            } else {
                match payload {
                    PayloadKind::Ct2 => Some((State { kind: StateKind::EkSentCt1Received, epoch: ep }, false)),
                    _ => Some((s, false)),
                }
            }
        }
        StateKind::EkSentCt1Received => {
            if msg_epoch > ep {
                None
            } else if msg_epoch < ep {
                Some((s, false))
            } else {
                match payload {
                    PayloadKind::Ct2 => match dec {
                        // Decode complete ⇒ `recv_ct2(decoded)?` runs: rejects (None) on MAC/chain
                        // failure (`!accept`); on success the EK-sender establishes the epoch secret.
                        Decode::Done =>
                            if accept { Some((State { kind: StateKind::NoHeaderReceived, epoch: ep }, true)) }
                            else { None },
                        // Decode incomplete ⇒ no MAC check yet (the `?` is unreachable); stay.
                        Decode::StillReceiving => Some((s, false)),
                    },
                    _ => Some((s, false)),
                }
            }
        }
        // ── send_ct ──────────────────────────────────────────────────────────────
        StateKind::NoHeaderReceived => {
            if msg_epoch > ep {
                None
            } else if msg_epoch < ep {
                Some((s, false))
            } else {
                match payload {
                    PayloadKind::Hdr => match dec {
                        // Decode complete ⇒ `recv_hdr(decoded)?` runs: rejects (None) on `!accept`.
                        Decode::Done =>
                            if accept { Some((State { kind: StateKind::HeaderReceived, epoch: ep }, false)) }
                            else { None },
                        Decode::StillReceiving => Some((s, false)),
                    },
                    _ => Some((s, false)),
                }
            }
        }
        StateKind::HeaderReceived => {
            if msg_epoch > ep {
                None
            } else {
                Some((s, false))
            }
        }
        StateKind::Ct1Sampled => {
            if msg_epoch > ep {
                None
            } else if msg_epoch < ep {
                Some((s, false))
            } else {
                // `ct1_ack` is the payload-derived bit (Ek → false, EkCt1Ack → true), exactly as
                // the upstream dispatcher passes it to `recv_ek_chunk` (states.rs:418-422).
                match payload {
                    PayloadKind::Ek => recv_ek_dispatch(ep, dec, false, accept),
                    PayloadKind::EkCt1Ack => recv_ek_dispatch(ep, dec, true, accept),
                    _ => Some((s, false)),
                }
            }
        }
        StateKind::EkReceivedCt1Sampled => {
            if msg_epoch > ep {
                None
            } else if msg_epoch < ep {
                Some((s, false))
            } else {
                match payload {
                    PayloadKind::Ct1Ack(true) => Some((State { kind: StateKind::Ct2Sampled, epoch: ep }, false)),
                    PayloadKind::EkCt1Ack => Some((State { kind: StateKind::Ct2Sampled, epoch: ep }, false)),
                    _ => Some((s, false)),
                }
            }
        }
        StateKind::Ct1Acknowledged => {
            if msg_epoch > ep {
                None
            } else if msg_epoch < ep {
                Some((s, false))
            } else {
                match payload {
                    PayloadKind::Ek => recv_ack_dispatch(ep, dec, s, accept),
                    PayloadKind::EkCt1Ack => recv_ack_dispatch(ep, dec, s, accept),
                    _ => Some((s, false)),
                }
            }
        }
        StateKind::Ct2Sampled => {
            if msg_epoch > ep {
                // Only epoch `ep+1` is accepted — a new round; the epoch advances.
                if msg_epoch - ep == 1 {
                    Some((State { kind: StateKind::KeysUnsampled, epoch: msg_epoch }, false))
                } else {
                    None
                }
            } else {
                Some((s, false))
            }
        }
    }
}

/// `Ct1Sampled::recv_ek_chunk`'s outcome, as the genuine `(ek-decode-done × ct1_ack)` product —
/// the four `Ct1SampledRecvChunk` cases (send_ct.rs:176-198):
///   (decoded, ack)        → Done                       → `Ct2Sampled`
///   (decoded, !ack)       → StillSending               → `EkReceivedCt1Sampled`
///   (!decoded, ack)       → StillReceiving             → `Ct1Acknowledged`
///   (!decoded, !ack)      → StillReceivingStillSending → stay `Ct1Sampled`
/// Because `ct1_ack` is the payload-derived bit, a non-ack payload (`Ek`) can only reach the
/// `!ack` successors — `Ek`+decoded → `EkReceivedCt1Sampled`, never `Ct2Sampled`. The MAC/chain
/// `accept` verdict is consulted ONLY when decode completes (`Done`) — that's where upstream's
/// `recv_ek(decoded)?` runs; while still receiving, the `?` is unreachable, so `accept` is
/// irrelevant and the chunk is just buffered (stay / ack-advance).
fn recv_ek_dispatch(ep: u64, dec: Decode, ct1_ack: bool, accept: bool) -> Option<(State, bool)> {
    match dec {
        Decode::Done =>
            if accept {
                let kind = if ct1_ack { StateKind::Ct2Sampled } else { StateKind::EkReceivedCt1Sampled };
                Some((State { kind, epoch: ep }, false))
            } else {
                None
            },
        Decode::StillReceiving => {
            let kind = if ct1_ack { StateKind::Ct1Acknowledged } else { StateKind::Ct1Sampled };
            Some((State { kind, epoch: ep }, false))
        }
    }
}

/// `Ct1Acknowledged::recv_ek_chunk`'s outcome (ct1 already acked, so ek-decode-progress only).
/// `accept` is consulted only on `Done` (where `recv_ek(decoded)?` runs); while still receiving,
/// stay. XREF: spqr send_ct.rs:256-276 (`Ct1AcknowledgedRecvChunk`; `?` at :267 inside `if let Some`).
fn recv_ack_dispatch(ep: u64, dec: Decode, stay: State, accept: bool) -> Option<(State, bool)> {
    match dec {
        Decode::Done =>
            if accept { Some((State { kind: StateKind::Ct2Sampled, epoch: ep }, false)) } else { None },
        Decode::StillReceiving => Some((stay, false)),
    }
}

/// The epoch (if any) exposed in state `s` — the post-compromise leakage predicate.
/// Eight states expose their current epoch; `KeysUnsampled` / `NoHeaderReceived` /
/// `HeaderReceived` expose none. XREF: spqr states.rs:66-88 @f2589fe
/// (`States::vulnerable_epochs`, `#[cfg(test)]`) [structure-faithful: `Vec<Epoch>` of length
/// 0 or 1 → `Option<u64>`; this is the spec witness of compromise, not production logic].
pub fn vulnerable_epoch(s: State) -> Option<u64> {
    match s.kind {
        StateKind::KeysUnsampled => None,
        StateKind::NoHeaderReceived => None,
        StateKind::HeaderReceived => None,
        _ => Some(s.epoch),
    }
}
