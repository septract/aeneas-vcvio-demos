/-
  SPQR node — value adequacy of the extracted SCKA transition structure.

  `states.rs` is the Aeneas extraction of SPQR's `v1/chunked/states.rs` state machine
  (`f2589fe`), as a control-flow skeleton: the 11-state `States` enum and its `send`/`recv`
  transitions, the message-payload emission, the output-key (epoch-secret) timing, the
  epoch advance, and the `vulnerable_epochs` leakage predicate. This is the **construction
  the SCKA security game is about** — the game quantifies over exactly this state sequence.

  The cryptographic operations the real states carry (`PolyEncoder`/`PolyDecoder`, ML-KEM
  encaps/decaps, the chain step, the MAC) are abstracted to typed boundaries (the codec
  decode outcome is the input `Decode`; the verified primitives live in the gf / sha256 /
  authenticator nodes; ML-KEM is the assumed IND-CCA floor on the proof side). So the
  value-adequacy obligation here is **totality**: the extracted transition functions are
  total (every `match` is exhaustive, the lone `msg_epoch - epoch` is guarded), hence they
  denote honest pure functions — the ε = 0 premise for lifting the transition graph into
  the VCVio SCKA game.
-/
import Demos.Extracted.States

open Aeneas Std Result

namespace Spqr.States

/-- **Initialisation is total** (party A starts in `KeysUnsampled`). -/
theorem init_a_total : states.init_a ⦃ fun _ => True ⦄ := by
  unfold states.init_a; step*

/-- **Initialisation is total** (party B starts in `NoHeaderReceived`). -/
theorem init_b_total : states.init_b ⦃ fun _ => True ⦄ := by
  unfold states.init_b; step*

/-- **Value adequacy of the send transition.** `send_step` is total: a pure dispatch over the
11 states to `(next state, emitted payload kind, output-key flag)`. -/
theorem send_step_total (s : states.State) : states.send_step s ⦃ fun _ => True ⦄ := by
  unfold states.send_step; step*

/-- The `Ct1Sampled` recv dispatch — the `(ek-decode-done × ct1_ack)` product — is total. -/
@[step]
theorem recv_ek_dispatch_total (ep : Std.U64) (dec : states.Decode) (ct1_ack accept : Bool) :
    states.recv_ek_dispatch ep dec ct1_ack accept ⦃ fun _ => True ⦄ := by
  unfold states.recv_ek_dispatch; step*

/-- The `Ct1Acknowledged` recv dispatch is total. -/
@[step]
theorem recv_ack_dispatch_total (ep : Std.U64) (dec : states.Decode) (stay : states.State)
    (accept : Bool) :
    states.recv_ack_dispatch ep dec stay accept ⦃ fun _ => True ⦄ := by
  unfold states.recv_ack_dispatch; step*

/-- **Value adequacy of the receive transition.** `recv_step` is total: the
`msg_epoch.cmp(epoch)` three-way branch, payload match, codec-outcome dispatch, and the
`accept` rejection boundary (which maps the upstream `recv_*_chunk(...)?` MAC/chain `Err` to
`None`) are exhaustive, and the only arithmetic — `msg_epoch - epoch` in the `Ct2Sampled`
next-round case — is guarded by `msg_epoch > epoch`, so it never underflows. -/
theorem recv_step_total (s : states.State) (msg_epoch : Std.U64) (payload : states.PayloadKind)
    (dec : states.Decode) (accept : Bool) :
    states.recv_step s msg_epoch payload dec accept ⦃ fun _ => True ⦄ := by
  unfold states.recv_step
  step*

/-- **Value adequacy of the vulnerability predicate.** `vulnerable_epoch` is total — the
per-state leakage predicate the post-compromise (healing) argument tracks. -/
theorem vulnerable_epoch_total (s : states.State) :
    states.vulnerable_epoch s ⦃ fun _ => True ⦄ := by
  unfold states.vulnerable_epoch; step*

end Spqr.States
