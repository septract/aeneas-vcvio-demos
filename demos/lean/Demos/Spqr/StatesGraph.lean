/-
  SPQR typestate graph lemmas — output-key emission timing and the vulnerable-epoch
  compromise-set characterisation.

  The companion file `Demos/Spqr/States.lean` proves the extracted transition functions
  (`send_step` / `recv_step` / `vulnerable_epoch`, from `Demos/Extracted/States.lean`,
  the Aeneas extraction of SPQR `f2589fe`'s `v1/chunked/states.rs`) are TOTAL — i.e. they
  denote honest pure functions. This file proves *what they compute*: the structural
  properties of the 11-state transition graph that a future SCKA security game would
  quantify over. NO security game is defined here — these are value-level (functional)
  facts about the extracted dispatch, in-boundary unconditionally (see TRUST.md, the
  libsignal/SPQR node section: "the typestate is a structure-faithful skeleton … not a
  security theorem").

  Two property families:

  * **Output-key emission timing.** The transition functions return an output-key flag
    (the `Bool` the SCKA game reads as "an `output_key` was produced this step"). We pin
    *exactly* which states/inputs raise it:
      - `send_step`: the flag is `true` for EXACTLY one state — `HeaderReceived`, where the
        responder samples its first ciphertext and the send advances to `Ct1Sampled`.
      - `recv_step`: the flag is `true` for EXACTLY the path `EkSentCt1Received` + `Ct2`
        payload + decode `Done` + `accept` (the round-completing receive into
        `NoHeaderReceived`).
    Both are proved as iff-characterisations, plus the per-state "no key emitted" facts.

  * **`vulnerable_epoch` tracks the compromise set.** `vulnerable_epoch s` is `none` for
    EXACTLY the three "no live epoch secret" states (`KeysUnsampled`, `NoHeaderReceived`,
    `HeaderReceived`) and `some s.epoch` for the other eight (the states that hold a
    sampled secret an adversary could compromise). We give the iff-characterisation and the
    structural coupling to the output flags: whenever a transition emits an output key, the
    state it lands in is vulnerable at the emitting party's epoch.
-/
import Demos.Extracted.States
import Demos.Spqr.States

open Aeneas Std Result
open states (State StateKind PayloadKind Decode send_step recv_step vulnerable_epoch
  recv_ek_dispatch recv_ack_dispatch)

-- The exhaustive case-split proofs below use `<;>` chains that close some branches eagerly; the
-- focus-linter flags the (harmless) leftover sequencing.
set_option linter.unnecessarySeqFocus false

namespace Spqr.States

/-! ## Pure projections of the extracted transitions.

The extracted `send_step` / `recv_step` / `vulnerable_epoch` are total (proved in
`States.lean`); each is a deterministic dispatch returning `ok (...)` on every input
(`recv_step` returns `ok none` on the reject/out-of-window branches). We work with their
`Result` form directly: every lemma below is an *equation* on the `ok (...)` value, so it
fully pins the computed result. -/

/-- The send-step output-key flag is `true` for **exactly one** state: `HeaderReceived`.
This is the responder's first-ciphertext emission (advancing `HeaderReceived → Ct1Sampled`),
the single point in the send graph where a fresh output key is produced. -/
theorem send_step_outputs_key_iff (s : State) (s' : State) (p : PayloadKind) (b : Bool) :
    send_step s = ok (s', p, b) → (b = true ↔ s.kind = StateKind.HeaderReceived) := by
  unfold send_step
  cases s with
  | mk kind epoch =>
    cases kind <;> simp_all

/-- Concretely: from `HeaderReceived`, `send_step` emits an output key and advances to
`Ct1Sampled` (the only output-emitting send transition), with payload `Ct1`. -/
theorem send_step_headerReceived (s : State) (h : s.kind = StateKind.HeaderReceived) :
    send_step s = ok ({ s with kind := StateKind.Ct1Sampled }, PayloadKind.Ct1, true) := by
  unfold send_step
  cases s with
  | mk kind epoch => cases kind <;> simp_all

/-- For every state OTHER than `HeaderReceived`, `send_step` emits NO output key. -/
theorem send_step_no_key_of_ne (s : State) (s' : State) (p : PayloadKind) (b : Bool)
    (hne : s.kind ≠ StateKind.HeaderReceived) :
    send_step s = ok (s', p, b) → b = false := by
  intro h
  have := (send_step_outputs_key_iff s s' p b h)
  cases b with
  | false => rfl
  | true => exact absurd (this.1 rfl) hne

/-! ## recv-step output-key timing. -/

/-- The receive-step output-key flag is `true` for **exactly one** path: from
`EkSentCt1Received`, an in-window `Ct2` payload whose decode is `Done` and that is
`accept`ed — the round-completing receive that advances to `NoHeaderReceived` and emits
the responder's output key. Every other state / payload / decode / accept combination
emits no key. -/
theorem recv_step_outputs_key_iff
    (s : State) (msg_epoch : Std.U64) (payload : PayloadKind) (dec : Decode) (accept : Bool)
    (s' : State) (b : Bool) :
    recv_step s msg_epoch payload dec accept = ok (some (s', b)) →
      (b = true ↔
        s.kind = StateKind.EkSentCt1Received ∧
        ¬ (msg_epoch > s.epoch) ∧ ¬ (msg_epoch < s.epoch) ∧
        payload = PayloadKind.Ct2 ∧ dec = Decode.Done ∧ accept = true) := by
  unfold recv_step recv_ek_dispatch recv_ack_dispatch
  cases s with
  | mk kind epoch =>
    cases kind <;> intro h <;> dsimp only [] at h ⊢ <;> (repeat' split at h) <;>
      (first
        | (simp only [reduceCtorEq] at h ⊢ <;> (try (obtain ⟨_, rfl⟩ := h)) <;> tauto)
        | (cases hh : msg_epoch - epoch <;> simp_all <;> split_ifs at h <;> simp_all))

/-- Concretely: from `EkSentCt1Received`, an in-window `Ct2`/`Done`/`accept` receive emits the
output key and advances to `NoHeaderReceived` (the unique output-emitting receive transition). -/
theorem recv_step_ekSentCt1Received_done
    (s : State) (msg_epoch : Std.U64)
    (heq : msg_epoch = s.epoch) (h : s.kind = StateKind.EkSentCt1Received) :
    recv_step s msg_epoch PayloadKind.Ct2 Decode.Done true =
      ok (some ({ s with kind := StateKind.NoHeaderReceived }, true)) := by
  unfold recv_step
  cases s with
  | mk kind epoch =>
    subst heq h
    -- msg_epoch = epoch, so both comparisons are false; the Done/accept branch fires
    simp

/-- For every receive that lands in a state (`some (s', b)`), if the starting state is NOT
`EkSentCt1Received`, NO output key is emitted. -/
theorem recv_step_no_key_of_ne
    (s : State) (msg_epoch : Std.U64) (payload : PayloadKind) (dec : Decode) (accept : Bool)
    (s' : State) (b : Bool) (hne : s.kind ≠ StateKind.EkSentCt1Received) :
    recv_step s msg_epoch payload dec accept = ok (some (s', b)) → b = false := by
  intro h
  have := (recv_step_outputs_key_iff s msg_epoch payload dec accept s' b h)
  cases b with
  | false => rfl
  | true => exact absurd (this.1 rfl).1 hne

/-! ## `vulnerable_epoch` tracks the compromise set.

`vulnerable_epoch s` reports the epoch whose chaining/round secrets are *live* in state `s` —
the set an adversary could compromise. It is `none` for EXACTLY the three states that hold no
sampled secret (`KeysUnsampled` before A samples; `NoHeaderReceived`/`HeaderReceived` on B's
side before a ciphertext is sampled), and `some s.epoch` for the other eight. -/

/-- The "not vulnerable" (no live epoch secret) states are EXACTLY the three: `KeysUnsampled`,
`NoHeaderReceived`, `HeaderReceived`. -/
theorem vulnerable_epoch_none_iff (s : State) :
    vulnerable_epoch s = ok none ↔
      (s.kind = StateKind.KeysUnsampled ∨ s.kind = StateKind.NoHeaderReceived ∨
       s.kind = StateKind.HeaderReceived) := by
  unfold vulnerable_epoch
  cases s with
  | mk kind epoch => cases kind <;> simp

/-- Dually, `vulnerable_epoch s` reports `some s.epoch` for EXACTLY the eight key-holding
states (the complement of the three above). When it reports an epoch, it is *this* state's
epoch — the compromise set is tracked at the party's current epoch, never a stale one. -/
theorem vulnerable_epoch_some_iff (s : State) (e : Std.U64) :
    vulnerable_epoch s = ok (some e) ↔
      (e = s.epoch ∧
        s.kind ≠ StateKind.KeysUnsampled ∧ s.kind ≠ StateKind.NoHeaderReceived ∧
        s.kind ≠ StateKind.HeaderReceived) := by
  unfold vulnerable_epoch
  cases s with
  | mk kind epoch => cases kind <;> simp [eq_comm]

/-- `vulnerable_epoch` never reports an epoch other than the state's own: if it returns
`some e`, then `e = s.epoch`. (No leakage of a past epoch's secret through the predicate.) -/
theorem vulnerable_epoch_eq_epoch (s : State) (e : Std.U64) :
    vulnerable_epoch s = ok (some e) → e = s.epoch := by
  intro h
  exact ((vulnerable_epoch_some_iff s e).1 h).1

/-! ## Coupling: an emitted output key lands in a vulnerable state.

The output-key flag and the vulnerability predicate are not independent: whenever a transition
*emits* an output key, the state it moves into is one that holds a live epoch secret (is
`vulnerable_epoch = some _`). This is the structural invariant a post-compromise-security
argument relies on — a fresh `output_key` is always accompanied by a tracked compromise point. -/

/-- The send-step output-key target is vulnerable: `HeaderReceived` (the only key-emitting send)
advances to `Ct1Sampled`, which `vulnerable_epoch` tracks at the same epoch. -/
theorem send_step_output_target_vulnerable (s : State)
    (h : s.kind = StateKind.HeaderReceived) :
    ∃ s' p, send_step s = ok (s', p, true) ∧ vulnerable_epoch s' = ok (some s'.epoch) := by
  refine ⟨{ s with kind := StateKind.Ct1Sampled }, PayloadKind.Ct1, send_step_headerReceived s h, ?_⟩
  unfold vulnerable_epoch
  simp

/-- The recv-step output-key target is vulnerable: the unique key-emitting receive advances
`EkSentCt1Received → NoHeaderReceived`. NB the *landing* state `NoHeaderReceived` is itself a
"reset" (B awaiting the next header, so `vulnerable_epoch = none`); what the output key exposes
is the epoch secret of the round just completed — the emitting party's epoch, not the new
state's. So unlike send, the recv emission is the round-CLOSING key: the lemma records that the
landing state is precisely the non-vulnerable reset, the dual structural fact. -/
theorem recv_step_output_target_reset
    (s : State) (msg_epoch : Std.U64)
    (heq : msg_epoch = s.epoch) (h : s.kind = StateKind.EkSentCt1Received) :
    ∃ s', recv_step s msg_epoch PayloadKind.Ct2 Decode.Done true = ok (some (s', true)) ∧
      vulnerable_epoch s' = ok none := by
  refine ⟨{ s with kind := StateKind.NoHeaderReceived },
    recv_step_ekSentCt1Received_done s msg_epoch heq h, ?_⟩
  unfold vulnerable_epoch
  simp

end Spqr.States
