/-
  Demo 3 — value adequacy of the extracted ratchet-step glue.

  `ratchet.ratchet_split` is the Aeneas extraction of a `while` loop that splits a 64-byte
  KDF/PRG output block into the next 32-byte chain key (`block[0..32]`) and a 32-byte message
  key (`block[32..64]`). Aeneas emits the `loop`/`ControlFlow` combinator, threading *both*
  output arrays through the loop state. We prove, with a loop invariant via
  `Std.loop.spec_decr_nat`, that it computes exactly that split — the value-adequacy (ε = 0
  node) obligation for the symmetric ratchet of demo 3.

  This is the deterministic per-step *plumbing*; the cryptographic KDF/PRG itself is abstract
  on the Lean side (its security is the hardness assumption — see `Demos/Ratchet/Chain.lean`).
-/
import Demos.Extracted.Ratchet

open Aeneas Std Result

namespace ratchet

/-- The loop computes the byte split on the indices already processed, for all priors:
`ck` accumulates `block[0..i]` and `mk` accumulates `block[32..32+i]`. -/
theorem ratchet_split_loop_spec (block : Array Std.U8 64#usize) :
    ∀ (ck mk : Array Std.U8 32#usize) (i : Std.Usize),
      i.val ≤ 32 →
      (∀ j, j < i.val → ck.val[j]! = block.val[j]!) →
      (∀ j, j < i.val → mk.val[j]! = block.val[32 + j]!) →
      ratchet_split_loop block ck mk i
        ⦃ r => (∀ j, j < 32 → r.1.val[j]! = block.val[j]!) ∧
               (∀ j, j < 32 → r.2.val[j]! = block.val[32 + j]!) ⦄ := by
  intro ck mk i hi hck hmk
  unfold ratchet_split_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 32#usize) × (Array Std.U8 32#usize) × Std.Usize =>
      32 - s.2.2.val)
    (inv := fun s : (Array Std.U8 32#usize) × (Array Std.U8 32#usize) × Std.Usize =>
      s.2.2.val ≤ 32 ∧
      (∀ j, j < s.2.2.val → s.1.val[j]! = block.val[j]!) ∧
      (∀ j, j < s.2.2.val → s.2.1.val[j]! = block.val[32 + j]!))
    (post := fun r : (Array Std.U8 32#usize) × (Array Std.U8 32#usize) =>
      (∀ j, j < 32 → r.1.val[j]! = block.val[j]!) ∧
      (∀ j, j < 32 → r.2.val[j]! = block.val[32 + j]!))
  · rintro ⟨ck1, mk1, i1⟩ ⟨hi1, hck1, hmk1⟩
    simp only [ratchet_split_loop.body]
    split
    · rename_i hlt
      step as ⟨v1, hv1⟩
      step as ⟨a, ha⟩
      step as ⟨off, hoff⟩
      step as ⟨v3, hv3⟩
      step as ⟨a1, ha1⟩
      step as ⟨i4, hi4⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · scalar_tac
      · intro j hj
        subst ha
        by_cases hje : j = i1.val
        · subst hje
          simp_lists [hv1]
        · have hlt2 : j < i1.val := by scalar_tac
          simp_lists
          exact hck1 j hlt2
      · intro j hj
        subst ha1
        by_cases hje : j = i1.val
        · subst hje
          simp_lists [hv3]
          scalar_tac
        · have hlt2 : j < i1.val := by scalar_tac
          simp_lists
          exact hmk1 j hlt2
      · scalar_tac
    · rename_i hge
      refine ⟨?_, ?_⟩
      · intro j hj; apply hck1; scalar_tac
      · intro j hj; apply hmk1; scalar_tac
  · exact ⟨hi, hck, hmk⟩

/-- **Value adequacy.** The extracted `ratchet_split` is total and computes the byte split:
the first output is `block[0..32]` (the next chain key), the second is `block[32..64]` (the
message key). Stated as a `Result` postcondition, so it certifies there is no `fail`/`div`. -/
theorem ratchet_split_spec (block : Array Std.U8 64#usize) :
    ratchet_split block
      ⦃ r => (∀ j, j < 32 → r.1.val[j]! = block.val[j]!) ∧
             (∀ j, j < 32 → r.2.val[j]! = block.val[32 + j]!) ⦄ := by
  unfold ratchet_split
  apply ratchet_split_loop_spec
  · scalar_tac
  · intro j hj; scalar_tac
  · intro j hj; scalar_tac

end ratchet
