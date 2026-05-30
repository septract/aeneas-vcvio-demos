/-
  Demo 2b — value adequacy of the meaty 32-byte combiner.

  `stream.combine` is the Aeneas extraction of a `while` loop over fixed-size byte arrays
  (Aeneas emits the `loop`/`ControlFlow` combinator). We prove, with a loop invariant via
  `Std.loop.spec_decr_nat`, that it computes the **pointwise XOR** — the value-adequacy
  obligation for the meatier stream-cipher extraction.
-/
import Demos.Extracted.Stream

open Aeneas Std Result

namespace stream

set_option maxHeartbeats 1000000

/-- The loop computes the pointwise xor on the indices already processed, for all priors. -/
theorem combine_loop_spec (ks m : Array Std.U8 32#usize) :
    ∀ (c : Array Std.U8 32#usize) (i : Std.Usize),
      i.val ≤ 32 →
      (∀ j, j < i.val → c.val[j]! = ks.val[j]! ^^^ m.val[j]!) →
      combine_loop ks m c i ⦃ r => ∀ j, j < 32 → r.val[j]! = ks.val[j]! ^^^ m.val[j]! ⦄ := by
  intro c i hi hc
  unfold combine_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 32#usize) × Std.Usize => 32 - s.2.val)
    (inv := fun s : (Array Std.U8 32#usize) × Std.Usize => s.2.val ≤ 32 ∧
      ∀ j, j < s.2.val → s.1.val[j]! = ks.val[j]! ^^^ m.val[j]!)
    (post := fun r : Array Std.U8 32#usize =>
      ∀ j, j < 32 → r.val[j]! = ks.val[j]! ^^^ m.val[j]!)
  · rintro ⟨c1, i1⟩ ⟨hi1, hc1⟩
    simp only [combine_loop.body]
    split
    · rename_i hlt
      step as ⟨v1, hv1⟩
      step as ⟨v2, hv2⟩
      step as ⟨v3, hv3⟩
      step as ⟨a, ha⟩
      step as ⟨i4, hi4⟩
      refine ⟨?_, ?_, ?_⟩
      · scalar_tac
      · intro j hj
        subst ha
        by_cases hje : j = i1.val
        · subst hje
          simp_lists [hv1, hv2]
          scalar_tac
        · have hlt2 : j < i1.val := by scalar_tac
          simp_lists
          exact hc1 j hlt2
      · scalar_tac
    · rename_i hge
      intro j hj
      apply hc1
      scalar_tac
  · exact ⟨hi, hc⟩

/-- **Value adequacy.** The extracted `combine` computes the pointwise XOR of its inputs. -/
theorem combine_spec (ks m : Array Std.U8 32#usize) :
    combine ks m ⦃ r => ∀ j, j < 32 → r.val[j]! = ks.val[j]! ^^^ m.val[j]! ⦄ := by
  unfold combine
  apply combine_loop_spec
  · scalar_tac
  · intro j hj; scalar_tac

end stream
