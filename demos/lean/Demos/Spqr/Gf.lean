/-
  SPQR node — value adequacy of the extracted GF(2¹⁶) field arithmetic.

  `gf.rs` is the Aeneas extraction of Signal's Reed–Solomon field arithmetic over
  GF(2¹⁶) (the erasure-code substrate of the Sparse Post-Quantum Ratchet), in the
  portable form Signal's own hax/F\* build verifies. The genuine content is the
  carryless multiply `poly_mul` and the table-driven reduction `poly_reduce`; their
  composition `gf_mul` is the field multiply. This is the SPQR analog of the
  ratchet demo's ChaCha node: real arithmetic, so the value-adequacy obligation is
  **totality** — the extracted code never panics, overflows, or diverges, hence it
  denotes an honest pure function on `u16`.

  We prove totality of every arithmetic entry point (`gf_add`, `poly_mul`,
  `poly_reduce`, `gf_mul`, `gf_div`) and pin `gf_add` to XOR. Algebraic field laws
  (associativity, distributivity, reduction-correctness against `Spec.GF16`) are a
  separate, heavier obligation, out of scope for this node — we certify the
  extraction is a total function, the ε = 0 lifting premise.
-/
import Demos.Extracted.Gf

open Aeneas Std Result

namespace Spqr.Gf

/-- Masking by `0xFF` keeps a `usize` below 256 — taught to `scalar_tac` so the
`poly_reduce` table-index bounds (`(v >>> 16) & 0xFF < 256`) discharge automatically. -/
@[scalar_tac (x &&& 255#usize).val]
theorem and255_le (x : Std.Usize) : (x &&& 255#usize).val ≤ 255 := by
  simp only [UScalar.val_and]; exact Nat.and_le_right

/-- Field addition: total, and exactly bitwise XOR. Mirrors `GF16::AddAssign`
(`self.value ^= other.value`) — characteristic-2 addition. -/
theorem gf_add_total (a b : Std.U16) : gf.gf_add a b ⦃ r => r = a ^^^ b ⦄ := by
  unfold gf.gf_add
  step*

/-- The carryless-multiply loop never fails: shifts by `shift < 16` (in range for
`u16`/`u32`) and an XOR accumulate; `shift` rises to 16. Loop state is `(acc, shift)`. -/
theorem poly_mul_loop_ok (b : Std.U16) (me : Std.U32) :
    ∀ (acc shift : Std.U32), shift.val ≤ 16 →
      gf.poly_mul_loop b acc me shift ⦃ fun _ => True ⦄ := by
  intro acc shift hs
  unfold gf.poly_mul_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : Std.U32 × Std.U32 => 16 - s.2.val)
    (inv := fun s : Std.U32 × Std.U32 => s.2.val ≤ 16)
    (post := fun _ => True)
  · rintro ⟨acc1, shift1⟩ hinv
    simp only [gf.poly_mul_loop.body]
    split
    · rename_i hlt
      step as ⟨v1, hv1⟩
      step as ⟨i1, hi1⟩
      split
      · step as ⟨i2, hi2⟩
        step as ⟨shift2, hshift2⟩
        refine ⟨?_, ?_⟩ <;> scalar_tac
      · step as ⟨shift2, hshift2⟩
        refine ⟨?_, ?_⟩ <;> scalar_tac
    · trivial
  · exact hs

/-- `poly_mul` is total: the carryless product of two field elements always exists. -/
@[step]
theorem poly_mul_total (a b : Std.U16) : gf.poly_mul a b ⦃ fun _ => True ⦄ := by
  unfold gf.poly_mul
  step as ⟨me, hme⟩
  apply poly_mul_loop_ok
  scalar_tac

/-- `reduce_from_byte`'s loop never fails: shifts by `i-1 < 8` and XOR/cast; `i` falls to 0.
Loop state is `(a, out, i)`. -/
theorem reduce_from_byte_loop_ok :
    ∀ (a : Std.U8) (out i : Std.U32), i.val ≤ 8 →
      gf.reduce_from_byte_loop a out i ⦃ fun _ => True ⦄ := by
  intro a out i hi
  unfold gf.reduce_from_byte_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : Std.U8 × Std.U32 × Std.U32 => s.2.2.val)
    (inv := fun s : Std.U8 × Std.U32 × Std.U32 => s.2.2.val ≤ 8)
    (post := fun _ => True)
  · rintro ⟨a1, out1, i1⟩ hinv
    simp only [gf.reduce_from_byte_loop.body]
    split
    · rename_i hlt
      step as ⟨i2, hi2⟩
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      split
      · step as ⟨i5, hi5⟩
        step as ⟨i6, hi6⟩
        step as ⟨i7, hi7⟩
        step as ⟨a2, ha2⟩
        refine ⟨?_, ?_⟩ <;> scalar_tac
      · refine ⟨?_, ?_⟩ <;> scalar_tac
    · trivial
  · exact hi

@[step]
theorem reduce_from_byte_total (a : Std.U8) : gf.reduce_from_byte a ⦃ fun _ => True ⦄ := by
  unfold gf.reduce_from_byte
  apply reduce_from_byte_loop_ok
  scalar_tac

/-- Building the 256-entry reduction table never fails (each entry is a total
`reduce_from_byte`; `i` rises to 256, the array length). Loop state is `(out, i)`. -/
theorem reduce_bytes_loop_ok :
    ∀ (out : Array Std.U16 256#usize) (i : Std.Usize), i.val ≤ 256 →
      gf.reduce_bytes_loop out i ⦃ fun _ => True ⦄ := by
  intro out i hi
  unfold gf.reduce_bytes_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U16 256#usize) × Std.Usize => 256 - s.2.val)
    (inv := fun s : (Array Std.U16 256#usize) × Std.Usize => s.2.val ≤ 256)
    (post := fun _ => True)
  · rintro ⟨o1, i1⟩ hinv
    simp only [gf.reduce_bytes_loop.body]
    split
    · rename_i hlt
      step as ⟨i2, hi2⟩
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      step as ⟨o2, ho2⟩
      step as ⟨i5, hi5⟩
      refine ⟨?_, ?_⟩ <;> scalar_tac
    · trivial
  · exact hi

@[step]
theorem reduce_bytes_total : gf.reduce_bytes ⦃ fun _ => True ⦄ := by
  unfold gf.reduce_bytes
  apply reduce_bytes_loop_ok
  scalar_tac

/-- **Value adequacy of the reduction.** `poly_reduce` is total: the two table folds
index `[u16; 256]` at `(v >>> 24)` and `(v >>> 16) & 0xFF`, both `< 256`, so neither
read is out of bounds and the function denotes a total `u32 → u16`. -/
@[step]
theorem poly_reduce_total (v : Std.U32) : gf.poly_reduce v ⦃ fun _ => True ⦄ := by
  unfold gf.poly_reduce
  -- `step*` advances the straight-line body, leaving the two table-index bounds.
  step*
  · -- first index: `(v >>> 24) < 256`.
    scalar_tac
  · -- second index: `((v >>> 16) & 0xFF) < 256`, from masking with `0xFF`.
    have key : (shifted_v &&& 255#usize).val ≤ 255 := and255_le shifted_v
    scalar_tac

/-- **Value adequacy of the field multiply.** `gf_mul = poly_reduce ∘ poly_mul` is
total — the headline ε = 0 lifting obligation for the SPQR field arithmetic. -/
@[step]
theorem gf_mul_total (a b : Std.U16) : gf.gf_mul a b ⦃ fun _ => True ⦄ := by
  unfold gf.gf_mul
  step*

/-- The Fermat-inverse division ladder is total: 15 iterations of the (total) field
multiply. Mirrors `GF16::const_div` (`a / b = a · b^(2¹⁶-2)`). Loop state `(sq, out, i)`. -/
theorem gf_div_total (numer denom : Std.U16) : gf.gf_div numer denom ⦃ fun _ => True ⦄ := by
  unfold gf.gf_div
  unfold gf.gf_div_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : Std.U16 × Std.U16 × Std.Usize => 16 - s.2.2.val)
    (inv := fun s : Std.U16 × Std.U16 × Std.Usize => s.2.2.val ≤ 16)
    (post := fun _ => True)
  · rintro ⟨sq, out, i⟩ hinv
    simp only [gf.gf_div_loop.body]
    split
    · rename_i hlt
      step as ⟨sq1, hsq1⟩
      step as ⟨out1, hout1⟩
      step as ⟨i1, hi1⟩
      refine ⟨?_, ?_⟩ <;> scalar_tac
    · trivial
  · scalar_tac

end Spqr.Gf
