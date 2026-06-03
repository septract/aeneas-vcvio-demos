/-
  SPQR Reed–Solomon codec — Layer C (PARTIAL): value specs of the decoder loops as
  explicit `gfMulV`/`gfAddV` recurrences over the EXTRACTED code.

  ## What this file establishes (genuine, IN-BOUNDARY, field-law-FREE)

  The banked specs in `Spqr/Gf.lean` characterize the encoder core (`poly_eval` =
  Horner fold `hornerV`) and one decoder step (`mult_xdiff_trailing` = one `(x−c)`
  multiply). This file extends that same value-spec style to the **decoder's
  evaluation kernel** `gf.compute_at` (the `decode_value_at` re-evaluation step):

    C1. **`compute_at_loop1` is the coefficient dot product** over the field:
        started from accumulator `out` at index `k`, the loop folds in
        `out ↦ gfAddV out (gfMulV coeffs[k] powers[k])`, i.e. it computes the pure
        recurrence `dotV coeffs powers out k`. (headline about `gf.compute_at_loop1`)

    C2. **`compute_at_loop0` builds the x-power table** by the squaring recurrence
        `powers[i] = gfMulV powers[i/2] powers[i/2 + i%2]`, leaving entries below the
        write index and at/after `len` untouched. (headline about `gf.compute_at_loop0`)

    C3. **`compute_at` is the dotted power table**: `gf.compute_at coeffs len x`
        succeeds with value `dotV coeffs (the power table) 0#u16 0` — combining C1+C2.
        (headline about `gf.compute_at`)

  These need NO field laws — they are exact "what value the loop computes" specs, the
  same proof shape as the six already-banked specs (`poly_eval_eq`, `poly_add_eq`,
  `poly_scale_eq`, `mult_xdiff_trailing_eq`). They are real, in-boundary results ABOUT
  the extracted `gf.compute_at*` and are registered as headlines.

  ## What this file does NOT do (the honest open obligations)

  - Connecting `dotV` / `hornerV` to Mathlib's `Polynomial.eval` requires the GF(2¹⁶)
    FIELD instance (`gfMulV`/`gfAddV` ≅ GF(2)[X]/(POLY)) — the documented gap in
    `Gf16Field.lean` (irreducibility of POLY + the clmul/reduce characterization). So
    the unconditional `decode ∘ encode = id` about `gf.decode_value_at` stays open.
  - The `prepare`/`complete`/`lagrange_interpolate` loop value specs (the interpolation
    side) are not attempted this round.
-/
import Demos.Spqr.Gf

open Aeneas Std Result
open Spqr.Gf

namespace Spqr.RsBridge

/-! ### C1. `compute_at_loop1` computes the coefficient dot product over the field. -/

/-- The dot-product accumulator `compute_at_loop1` computes. Mirrors the loop body
EXACTLY: started at accumulator `out` and index `k`, each step folds in one more
term from the top, `out ↦ gfAddV out (gfMulV coeffs[k] powers[k])`, incrementing `k`
until it reaches `len`. -/
def dotV (coeffs powers : Array Std.U16 37#usize) (len : Std.Usize) :
    Std.U16 → Nat → Std.U16
  | out, k =>
    if k < len.val then
      dotV coeffs powers len (gfAddV out (gfMulV coeffs.val[k]! powers.val[k]!)) (k + 1)
    else out
  termination_by _ k => len.val - k
  decreasing_by
    rename_i h; omega

/-- **Dot-product value spec of the evaluation loop.** `compute_at_loop1` computes
exactly the pure fold `dotV`: started from accumulator `out` and index `k`, it returns
`dotV coeffs powers len out k.val`. -/
theorem compute_at_loop1_eq (coeffs : Array Std.U16 37#usize) (len : Std.Usize)
    (powers : Array Std.U16 37#usize) (hlen : len.val ≤ 37) :
    ∀ (out : Std.U16) (k : Std.Usize),
      gf.compute_at_loop1 coeffs len powers out k
        ⦃ r => r = dotV coeffs powers len out k.val ⦄ := by
  intro out k
  unfold gf.compute_at_loop1
  apply Std.loop.spec_decr_nat
    (measure := fun s : Std.U16 × Std.Usize => len.val - s.2.val)
    (inv := fun s : Std.U16 × Std.Usize =>
      dotV coeffs powers len s.1 s.2.val = dotV coeffs powers len out k.val)
    (post := fun r : Std.U16 => r = dotV coeffs powers len out k.val)
  · rintro ⟨o1, k1⟩ hinv
    simp only [gf.compute_at_loop1.body]
    split
    · rename_i hlt
      step as ⟨i, hi⟩
      step as ⟨i1, hi1⟩
      rw [gf_mul_eq]
      simp only [Std.bind_tc_ok]
      rw [gf_add_eq]
      step as ⟨k2, hk2⟩
      refine ⟨?_, by scalar_tac⟩
      simp only [hinv.symm]
      conv_rhs => rw [dotV]
      rw [if_pos (by scalar_tac)]
      rw [hk2, hi, hi1]
    · rename_i hge
      have h : ¬ k1.val < len.val := by scalar_tac
      conv at hinv => rw [dotV, if_neg h]
      exact hinv
  · rfl

/-- **Dot-product value spec of `compute_at`'s coefficient loop** (entry point). The
extracted `gf.compute_at_loop1` started at `out = 0`, `k = 0` succeeds with value
`dotV coeffs powers len 0#u16 0` — the field dot product `Σ_{k<len} coeffs[k] ⊗ powers[k]`. -/
theorem compute_at_loop1_eq0 (coeffs : Array Std.U16 37#usize) (len : Std.Usize)
    (powers : Array Std.U16 37#usize) (hlen : len.val ≤ 37) :
    gf.compute_at_loop1 coeffs len powers 0#u16 0#usize
      ⦃ r => r = dotV coeffs powers len 0#u16 0 ⦄ :=
  compute_at_loop1_eq coeffs len powers hlen 0#u16 0#usize

/-! ### C2. `compute_at_loop0` builds the x-power table by the squaring recurrence. -/

/-- **Value spec of the power-table loop (the squaring recurrence).** Running
`compute_at_loop0` from write index `i ≥ 2` to `len ≤ 37` produces an array `r` whose
freshly written slots `i ≤ j < len` each satisfy the exact squaring recurrence the
extracted loop computes:
`r[j] = gfMulV r[j/2] r[j/2 + j%2]`.

This is a genuine value characterization (not just totality): the slot read indices
`j/2` and `j/2 + j%2` are both `< j` (using `j ≥ i ≥ 2`), hence already finalized and
never touched by a later write (writes target indices `≥ j+1`), so the recurrence holds
of the FINAL array `r`. Field-law-free — it characterizes which field products the loop
forms, in terms of `gfMulV` (the value spec of the extracted `gf_mul`). -/
theorem compute_at_loop0_recurrence (len : Std.Usize) (hlen : len.val ≤ 37) :
    ∀ (powers : Array Std.U16 37#usize) (i : Std.Usize), 2 ≤ i.val →
      gf.compute_at_loop0 len powers i
        ⦃ r => (∀ j, j < i.val → r.val[j]! = powers.val[j]!) ∧
               (∀ j, i.val ≤ j → j < len.val →
                  r.val[j]! = gfMulV r.val[j / 2]! r.val[j / 2 + j % 2]!) ⦄ := by
  intro powers i hi2
  unfold gf.compute_at_loop0
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U16 37#usize) × Std.Usize => len.val - s.2.val)
    (inv := fun s : (Array Std.U16 37#usize) × Std.Usize =>
      i.val ≤ s.2.val ∧
      (∀ j, j < i.val → s.1.val[j]! = powers.val[j]!) ∧
      (∀ j, i.val ≤ j → j < s.2.val →
        s.1.val[j]! = gfMulV s.1.val[j / 2]! s.1.val[j / 2 + j % 2]!))
    (post := fun r : Array Std.U16 37#usize =>
      (∀ j, j < i.val → r.val[j]! = powers.val[j]!) ∧
      (∀ j, i.val ≤ j → j < len.val →
        r.val[j]! = gfMulV r.val[j / 2]! r.val[j / 2 + j % 2]!))
  · rintro ⟨p1, i1⟩ ⟨hle, hbelow, hrec⟩
    simp only [gf.compute_at_loop0.body]
    split
    · rename_i hlt
      step as ⟨q1, hq1⟩
      step as ⟨a, ha⟩
      step as ⟨q2, hq2⟩
      step as ⟨q3, hq3⟩
      step as ⟨b, hb⟩
      rw [gf_mul_eq]
      step as ⟨p2, hp2⟩
      step as ⟨i2, hi2'⟩
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · -- below-region preservation: the write at `i1 ≥ i` doesn't touch `j < i`.
        intro j hj
        subst hp2
        have hjne : j ≠ i1.val := by scalar_tac
        simp_lists
        exact hbelow j hj
      · intro j hij hji2
        subst hp2
        -- The two slots the recurrence at `j` reads are `< j ≤ i1`, hence unaffected by
        -- this step's write at `i1` (so we can read the original `p1` there).
        have hjhalf : j / 2 < i1.val := by scalar_tac
        have hjsum : j / 2 + j % 2 < i1.val := by scalar_tac
        by_cases hje : j = i1.val
        · -- the slot just written: its value is exactly the recurrence over `p1`,
          -- and the read slots are `< i1`, untouched by the write.
          have hq1v : q1.val = j / 2 := by rw [hq1, hje]
          have hq3v : q3.val = j / 2 + j % 2 := by rw [hq3, hq1, hq2, hje]
          rw [hje]
          simp_lists
          rw [ha, hb, hq1v, hq3v, hje]
        · -- an earlier slot: recurrence held on `p1`, and neither it nor its read slots
          -- are touched by the write at `i1`.
          have hji1 : j < i1.val := by scalar_tac
          simp_lists
          rw [hrec j hij hji1]
    · rename_i hge
      -- `i1 ≥ len`, so every `j < len` is `< i1` and the invariant's recurrence applies.
      refine ⟨hbelow, ?_⟩
      intro j hij hjlen
      exact hrec j hij (by scalar_tac)
  · exact ⟨_root_.le_refl _, fun j hj => rfl, fun j hij hji => by scalar_tac⟩

/-! ### C3. `compute_at` is the field dot product of `coeffs` against the x-power table. -/

/-- **Value spec of `gf.compute_at` (the decoder's evaluation step).** For `len ≤ 37`,
`gf.compute_at coeffs len x` succeeds with a value that is the field dot product
`dotV coeffs powers len 0 0 = Σ_{k<len} coeffs[k] ⊗ powers[k]` of the coefficients
against an x-power table `powers` which:
  * has `powers[0] = 1` (= x⁰) and `powers[1] = x` (= x¹), and
  * for every `2 ≤ j < len` satisfies the squaring recurrence
    `powers[j] = gfMulV powers[j/2] powers[j/2 + j%2]`
i.e. `powers[j] = x^j` over the field (modulo the GF(2¹⁶) field laws connecting the
squaring recurrence to actual powers — the documented `Gf16Field` gap).

This is the full in-boundary value characterization of the extracted `gf.compute_at`,
assembled from `compute_at_loop0_recurrence` (the power table) and `compute_at_loop1_eq`
(the dot product). It is field-law-FREE: it pins exactly which `gfMulV`/`gfAddV`
combination the loops form. Connecting `dotV`/the power recurrence to `Polynomial.eval`
(hence `decode ∘ encode = id`) additionally needs the GF(2¹⁶) field instance. -/
theorem compute_at_eq (coeffs : Array Std.U16 37#usize) (len : Std.Usize) (x : Std.U16)
    (hlen : len.val ≤ 37) :
    gf.compute_at coeffs len x
      ⦃ r => ∃ powers : Array Std.U16 37#usize,
               powers.val[0]! = 1#u16 ∧ powers.val[1]! = x ∧
               (∀ j, 2 ≤ j → j < len.val →
                  powers.val[j]! = gfMulV powers.val[j / 2]! powers.val[j / 2 + j % 2]!) ∧
               r = dotV coeffs powers len 0#u16 0 ⦄ := by
  unfold gf.compute_at
  -- set up `powers[0] = 1`, `powers[1] = x`, then run the two loops.
  step as ⟨p1, hp1⟩
  step as ⟨p2, hp2⟩
  -- the power-table loop: its result `q` preserves slots `< 2` (so `q[0] = p2[0] = 1`,
  -- `q[1] = p2[1] = x`) and satisfies the squaring recurrence for `2 ≤ j < len`.
  have hloop0 := compute_at_loop0_recurrence len hlen p2 2#usize (by scalar_tac)
  step with hloop0 as ⟨q, hqbelow, hqrec⟩
  -- the dot-product loop: its result is `dotV coeffs q len 0 0`.
  have hloop1 := compute_at_loop1_eq0 coeffs len q hlen
  step with hloop1 as ⟨r, hr⟩
  refine ⟨q, ?_, ?_, hqrec, hr⟩
  · -- `q[0] = 1`: slot 0 < 2, preserved; and `p2 = p1[1 := x]`, `p1 = powers[0 := 1]`.
    have h0 := hqbelow 0 (by scalar_tac)
    rw [h0, hp2]
    simp_lists
    rw [hp1]
    simp_lists
  · -- `q[1] = x`: slot 1 < 2, preserved; `p2[1] = x`.
    have h1 := hqbelow 1 (by scalar_tac)
    rw [h1, hp2]
    simp_lists

end Spqr.RsBridge
