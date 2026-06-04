/-
  SPQR Reed–Solomon codec — Layer C (interpolation side, PARTIAL): value specs of the
  EXTRACTED interpolation loops (`gf.prepare`, `gf.complete`, `gf.lagrange_interpolate`)
  as explicit `gfMulV`/`gfAddV`/`gf_div` recurrences, field-law-FREE.

  ## What this file establishes (genuine, IN-BOUNDARY, field-law-FREE)

  The banked `Spqr/Gf.lean` characterizes the encoder core and one decoder step
  (`mult_xdiff_trailing` = one `(x−c)` multiply, `xdiffStep`), and `Spqr/RsBridge.lean`
  characterizes the decoder's *evaluation* kernel (`compute_at`). This file does the
  same for the decoder's *interpolation* loops — the ones that reconstruct the
  Lagrange polynomial from the (x, y) samples:

    C2a. **`complete_loop0` computes the denominator product** — the running field
         product `∏_{j<n, pix≠xs[j]} (pix ⊕ xs[j])` (a `gfMulV`/`gfAddV` fold). The same
         accumulator-recurrence shape as `compute_at_loop1`. (about `gf.complete_loop0`)

    C3a. **`lagrange_interpolate_loop0` copies `working[k+1] → out[k]`** (the
         "divide by x"/drop-lowest-coefficient shift). (about `gf.lagrange_interpolate_loop0`)

    C3b. **`lagrange_interpolate_loop1_loop0` accumulates `out[j] ⊕= working[j+1]`** —
         the `gfAddV` accumulation of one `complete` result into the running sum,
         shifted down by one coefficient. (about `gf.lagrange_interpolate_loop1_loop0`)

    C1.  **`prepare_loop` iterates `mult_xdiff_trailing`** — its result is the `n`-fold
         composition of the banked `xdiffStep` step (one `(x − xs[i])` multiply each),
         i.e. it builds `∏_{i<n}(x − xs[i])`. (about `gf.prepare`/`gf.prepare_loop`)

  These need NO field laws — they are exact "what value the loop computes" specs, the
  same proof shape as the banked specs. They are real, in-boundary results ABOUT the
  extracted interpolation loops and are registered as headlines.

  ## What this file does NOT do (the honest open obligations)

  - Connecting these recurrences to Mathlib's `Lagrange.interpolate` (hence the
    unconditional `decode ∘ encode = id` about `gf.decode_value_at`) requires the
    GF(2¹⁶) FIELD instance — the documented gap in `Gf16Field.lean` (irreducibility of
    POLY + the clmul/reduce multiplicative characterization).
  - `gf.complete`'s long-division loop (`complete_loop1`) and the full assembly of
    `gf.lagrange_interpolate` are characterized only at the loop level here.
-/
import Demos.Spqr.Gf

open Aeneas Std Result
open Spqr.Gf

namespace Spqr.RsInterp

/-! ### C2a. `complete_loop0` computes the denominator product over the field. -/

/-- The running denominator product `complete_loop0` computes. Mirrors the loop body
EXACTLY: started at accumulator `denom` and index `j`, each step multiplies in one more
factor `gfAddV pix xs[j]` (i.e. `pix ⊕ xs[j]`) **iff** `pix ≠ xs[j]`, leaving `denom`
unchanged otherwise, incrementing `j` until it reaches `n`. -/
def denomV (xs : Array Std.U16 36#usize) (n : Std.Usize) (pix : Std.U16) :
    Std.U16 → Nat → Std.U16
  | denom, j =>
    if j < n.val then
      let denom' := if pix ≠ xs.val[j]! then gfMulV denom (gfAddV pix xs.val[j]!) else denom
      denomV xs n pix denom' (j + 1)
    else denom
  termination_by _ j => n.val - j
  decreasing_by rename_i h; omega

/-- **Denominator-product value spec of `complete`'s first loop.** `complete_loop0`
computes exactly the pure fold `denomV`: started from accumulator `denom` and index `j`,
it returns `denomV xs n pix denom j.val`. Field-law-free — it pins exactly which `gfMulV`
of `gfAddV pix xs[j]` factors (over the `pix ≠ xs[j]` filter) the loop forms. -/
theorem complete_loop0_eq (xs : Array Std.U16 36#usize) (n : Std.Usize) (pix : Std.U16)
    (hn : n.val ≤ 36) :
    ∀ (denom : Std.U16) (j : Std.Usize),
      gf.complete_loop0 xs n pix denom j
        ⦃ r => r = denomV xs n pix denom j.val ⦄ := by
  intro denom j
  unfold gf.complete_loop0
  apply Std.loop.spec_decr_nat
    (measure := fun s : Std.U16 × Std.Usize => n.val - s.2.val)
    (inv := fun s : Std.U16 × Std.Usize =>
      denomV xs n pix s.1 s.2.val = denomV xs n pix denom j.val)
    (post := fun r : Std.U16 => r = denomV xs n pix denom j.val)
  · rintro ⟨d1, j1⟩ hinv
    simp only [gf.complete_loop0.body]
    split
    · rename_i hlt
      step as ⟨xj, hxj⟩
      -- the conditional multiply
      split
      · rename_i hne
        rw [gf_add_eq]
        simp only [Std.bind_tc_ok]
        rw [gf_mul_eq]
        step as ⟨j2, hj2⟩
        refine ⟨?_, by scalar_tac⟩
        simp only [hinv.symm]
        conv_rhs => rw [denomV]
        rw [if_pos (by scalar_tac)]
        simp only [hj2]
        have hne' : pix ≠ xs.val[j1.val]! := by
          rw [← hxj]; simp only [bne_iff_ne] at hne; exact hne
        rw [if_pos hne', hxj]
      · rename_i heq
        step as ⟨j2, hj2⟩
        refine ⟨?_, by scalar_tac⟩
        simp only [hinv.symm]
        conv_rhs => rw [denomV]
        rw [if_pos (by scalar_tac)]
        simp only [hj2]
        have heq' : pix = xs.val[j1.val]! := by
          simp only [bne_iff_ne, not_not] at heq
          rw [← hxj]; exact heq
        rw [if_neg (not_not.mpr heq')]
    · rename_i hge
      have h : ¬ j1.val < n.val := by scalar_tac
      conv at hinv => rw [denomV, if_neg h]
      exact hinv
  · rfl

/-- **Entry-point spec.** `gf.complete`'s denominator loop started at `denom = 1`, `j = 0`
succeeds with `denomV xs n pix 1#u16 0` — the field product `∏_{j<n, pix≠xs[j]} (pix ⊕ xs[j])`. -/
theorem complete_loop0_eq0 (xs : Array Std.U16 36#usize) (n : Std.Usize) (pix : Std.U16)
    (hn : n.val ≤ 36) :
    gf.complete_loop0 xs n pix 1#u16 0#usize
      ⦃ r => r = denomV xs n pix 1#u16 0 ⦄ :=
  complete_loop0_eq xs n pix hn 1#u16 0#usize

/-! ### C2b. `complete_loop1` is the scale-and-carry long-division sweep. -/

/-- One step of the long-division sweep `complete_loop1.body` does, as a pure
function on the coefficient-reading function `c`, at write index `idx`:
  * `out[idx]   ↦ gfMulV (c idx) scale`     (finalize the leading coefficient), and
  * `out[idx-1] ↦ gfAddV (c (idx-1)) (gfMulV (c idx) pix)`  (carry the negative delta),
leaving every other coefficient unchanged. `scale`/`pix` are kept as VALUES (the
extracted `gf_div piy denominator` and the node `xs[i]`), so this is field-law-free —
it pins exactly the `gfMulV`/`gfAddV` combination the body forms, using the ORIGINAL
`c idx` for both writes (matching the body, which reads `out[idx]` once into `i`). -/
def divStepFn (pix scale : Std.U16) (c : Nat → Std.U16) (idx : Nat) : Nat → Std.U16 :=
  fun m =>
    if m = idx then gfMulV (c idx) scale
    else if m = idx - 1 then gfAddV (c (idx - 1)) (gfMulV (c idx) pix)
    else c m

/-- The pure functional model of `complete_loop1`: from coefficient function `c` and
loop index `j2`, each step applies one `divStepFn` at write index `idx = len - j2`, then
increments `j2`, until `j2` reaches `len`. Mirrors `gf.complete_loop1.body` line for line. -/
def divFold (pix scale : Std.U16) (len : Nat) :
    (Nat → Std.U16) → Nat → (Nat → Std.U16)
  | c, j2 =>
    if j2 < len then
      divFold pix scale len (divStepFn pix scale c (len - j2)) (j2 + 1)
    else c
  termination_by _ j2 => len - j2
  decreasing_by rename_i h; omega

/-- **Value spec of `complete`'s long-division loop.** For `len ≤ 37` and `1 ≤ j2`,
`complete_loop1 out pix scale len j2` produces an array whose every coefficient
`m < 37` equals `divFold pix scale len (out.val[·]!) j2 m` — the scale-and-carry sweep:
each step `idx = len - j2` sets `out[idx] = gfMulV out[idx] scale` and
`out[idx-1] = gfAddV out[idx-1] (gfMulV out[idx] pix)`. Field-law-free; `scale` and `pix`
are opaque values (`scale = gf_div piy denominator`). -/
theorem complete_loop1_eq (pix scale : Std.U16) (len : Std.Usize) (hlen : len.val ≤ 37) :
    ∀ (out : Array Std.U16 37#usize) (j2 : Std.Usize), 1 ≤ j2.val → j2.val ≤ len.val →
      gf.complete_loop1 out pix scale len j2
        ⦃ r => ∀ m, m < 37 →
                 r.val[m]! = divFold pix scale len.val (fun k => out.val[k]!) j2.val m ⦄ := by
  intro out j2 hj2 hj2l
  unfold gf.complete_loop1
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U16 37#usize) × Std.Usize => len.val - s.2.val)
    (inv := fun s : (Array Std.U16 37#usize) × Std.Usize =>
      1 ≤ s.2.val ∧ s.2.val ≤ len.val ∧
      (∀ m, m < 37 →
        divFold pix scale len.val (fun k => s.1.val[k]!) s.2.val m
          = divFold pix scale len.val (fun k => out.val[k]!) j2.val m))
    (post := fun r : Array Std.U16 37#usize =>
      ∀ m, m < 37 →
        r.val[m]! = divFold pix scale len.val (fun k => out.val[k]!) j2.val m)
  · rintro ⟨o1, j21⟩ ⟨hj21, hj21l, hinv⟩
    simp only [gf.complete_loop1.body]
    split
    · rename_i hlt
      step as ⟨idx, hidx⟩
      step as ⟨vi, hvi⟩
      rw [gf_mul_eq]                 -- negative_delta = gfMulV vi pix
      rw [gf_mul_eq]                 -- i1 = gfMulV vi scale
      step as ⟨o2, ho2⟩              -- out1 = o1[idx := gfMulV vi scale]
      step as ⟨i2, hi2⟩
      step as ⟨vi3, hvi3⟩
      rw [gf_add_eq]                 -- i4 = gfAddV vi3 (gfMulV vi pix)
      step as ⟨a, ha⟩
      step as ⟨j22, hj22⟩
      refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
      intro m hm
      -- Relate the post-step array `a` (= o1 updated at idx and idx-1) to one divStepFn,
      -- pointwise for EVERY index `k` (out-of-range slots default to 0 on both sides).
      have hidxv : idx.val = len.val - j21.val := hidx
      have hi2v : i2.val = idx.val - 1 := hi2
      have hvi3v : vi3 = o1.val[idx.val - 1]! := by
        rw [hvi3, ho2, hi2v]
        have hne : idx.val - 1 ≠ idx.val := by scalar_tac
        simp_lists
      have key : ∀ k, a.val[k]! = divStepFn pix scale (fun k => o1.val[k]!) idx.val k := by
        intro k
        simp only [divStepFn]
        subst ha
        by_cases h1 : k = idx.val
        · -- k = idx: set by `o2` (= vi*scale), and the idx-1 write doesn't touch idx.
          subst h1
          rw [if_pos rfl]
          have hne : idx.val ≠ i2.val := by scalar_tac
          simp_lists
          rw [ho2]
          simp_lists
          rw [hvi]
        · by_cases h2 : k = idx.val - 1
          · -- k = idx-1: set by `a` to gfAddV o1[idx-1] (gfMulV vi pix).
            have hki2 : k = i2.val := by rw [hi2v]; exact h2
            rw [if_neg h1, if_pos h2, hki2]
            simp_lists
            rw [hvi3v, hvi]
          · -- k untouched: a[k] = o2[k] = o1[k].
            rw [if_neg h1, if_neg h2]
            have hki2 : k ≠ i2.val := by rw [hi2v]; exact h2
            simp_lists
            rw [ho2]
            have hne : k ≠ idx.val := h1
            simp_lists
      -- one-step unfolding of divFold on the LHS, then close with the invariant.
      have hfun : (fun k => a.val[k]!)
          = divStepFn pix scale (fun k => o1.val[k]!) (len.val - j21.val) := by
        funext k; rw [key k, hidxv]
      have hstep : divFold pix scale len.val (fun k => a.val[k]!) j22.val m
          = divFold pix scale len.val (fun k => o1.val[k]!) j21.val m := by
        conv_rhs => rw [divFold, if_pos (by scalar_tac)]
        rw [hfun, hj22]
      rw [hstep]
      exact hinv m hm
    · rename_i hge
      intro m hm
      have := hinv m hm
      rw [divFold, if_neg (by scalar_tac)] at this
      exact this
  · refine ⟨hj2, hj2l, fun m _ => rfl⟩

/-- The extracted Fermat-inverse division, read as a pure `u16 → u16 → u16` (the value
of the `Result`, or `0#u16` on the never-taken failure branch). Kept OPAQUE — a value
spec for `complete` never needs the field laws governing it. -/
def gfDivV (numer denom : Std.U16) : Std.U16 :=
  match gf.gf_div numer denom with
  | .ok c => c
  | _ => 0#u16

theorem gf_div_eq (numer denom : Std.U16) : gf.gf_div numer denom = .ok (gfDivV numer denom) := by
  have := gf_div_total numer denom
  unfold gfDivV
  cases h : gf.gf_div numer denom with
  | ok c => rfl
  | div => simp [h] at this
  | fail e => simp [h] at this

/-- **Value spec of `gf.complete`** (one Lagrange basis term). For `n ≤ 36` and `i < n`,
`gf.complete coeffs xs ys n i` runs the long-division sweep `divFold` on `coeffs` with
the EXACT extracted parameters: `pix = xs[i]`, `len = n+1`, `j2` starting at `1`, and
`scale = gfDivV ys[i] (denomV xs n xs[i] 1 0)` — the Lagrange coefficient
`ys[i] / ∏_{j<n, xs[j]≠xs[i]} (xs[i] ⊕ xs[j])` (the denominator product is the banked
`denomV`, the division kept as the opaque value `gfDivV`). Field-law-free. -/
theorem complete_eq (coeffs : Array Std.U16 37#usize) (xs ys : Array Std.U16 36#usize)
    (n i : Std.Usize) (hn : n.val ≤ 36) (hi : i.val < n.val) :
    gf.complete coeffs xs ys n i
      ⦃ r => ∀ m, m < 37 →
               r.val[m]! = divFold xs.val[i.val]!
                 (gfDivV ys.val[i.val]! (denomV xs n xs.val[i.val]! 1#u16 0))
                 (n.val + 1) (fun k => coeffs.val[k]!) 1 m ⦄ := by
  unfold gf.complete
  step as ⟨pix, hpix⟩
  step as ⟨piy, hpiy⟩
  have hloop0 := complete_loop0_eq0 xs n pix hn
  step with hloop0 as ⟨denom, hdenom⟩
  rw [gf_div_eq]
  simp only [Std.bind_tc_ok]                 -- substitute scale := gfDivV piy denom
  step as ⟨len, hlen⟩                        -- len = n+1
  have hlen37 : len.val ≤ 37 := by scalar_tac
  have hloop1 := complete_loop1_eq pix (gfDivV piy denom) len hlen37 coeffs 1#usize
    (by scalar_tac) (by scalar_tac)
  step with hloop1 as ⟨r, hr⟩
  rename_i m hm
  rw [hr m hm]
  -- rewrite the extracted parameters to the closed-form ones
  have hlenv : len.val = n.val + 1 := by scalar_tac
  rw [hlenv, hpix, hdenom, hpix, hpiy]

/-! ### C3a. `lagrange_interpolate_loop0` copies `working[k+1] → out[k]`. -/

/-- **Value spec of the copy loop.** `lagrange_interpolate_loop0` shifts `working` down by
one coefficient into `out`: every slot `k < n` of the result equals `working[k+1]`, and
every slot `k ≥ n` is preserved from the incoming `out`. This is the "divide-by-x" /
drop-the-lowest-coefficient copy. Field-law-free (a pure array shift). -/
theorem lagrange_interpolate_loop0_eq (n : Std.Usize) (working : Array Std.U16 37#usize)
    (hn : n.val ≤ 36) :
    ∀ (out : Array Std.U16 37#usize) (k : Std.Usize), k.val ≤ n.val →
      (∀ m, m < k.val → out.val[m]! = working.val[m + 1]!) →
      gf.lagrange_interpolate_loop0 n out working k
        ⦃ r => (∀ m, m < n.val → r.val[m]! = working.val[m + 1]!) ∧
               (∀ m, n.val ≤ m → m < 37 → r.val[m]! = out.val[m]!) ⦄ := by
  intro out k hk hpre
  unfold gf.lagrange_interpolate_loop0
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U16 37#usize) × Std.Usize => n.val - s.2.val)
    (inv := fun s : (Array Std.U16 37#usize) × Std.Usize =>
      k.val ≤ s.2.val ∧ s.2.val ≤ n.val ∧
      (∀ m, m < s.2.val → s.1.val[m]! = working.val[m + 1]!) ∧
      (∀ m, n.val ≤ m → m < 37 → s.1.val[m]! = out.val[m]!))
    (post := fun r : Array Std.U16 37#usize =>
      (∀ m, m < n.val → r.val[m]! = working.val[m + 1]!) ∧
      (∀ m, n.val ≤ m → m < 37 → r.val[m]! = out.val[m]!))
  · rintro ⟨o1, k1⟩ ⟨hk1, hk1n, hbelow, habove⟩
    simp only [gf.lagrange_interpolate_loop0.body]
    split
    · rename_i hlt
      step as ⟨i1, hi1⟩
      step as ⟨w1, hw1⟩
      step as ⟨o2, ho2⟩
      refine ⟨by scalar_tac, by scalar_tac, ?_, ?_, by scalar_tac⟩
      · -- below region after writing slot `k1`
        intro m hm
        subst ho2
        by_cases hme : m = k1.val
        · subst hme; simp_lists; rw [hw1, hi1]
        · have : m < k1.val := by scalar_tac
          simp_lists; exact hbelow m this
      · -- above region: the write at `k1 < n` doesn't touch `m ≥ n`
        intro m hmn hm37
        subst ho2
        have : m ≠ k1.val := by scalar_tac
        simp_lists; exact habove m hmn hm37
    · rename_i hge
      have hke : k1.val = n.val := by scalar_tac
      refine ⟨?_, habove⟩
      intro m hm; apply hbelow; scalar_tac
  · exact ⟨_root_.le_refl _, hk, hpre, fun m _ _ => rfl⟩

/-! ### C3b. `lagrange_interpolate_loop1_loop0` accumulates `out[j] ⊕= working[j+1]`. -/

/-- **Value spec of the accumulate loop.** `lagrange_interpolate_loop1_loop0` folds one
`complete` result (`working`, shifted down by one coefficient) into the running sum `out`:
every slot `j < n` of the result becomes `gfAddV out[j] working[j+1] = out[j] ⊕ working[j+1]`,
and every slot `j ≥ n` is preserved. Field-law-free `gfAddV` accumulation. -/
theorem lagrange_interpolate_loop1_loop0_eq (n : Std.Usize) (working : Array Std.U16 37#usize)
    (hn : n.val ≤ 36) :
    ∀ (out : Array Std.U16 37#usize) (j : Std.Usize), j.val ≤ n.val →
      gf.lagrange_interpolate_loop1_loop0 n out working j
        ⦃ r => (∀ m, j.val ≤ m → m < n.val →
                  r.val[m]! = gfAddV (out.val[m]!) (working.val[m + 1]!)) ∧
               (∀ m, m < j.val → r.val[m]! = out.val[m]!) ∧
               (∀ m, n.val ≤ m → m < 37 → r.val[m]! = out.val[m]!) ⦄ := by
  intro out j hj
  unfold gf.lagrange_interpolate_loop1_loop0
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U16 37#usize) × Std.Usize => n.val - s.2.val)
    (inv := fun s : (Array Std.U16 37#usize) × Std.Usize =>
      j.val ≤ s.2.val ∧ s.2.val ≤ n.val ∧
      (∀ m, j.val ≤ m → m < s.2.val →
        s.1.val[m]! = gfAddV (out.val[m]!) (working.val[m + 1]!)) ∧
      (∀ m, m < j.val → s.1.val[m]! = out.val[m]!) ∧
      (∀ m, s.2.val ≤ m → m < 37 → s.1.val[m]! = out.val[m]!))
    (post := fun r : Array Std.U16 37#usize =>
      (∀ m, j.val ≤ m → m < n.val →
        r.val[m]! = gfAddV (out.val[m]!) (working.val[m + 1]!)) ∧
      (∀ m, m < j.val → r.val[m]! = out.val[m]!) ∧
      (∀ m, n.val ≤ m → m < 37 → r.val[m]! = out.val[m]!))
  · rintro ⟨o1, j1⟩ ⟨hj1, hj1n, hacc, hbelow, habove⟩
    simp only [gf.lagrange_interpolate_loop1_loop0.body]
    split
    · rename_i hlt
      step as ⟨vj, hvj⟩
      step as ⟨i1, hi1⟩
      step as ⟨w1, hw1⟩
      rw [gf_add_eq]
      step as ⟨o2, ho2⟩
      refine ⟨by scalar_tac, by scalar_tac, ?_, ?_, ?_, by scalar_tac⟩
      · -- accumulated region: slot `j1` newly written, earlier slots already accumulated
        intro m hjm hm
        subst ho2
        by_cases hme : m = j1.val
        · subst hme
          simp_lists
          rw [hw1, hi1, hvj]
          -- o1[j1] = out[j1] since j1 ≥ j and < j1's accumulated region is empty... use habove
          rw [habove j1.val (by scalar_tac) (by scalar_tac)]
        · have hmlt : m < j1.val := by scalar_tac
          simp_lists; exact hacc m hjm hmlt
      · -- below `j1`: preserved (untouched by the write at `j1`)
        intro m hm
        subst ho2
        have : m ≠ j1.val := by scalar_tac
        simp_lists; exact hbelow m (by scalar_tac)
      · -- above region recharacterized at `j1+1`: write at `j1`, so for m > j1 unchanged
        intro m hmn hm37
        subst ho2
        have : m ≠ j1.val := by scalar_tac
        simp_lists; exact habove m (by scalar_tac) hm37
    · rename_i hge
      have hje : j1.val = n.val := by scalar_tac
      refine ⟨?_, hbelow, ?_⟩
      · intro m hjm hmn; exact hacc m hjm (by scalar_tac)
      · intro m hmn hm37; exact habove m (by scalar_tac) hm37
  · refine ⟨_root_.le_refl _, hj, ?_, fun m _ => rfl, fun m _ _ => rfl⟩
    intro m hjm hmj; exact absurd hmj (by scalar_tac)

/-! ### C1. `gf.prepare` iterates `mult_xdiff_trailing` (= `xdiffStep`) `n` times. -/

/-- The window-update of one `mult_xdiff_trailing` step (the banked `Spqr.Gf.xdiffStep`),
read as a transform on a COEFFICIENT-FUNCTION `c : Nat → U16` rather than an array — over
the window `start-1 ≤ j < len-1`, coefficient `j` becomes `c j ⊕ gfMulV (c (j+1)) difference`,
elsewhere unchanged. This is exactly the closed form `mult_xdiff_trailing_eq` proves. -/
def xdiffStepFn (len start : Nat) (difference : Std.U16) (c : Nat → Std.U16) : Nat → Std.U16 :=
  fun j =>
    if start - 1 ≤ j ∧ j < len - 1 then c j ^^^ gfMulV (c (j + 1)) difference
    else c j

/-- The pure functional model of `prepare_loop`: from coefficient function `c` and loop
index `i`, each step applies one `xdiffStepFn` with the EXACT extracted parameters
`len = n+1`, `start = n-i`, `difference = xs[i]`, then increments `i`, until `i` reaches
`n`. Mirrors `gf.prepare_loop.body` line for line — the `n`-fold `(x − xs[i])` multiply
that builds `∏_{i<n}(x − xs[i])`. -/
def prepareFoldFn (xs : Array Std.U16 36#usize) (n : Std.Usize) :
    (Nat → Std.U16) → Nat → (Nat → Std.U16)
  | c, i =>
    if i < n.val then
      prepareFoldFn xs n (xdiffStepFn (n.val + 1) (n.val - i) xs.val[i]! c) (i + 1)
    else c
  termination_by _ i => n.val - i
  decreasing_by rename_i h; omega

/-- **Value spec of `prepare_loop`.** For `n ≤ 36`, started from coefficient function `c`
at index `i`, the loop produces an array whose every coefficient `j < 37` equals
`prepareFoldFn xs n c i j` — the iterated `xdiffStepFn` fold (each iteration one
`(x − xs[i])` multiply, the banked `mult_xdiff_trailing_eq`/`xdiffStep`). Field-law-free. -/
theorem prepare_loop_eq (xs : Array Std.U16 36#usize) (n : Std.Usize) (hn : n.val ≤ 36) :
    ∀ (p : Array Std.U16 37#usize) (i : Std.Usize), i.val ≤ n.val →
      gf.prepare_loop xs n p i
        ⦃ r => ∀ j, j < 37 → r.val[j]! = prepareFoldFn xs n (fun k => p.val[k]!) i.val j ⦄ := by
  intro p i hi
  unfold gf.prepare_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U16 37#usize) × Std.Usize => n.val - s.2.val)
    (inv := fun s : (Array Std.U16 37#usize) × Std.Usize =>
      s.2.val ≤ n.val ∧
      (∀ j, j < 37 →
        prepareFoldFn xs n (fun k => s.1.val[k]!) s.2.val j
          = prepareFoldFn xs n (fun k => p.val[k]!) i.val j))
    (post := fun r : Array Std.U16 37#usize =>
      ∀ j, j < 37 → r.val[j]! = prepareFoldFn xs n (fun k => p.val[k]!) i.val j)
  · rintro ⟨p1, i1⟩ ⟨hi1n, hinv⟩
    simp only [gf.prepare_loop.body]
    split
    · rename_i hlt
      step as ⟨len, hlen⟩            -- len = n+1
      step as ⟨st, hst⟩             -- st = n - i1
      step as ⟨xi, hxi⟩             -- xi = xs[i1]
      -- the inner `mult_xdiff_trailing` is the banked window-update `xdiffStep`.
      have hmx := mult_xdiff_trailing_eq p1 len st xi (by scalar_tac) (by scalar_tac)
        (by scalar_tac)
      step with hmx as ⟨p2, hp2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      intro j hj
      -- one-step unfold of prepareFoldFn at state (p1, i1), feeding in the xdiffStep window.
      have hfun : (fun k => p2.val[k]!)
          = xdiffStepFn (n.val + 1) (n.val - i1.val) xs.val[i1.val]! (fun k => p1.val[k]!) := by
        funext k
        unfold xdiffStepFn
        by_cases hk37 : k < 37
        · rw [hp2 k hk37]
          unfold Spqr.Gf.xdiffStep
          rw [hlen, hst, hxi]
        · -- out-of-range (k ≥ 37 > n-1): both sides read the array default; window misses k.
          have hwin : ¬ ((n.val - i1.val) - 1 ≤ k ∧ k < (n.val + 1) - 1) := by
            rintro ⟨_, h2⟩; omega
          rw [if_neg hwin]
          simp_lists
      rw [← hinv j hj]
      conv_rhs => rw [prepareFoldFn, if_pos (by scalar_tac)]
      rw [hfun, hi2]
    · rename_i hge
      intro j hj
      have := hinv j hj
      rw [prepareFoldFn, if_neg (by scalar_tac)] at this
      exact this
  · exact ⟨hi, fun j _ => rfl⟩

/-- The initial coefficient function `gf.prepare` folds over: the constant polynomial
`1` placed at index `n` (`p[n] = 1`, all else `0`) — the start of `∏(x − xs[i])`. -/
def prepareInit (n : Std.Usize) : Nat → Std.U16 := fun k => if k = n.val then 1#u16 else 0#u16

/-- **Value spec of `gf.prepare`** (`PRODUCT(x − xs[i])`). For `n ≤ 36`, `gf.prepare xs n`
succeeds with an array whose every coefficient `j < 37` equals
`prepareFoldFn xs n (prepareInit n) 0 j` — the `n`-fold `xdiffStepFn` of the delta array
`[0,…,0,1,0,…]` (a `1` at index `n`), each iteration one `(x − xs[i])` multiply (the banked
`mult_xdiff_trailing_eq`). This is the in-boundary value characterization of the extracted
`gf.prepare` that the SCKA decoder's basis-polynomial construction rests on; field-law-free. -/
theorem prepare_eq (xs : Array Std.U16 36#usize) (n : Std.Usize) (hn : n.val ≤ 36) :
    gf.prepare xs n
      ⦃ r => ∀ j, j < 37 → r.val[j]! = prepareFoldFn xs n (prepareInit n) 0 j ⦄ := by
  unfold gf.prepare
  step as ⟨a, ha⟩
  have hloop := prepare_loop_eq xs n hn a 0#usize (by scalar_tac)
  step with hloop as ⟨r, hr⟩
  rename_i j hj
  rw [hr j hj]
  -- the loop's initial coefficient function is `prepareInit n`.
  have hinit : (fun k => a.val[k]!) = prepareInit n := by
    funext k
    unfold prepareInit
    subst ha
    by_cases hkn : k = n.val
    · subst hkn; simp_lists
    · simp_lists
      rw [if_neg hkn]
      -- `Array.repeat 37 0` reads `0` at every index.
      rcases Nat.lt_or_ge k 37 with h | h
      · rw [show (Array.repeat 37#usize 0#u16).val = List.replicate 37 0#u16 from rfl,
          List.getElem!_replicate]; exact h
      · rw [show (Array.repeat 37#usize 0#u16).val = List.replicate 37 0#u16 from rfl,
          List.getElem!_eq_getElem?_getD, List.getElem?_eq_none (by simpa using h)]; rfl
  rw [hinit]

end Spqr.RsInterp
