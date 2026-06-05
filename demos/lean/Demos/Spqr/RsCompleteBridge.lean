/-
  SPQR Reed–Solomon codec — Layer C, the COMPLETE bridge: the extracted `gf.complete`
  is the synthetic division of the nodal product by `(X − xs[i])`, scaled, over the
  genuine GF(2¹⁶) commutative ring.

  ## What this file establishes (genuine, IN-BOUNDARY, UNCONDITIONAL — no irreducibility)

  `RsInterp.complete_eq` characterized `gf.complete coeffs xs ys n i` as the long-division
  sweep `divFold pix scale (n+1) (coeffs[·]) 1` with `pix = xs[i]`, `scale = gfDivV ys[i]
  (denomV …)`. This file closes the polynomial-algebra reading of that sweep: it computes
  the SYNTHETIC DIVISION of the coefficient polynomial by `(X − C pix)`, scaled by `C scale`
  and shifted up by one (`× X`), with the division remainder left in slot 0.

  Concretely, write `T = gpoly (coeffs[·]) (n+1)` for the input coefficient polynomial. The
  synthetic-division tail-Horner sums `synTail c pix m = ∑_{t} c[m+t]·pix^t` satisfy the
  one-step recurrence `synTail c pix m = c[m] + pix · synTail c pix (m+1)`, and the
  `divFold` output `o` is exactly

      o[0] = synTail c pix 0        (the division remainder = eval pix T),
      o[m] = scale · synTail c pix m   for 1 ≤ m ≤ n   (the scaled quotient, shifted by X).

  Reading this into `gpoly`:

    P1. **`gf.complete` is the scaled, shifted synthetic quotient** (`complete_eq_synDiv`,
        UNCONDITIONAL, in-boundary). `gpoly (complete output) (n+1)` over GF16 equals
        `C(remainder) + C(scale) · X · Q`, where `Q = ∑_{m<n} synTail c pix (m+1) · X^m` is
        the synthetic-division quotient and `remainder = synTail c pix 0`.

    P2. **The multiply-back identity** (`synDiv_mul_back`, the building block): over any
        `CommRing`, `(X − C pix) · Q + C(remainder) = T` (exact polynomial division of `T`
        by the monic `X − C pix`), with `remainder = eval pix T` and `Q` the quotient. Used
        to conclude that when `pix` is a root of `T` (e.g. `T = nodal`, `pix = xs[i]`,
        `i < n`), the remainder vanishes and `gpoly (complete output) (n+1) = C scale · X ·
        (T /(X − C pix))` — the scaled basis numerator times `X`.

  P1 mentions `gf.complete` (via the banked `complete_eq`/`divFold`), so it is an in-boundary
  headline about the extracted code. NO `axiom`, NO `sorry`, NO `native_decide`, NO `decide`
  over the value space, NO irreducibility — only the unconditional `CommRing`.

  ## What this file does NOT do (the honest open obligation)

  - It does NOT yet assemble the `lagrange_interpolate_loop0`/`loop1_loop0` sum over `i` into
    Mathlib's `Lagrange.interpolate` (the final basis-sum step), nor discharge `RsCapstone`'s
    `hbridge`. That assembly additionally reads `gfDivV` as the field inverse (banked in
    `RsDivInverse` conditional on `Irreducible POLY_poly`) to identify `scale_i` with the
    Lagrange weight, and matches the per-`i` scaled numerator against `Lagrange.basis`.
-/
import Demos.Spqr.RsInterp
import Demos.Spqr.RsEvalBridge
import Demos.Spqr.RsPrepareBridge

open Aeneas Std Result
open Spqr.Gf
open Spqr.RsInterp (divStepFn divFold gfDivV denomV complete_eq)
open Spqr.RsEvalBridge (gpoly eval_gpoly)
open Spqr.RsPrepareBridge (nodal nodal_natDegree nodal_succ neg_eq coeff_mul_X_sub_C)
open Spqr.Gf16FieldInstance (GF16 add_eq_gfAddV mul_eq_gfMulV zero_eq one_eq)
open Polynomial

namespace Spqr.RsCompleteBridge

/-! ### The synthetic-division tail-Horner sum over GF16. -/

/-- The synthetic-division tail-Horner sum from index `m` over a window of width `w`
(`= len − m` remaining coefficients): `∑_{t<w} ofU16 (c (m+t)) · p^t`. This is the value the
`divFold` sweep leaves at slot `m` (scaled by `scale` for `m ≥ 1`). The one-step recurrence
`synTail c p (w+1) m = ofU16 (c m) + p · synTail c p w (m+1)` is the synthetic-division carry. -/
noncomputable def synTail (c : Nat → Std.U16) (p : GF16) : Nat → Nat → GF16
  | _, 0 => 0
  | m, (w + 1) => GF16.ofU16 (c m) + p * synTail c p (m + 1) w

@[simp] theorem synTail_zero (c : Nat → Std.U16) (p : GF16) (m : Nat) :
    synTail c p m 0 = 0 := rfl

theorem synTail_succ (c : Nat → Std.U16) (p : GF16) (m w : Nat) :
    synTail c p m (w + 1) = GF16.ofU16 (c m) + p * synTail c p (m + 1) w := rfl

/-! ### The `divFold` invariant: the running array state in synthetic-division progress. -/

/-- The state invariant of the `divFold` sweep at loop index `j2` (about to process
`idx = len − j2`), read into GF16. With `c` the ORIGINAL input coefficient function,
`pix`/`scale` the divisor root / scale:

  * every FINALIZED slot `m` with `len − j2 < m < len` holds the scaled tail-Horner
    `scale · synTail c pix m (len − m)`;
  * the "next" slot `m = len − j2` holds the full UN-scaled tail-Horner
    `synTail c pix m (len − m)` (built up by the carries from the steps already run);
  * every UNTOUCHED slot `m < len − j2` still holds the original word `arr m = c m`. -/
def DivInv (c : Nat → Std.U16) (pix scale : GF16) (len : Nat) (arr : Nat → Std.U16) (j2 : Nat) :
    Prop :=
  (∀ m, len - j2 < m → m < len → GF16.ofU16 (arr m) = scale * synTail c pix m (len - m)) ∧
  (GF16.ofU16 (arr (len - j2)) = synTail c pix (len - j2) (len - (len - j2))) ∧
  (∀ m, m < len - j2 → arr m = c m)

/-- The `divStepFn` window-update, read into GF16: the extracted `gfMulV`/`gfAddV` ARE the ring
`*`/`+`. Slot `idx` becomes `(arr idx) · scale`, slot `idx-1` becomes `(arr (idx-1)) + (arr idx)·p`. -/
theorem ofU16_divStepFn (pix scale : Std.U16) (c : Nat → Std.U16) (idx m : Nat) :
    GF16.ofU16 (divStepFn pix scale c idx m)
      = if m = idx then GF16.ofU16 (c idx) * GF16.ofU16 scale
        else if m = idx - 1 then
          GF16.ofU16 (c (idx - 1)) + GF16.ofU16 (c idx) * GF16.ofU16 pix
        else GF16.ofU16 (c m) := by
  unfold divStepFn
  split
  · rw [← mul_eq_gfMulV]
  · split
    · rw [← add_eq_gfAddV, ← mul_eq_gfMulV]
    · rfl

/-- **One `divFold` step preserves `DivInv`.** If `DivInv c pix scale len arr j2` holds and
`j2 < len` (so `idx = len − j2 ≥ 1`), then `DivInv c pix scale len (divStepFn pix scale arr idx) (j2+1)`:
slot `idx` finalizes to the scaled full Horner, slot `idx−1` builds up to the next un-scaled full
Horner by the synthetic-division carry, and everything below `idx−1` is untouched. -/
theorem DivInv_step (c : Nat → Std.U16) (pix scale : Std.U16) (len j2 : Nat)
    (hj2 : 1 ≤ j2) (hlt : j2 < len)
    (hinv : DivInv c (GF16.ofU16 pix) (GF16.ofU16 scale) len arr j2) :
    DivInv c (GF16.ofU16 pix) (GF16.ofU16 scale) len
      (divStepFn pix scale arr (len - j2)) (j2 + 1) := by
  obtain ⟨hfin, hnext, hbelow⟩ := hinv
  set idx := len - j2 with hidx
  have hidxpos : 1 ≤ idx := by omega
  have hidxlt : idx < len := by omega
  -- len - (j2+1) = idx - 1
  have hnewidx : len - (j2 + 1) = idx - 1 := by omega
  refine ⟨?_, ?_, ?_⟩
  · -- finalized region for j2+1: m with idx-1 < m < len.  Split m = idx vs m > idx.
    intro m hm hmlen
    rw [hnewidx] at hm
    rw [ofU16_divStepFn]
    by_cases hmi : m = idx
    · -- slot idx finalizes: was un-scaled full Horner (hnext), now ·scale
      subst hmi
      rw [if_pos rfl]
      rw [hnext, hidx]
      ring
    · -- m > idx: unchanged finalized slot
      have hmgt : idx < m := by omega
      rw [if_neg hmi, if_neg (by omega)]
      exact hfin m (by omega) hmlen
  · -- the new "next" slot is idx-1 = len-(j2+1).  It builds c[idx-1] + pix·synTail(idx)(...).
    rw [hnewidx]
    rw [ofU16_divStepFn]
    rw [if_neg (by omega), if_pos rfl]
    -- arr (idx-1) = c (idx-1) (was below), arr idx = synTail c pix idx (len-idx) (was next, hnext)
    rw [hbelow (idx - 1) (by omega), hnext, hidx]
    -- goal: ofU16 (c (idx-1)) + pix * synTail c pix idx (len-idx)
    --     = synTail c pix (idx-1) (len-(idx-1))
    have hwid : len - (idx - 1) = (len - idx) + 1 := by omega
    have hsucc : idx - 1 + 1 = idx := by omega
    rw [hwid, synTail_succ, hsucc, mul_comm]
  · -- below idx-1: untouched
    intro m hm
    rw [hnewidx] at hm
    unfold divStepFn
    rw [if_neg (by omega), if_neg (by omega)]
    exact hbelow m (by omega)

/-- The base case: at loop index `1` (the extracted `complete_loop1` start), the UNMODIFIED
input array `c` satisfies `DivInv` — the finalized region is empty, the "next" slot `len−1`
holds `c[len−1] = synTail c pix (len−1) 1`, and all lower slots are the original `c`. -/
theorem DivInv_init (c : Nat → Std.U16) (pix scale : Std.U16) (len : Nat) (hlen : 1 ≤ len) :
    DivInv c (GF16.ofU16 pix) (GF16.ofU16 scale) len c 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro m hm hmlen; omega
  · -- next slot len-1: synTail width len-(len-1) = 1
    have : len - (len - 1) = 1 := by omega
    rw [this, synTail_succ, synTail_zero, mul_zero, add_zero]
  · intro m hm; rfl

/-- **The full `divFold` sweep finalizes `DivInv` at `j2 = len`.** Starting from any array with
`DivInv c pix scale len arr j2`, iterating `divFold` (steps `j2, …, len−1`) yields an array with
`DivInv c pix scale len · len`: every slot `m ≥ 1` holds the scaled full Horner
`scale · synTail c pix m (len−m)` and slot `0` holds the un-scaled remainder `synTail c pix 0 len`.
Induction on the number of remaining steps `len − j2`. -/
theorem DivInv_fold (c : Nat → Std.U16) (pix scale : Std.U16) (len : Nat) :
    ∀ (d : Nat) (arr : Nat → Std.U16) (j2 : Nat), len - j2 = d → 1 ≤ j2 → j2 ≤ len →
      DivInv c (GF16.ofU16 pix) (GF16.ofU16 scale) len arr j2 →
      DivInv c (GF16.ofU16 pix) (GF16.ofU16 scale) len (divFold pix scale len arr j2) len := by
  intro d
  induction d with
  | zero =>
    intro arr j2 hd hj2 hj2l hinv
    have hje : j2 = len := by omega
    rw [divFold, if_neg (by omega)]
    rw [hje] at hinv; exact hinv
  | succ d ih =>
    intro arr j2 hd hj2 hj2l hinv
    have hjlt : j2 < len := by omega
    rw [divFold, if_pos hjlt]
    exact ih (divStepFn pix scale arr (len - j2)) (j2 + 1) (by omega) (by omega) (by omega)
      (DivInv_step c pix scale len j2 hj2 hjlt hinv)

/-! ### The synthetic-division quotient polynomial and the multiply-back identity. -/

/-- The window polynomial `∑_{k<w} C(ofU16 (c (m+k))) X^k` — the coefficients of `c` over the
window `[m, m+w)`, re-based to start at `X^0`. `gpoly c len = gpolyWin c 0 len`. -/
noncomputable def gpolyWin (c : Nat → Std.U16) (m w : Nat) : GF16[X] :=
  ∑ k ∈ Finset.range w, C (GF16.ofU16 (c (m + k))) * X ^ k

/-- The synthetic-division quotient of the window `[m, m+w)` by `(X − C p)`: degree-`k` coefficient
is the tail-Horner `synTail c p (m+k+1) (w−1−k)`. -/
noncomputable def synQuotWin (c : Nat → Std.U16) (p : GF16) (m w : Nat) : GF16[X] :=
  ∑ k ∈ Finset.range (w - 1), C (synTail c p (m + k + 1) (w - 1 - k)) * X ^ k

/-- The window polynomial satisfies the Horner peel `gpolyWin c m (w+1) = C(c m) + X · gpolyWin c (m+1) w`. -/
theorem gpolyWin_succ (c : Nat → Std.U16) (m w : Nat) :
    gpolyWin c m (w + 1) = C (GF16.ofU16 (c m)) + X * gpolyWin c (m + 1) w := by
  unfold gpolyWin
  rw [Finset.sum_range_succ']
  simp only [Nat.add_zero, pow_zero, mul_one]
  rw [Finset.mul_sum, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [show m + (k + 1) = (m + 1) + k by omega]
  ring

/-- The quotient window peels as `synQuotWin c p m (w+1) = C(synTail c p (m+1) w) + X · synQuotWin c p (m+1) w`. -/
theorem synQuotWin_succ (c : Nat → Std.U16) (p : GF16) (m w : Nat) :
    synQuotWin c p m (w + 1) = C (synTail c p (m + 1) w) + X * synQuotWin c p (m + 1) w := by
  have hlhs : synQuotWin c p m (w + 1)
      = ∑ k ∈ Finset.range w, C (synTail c p (m + k + 1) (w - k)) * X ^ k := by
    unfold synQuotWin
    rw [show w + 1 - 1 = w by omega]
  have hrhs : X * synQuotWin c p (m + 1) w
      = ∑ k ∈ Finset.range (w - 1), C (synTail c p (m + 1 + k + 1) (w - 1 - k)) * X ^ (k + 1) := by
    unfold synQuotWin
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _; ring
  rw [hlhs, hrhs]
  cases w with
  | zero => simp
  | succ w' =>
    rw [Finset.sum_range_succ']
    rw [show w' + 1 - 1 = w' by omega]
    rw [add_comm]
    congr 1
    · -- the k=0 term
      simp only [Nat.add_zero, pow_zero, mul_one, show m + 0 + 1 = m + 1 by rfl,
        show w' + 1 - 0 = w' + 1 by rfl]
    · -- the shifted body: index k ↦ k+1
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      rw [show m + (k + 1) + 1 = m + 1 + k + 1 from by omega]
      rw [show w' + 1 - (k + 1) = w' - k from by omega]

/-- **Multiply-back over the window** (exact synthetic division of `[m, m+w)` by `X − C p`). -/
theorem synDiv_mul_back_win (c : Nat → Std.U16) (p : GF16) :
    ∀ (w m : Nat),
      (X - C p) * synQuotWin c p m w + C (synTail c p m w) = gpolyWin c m w := by
  intro w
  induction w with
  | zero => intro m; simp [synQuotWin, gpolyWin]
  | succ w ih =>
    intro m
    rw [gpolyWin_succ, synQuotWin_succ, synTail_succ]
    rw [map_add, map_mul]
    -- IH at m+1
    have hih := ih (m + 1)
    -- (X - Cp)(C(synTail (m+1) w) + X·Q') + (C(c m) + Cp·C(synTail (m+1) w))
    --   = C(c m) + X·((X-Cp)·Q' + C(synTail (m+1) w))   [= C(c m) + X·gpolyWin (m+1) w]
    rw [mul_add, ← hih]
    ring

/-- `gpolyWin c 0 len = gpoly c len`. -/
theorem gpolyWin_zero (c : Nat → Std.U16) (len : Nat) : gpolyWin c 0 len = gpoly (fun k => c k) len := by
  unfold gpolyWin gpoly
  apply Finset.sum_congr rfl
  intro k _; rw [Nat.zero_add]

/-- The synthetic-division quotient polynomial of the whole input (window `[0, len)`), as the
degree-`<len−1` quotient of `gpoly c len` by `X − C p`. -/
noncomputable def synQuot (c : Nat → Std.U16) (p : GF16) (len : Nat) : GF16[X] :=
  synQuotWin c p 0 len

/-- **Multiply-back (exact synthetic division).** `(X − C p) · synQuot + C (remainder) = gpoly c len`,
with `remainder = synTail c p 0 len`. The quotient `synQuot` is genuine and `synTail c p 0 len` is the
division remainder. UNCONDITIONAL, over the `GF16` CommRing. -/
theorem synDiv_mul_back (c : Nat → Std.U16) (p : GF16) (len : Nat) :
    (X - C p) * synQuot c p len + C (synTail c p 0 len) = gpoly (fun k => c k) len := by
  rw [synQuot, ← gpolyWin_zero]
  exact synDiv_mul_back_win c p len 0

/-! ### The `gpoly` of the `divFold` output, from `DivInv`. -/

/-- **The `gpoly` of the `complete` long-division output.** If `o` satisfies `DivInv c pix scale len o len`
(the finalized invariant from `DivInv_fold`), then over GF16 its coefficient polynomial is
`gpoly o len = C(remainder) + C scale · X · synQuot`, where `remainder = synTail c pix 0 len` and
`synQuot` is the synthetic-division quotient: every slot `m ≥ 1` is `scale · synTail c pix m (len−m)`
and slot `0` is the un-scaled remainder. UNCONDITIONAL. -/
theorem gpoly_divOutput (c : Nat → Std.U16) (pix scale : Std.U16) (len : Nat) (hlen : 1 ≤ len)
    (o : Nat → Std.U16)
    (hinv : DivInv c (GF16.ofU16 pix) (GF16.ofU16 scale) len o len) :
    gpoly (fun k => o k) len
      = C (synTail c (GF16.ofU16 pix) 0 len)
        + C (GF16.ofU16 scale) * X * synQuot c (GF16.ofU16 pix) len := by
  obtain ⟨hfin, hzero, _⟩ := hinv
  rw [show len - len = 0 from by omega] at hfin
  rw [show len - len = 0 from by omega, show len - 0 = len from by omega] at hzero
  obtain ⟨len', rfl⟩ : ∃ m, len = m + 1 := ⟨len - 1, by omega⟩
  unfold gpoly
  rw [Finset.sum_range_succ']
  rw [Nat.add_zero, pow_zero, mul_one, hzero, add_comm]
  congr 1
  rw [synQuot, synQuotWin]
  rw [show len' + 1 - 1 = len' from by omega]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have ho : GF16.ofU16 (o (k + 1))
      = GF16.ofU16 scale * synTail c (GF16.ofU16 pix) (k + 1) (len' + 1 - (k + 1)) :=
    hfin (k + 1) (by omega) (by omega)
  rw [ho, map_mul]
  rw [show 0 + k + 1 = k + 1 from by omega, show len' - k = len' + 1 - (k + 1) from by omega]
  ring

/-! ### P1. `gf.complete` is the scaled, shifted synthetic quotient (UNCONDITIONAL, in-boundary). -/

/-- **`gf.complete` computes the scaled, shifted synthetic quotient over GF(2¹⁶)** (UNCONDITIONAL,
in-boundary). For `n ≤ 36` and `i < n`, the extracted `gf.complete coeffs xs ys n i` succeeds with an
array `r` whose `GF16` coefficient polynomial `gpoly (r[·]) (n+1)` equals

    C(remainder) + C(scale) · X · synQuot

where `pix = ofU16 xs[i]`, `scale = ofU16 (gfDivV ys[i] (denomV xs n xs[i] 1 0))` is the Lagrange
weight (the banked `complete_eq` parameters), `remainder = synTail (coeffs[·]) pix 0 (n+1)` is the
synthetic-division remainder, and `synQuot` is the quotient of `gpoly coeffs (n+1)` by `(X − C pix)`.
Equivalently (`synDiv_mul_back`), `(X − C pix) · synQuot + C remainder = gpoly coeffs (n+1)`, so when
`pix` is a root of the input (e.g. `coeffs = prepare` so `gpoly coeffs (n+1) = ∏(X − xs[j])` and
`pix = xs[i]`, `i < n`), `remainder = 0` and `gpoly (r[·]) (n+1) = C scale · X · (∏_{j≠i}(X − xs[j]))`
— the scaled basis numerator times `X`.

Assembled from the banked `RsInterp.complete_eq` (`gf.complete` runs `divFold`), the `DivInv`
window-invariant induction (`DivInv_init`/`DivInv_step`/`DivInv_fold`), and `gpoly_divOutput`. Uses
ONLY the unconditional `CommRing` on `GF16` (`hmul` discharged by Stage 2) — NO field inverse, NO
irreducibility. NO `axiom`, `sorry`, `native_decide`, or `decide` over the value space. -/
theorem complete_eq_synDiv (coeffs : Array Std.U16 37#usize) (xs ys : Array Std.U16 36#usize)
    (n i : Std.Usize) (hn : n.val ≤ 36) (hi : i.val < n.val) :
    gf.complete coeffs xs ys n i
      ⦃ r =>
        gpoly (fun k => r.val[k]!) (n.val + 1)
          = C (synTail (fun k => coeffs.val[k]!) (GF16.ofU16 xs.val[i.val]!) 0 (n.val + 1))
            + C (GF16.ofU16 (gfDivV ys.val[i.val]! (denomV xs n xs.val[i.val]! 1#u16 0)))
              * X * synQuot (fun k => coeffs.val[k]!) (GF16.ofU16 xs.val[i.val]!) (n.val + 1) ⦄ := by
  have hce := complete_eq coeffs xs ys n i hn hi
  apply Std.WP.spec_mono hce
  intro r hr
  set c := (fun k => coeffs.val[k]! : Nat → Std.U16) with hc
  set pix := xs.val[i.val]! with hpix
  set scale := gfDivV ys.val[i.val]! (denomV xs n xs.val[i.val]! 1#u16 0) with hscale
  -- the fold-finalized invariant on the pure divFold output
  have hinit : DivInv c (GF16.ofU16 pix) (GF16.ofU16 scale) (n.val + 1) c 1 :=
    DivInv_init c pix scale (n.val + 1) (by omega)
  have hfold : DivInv c (GF16.ofU16 pix) (GF16.ofU16 scale) (n.val + 1)
      (divFold pix scale (n.val + 1) c 1) (n.val + 1) :=
    DivInv_fold c pix scale (n.val + 1) (n.val) c 1 (by omega) (by omega) (by omega) hinit
  -- gpoly of the extracted array = gpoly of the pure divFold output (they agree on m < n+1 ≤ 37)
  have hgp : gpoly (fun k => r.val[k]!) (n.val + 1)
      = gpoly (fun k => divFold pix scale (n.val + 1) c 1 k) (n.val + 1) := by
    unfold gpoly
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    simp only []
    rw [hr k (by omega)]
  rw [hgp]
  exact gpoly_divOutput c pix scale (n.val + 1) (by omega)
    (divFold pix scale (n.val + 1) c 1) hfold

/-! ### The synthetic-division remainder is the polynomial evaluation; root case. -/

/-- **The synthetic-division remainder `synTail c p 0 len` is the evaluation `eval p (gpoly c len)`.**
Immediate from the multiply-back: evaluating `(X − C p)·synQuot + C r = gpoly c len` at `p` kills the
`(X − C p)` term (`eval p (X − C p) = p − p = 0`), leaving `r = eval p (gpoly c len)`. UNCONDITIONAL. -/
theorem synTail_eq_eval (c : Nat → Std.U16) (p : GF16) (len : Nat) :
    synTail c p 0 len = eval p (gpoly (fun k => c k) len) := by
  have h := synDiv_mul_back c p len
  have := congrArg (eval p) h
  rw [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, zero_add, eval_C] at this
  exact this

/-- **`gf.complete` at a ROOT of its input is the scaled, shifted basis quotient (remainder gone).**
For `n ≤ 36`, `i < n`, IF `pix = xs[i]` is a root of the input coefficient polynomial
(`eval (ofU16 xs[i]) (gpoly coeffs (n+1)) = 0` — which holds when `coeffs` is the `gf.prepare`
nodal product, since each `xs[j]` is a root), then `gf.complete coeffs xs ys n i` succeeds with an
array `r` whose `GF16` polynomial is `gpoly (r[·]) (n+1) = C scale · X · synQuot`, with the
synthetic-division REMAINDER vanished: the output is exactly the scale times `X` times the
synthetic quotient `gpoly coeffs (n+1) / (X − C pix)` — the (scaled) Lagrange basis numerator times
`X`. UNCONDITIONAL over the `GF16` CommRing; no field inverse, no irreducibility. About `gf.complete`. -/
theorem complete_eq_synDiv_root (coeffs : Array Std.U16 37#usize) (xs ys : Array Std.U16 36#usize)
    (n i : Std.Usize) (hn : n.val ≤ 36) (hi : i.val < n.val)
    (hroot : eval (GF16.ofU16 xs.val[i.val]!) (gpoly (fun k => coeffs.val[k]!) (n.val + 1)) = 0) :
    gf.complete coeffs xs ys n i
      ⦃ r =>
        gpoly (fun k => r.val[k]!) (n.val + 1)
          = C (GF16.ofU16 (gfDivV ys.val[i.val]! (denomV xs n xs.val[i.val]! 1#u16 0)))
              * X * synQuot (fun k => coeffs.val[k]!) (GF16.ofU16 xs.val[i.val]!) (n.val + 1) ⦄ := by
  have hce := complete_eq_synDiv coeffs xs ys n i hn hi
  apply Std.WP.spec_mono hce
  intro r hr
  rw [hr]
  rw [synTail_eq_eval, hroot, map_zero, zero_add]

/-! ### Identifying the synthetic quotient of the nodal product with the Lagrange basis numerator. -/

/-- The basis numerator `∏_{k ∈ (range n).erase i}(X − C(ofU16 xs[k]))` — the nodal product with the
`i`-th factor removed (a Lagrange-basis numerator, monic of degree `n−1`). -/
noncomputable def basisNumer (xs : Array Std.U16 36#usize) (n i : Nat) : GF16[X] :=
  ∏ k ∈ (Finset.range n).erase i, (X - C (GF16.ofU16 xs.val[k]!))

/-- **The synthetic quotient of the nodal product by `(X − C xs[i])` is the basis numerator.** When
the input coefficient polynomial is the nodal product `gpoly coeffs (n+1) = nodal xs n` (e.g. from
`gf.prepare`, banked as `prepare_eq_nodal`) and `i < n`, the synthetic-division quotient
`synQuot coeffs (ofU16 xs[i]) (n+1)` equals `∏_{k≠i}(X − C(ofU16 xs[k]))`. Proved by factoring the
`i`-th root out of `nodal` (`Finset.mul_prod_erase`) and cancelling the monic `(X − C xs[i])` via
`mul_divByMonic_cancel_left` on the multiply-back identity. UNCONDITIONAL over the `GF16` CommRing
(no irreducibility — `X − C pix` is monic, hence a non-zero-divisor regardless). -/
theorem synQuot_nodal_eq (coeffs : Array Std.U16 37#usize) (xs : Array Std.U16 36#usize)
    (n i : Nat) (hi : i < n)
    (hnodal : gpoly (fun k => coeffs.val[k]!) (n + 1) = nodal xs n) :
    synQuot (fun k => coeffs.val[k]!) (GF16.ofU16 xs.val[i]!) (n + 1) = basisNumer xs n i := by
  set pix := GF16.ofU16 xs.val[i]! with hpix
  have hmono : (X - C pix).Monic := monic_X_sub_C pix
  -- nodal factors as (X - C pix) * basisNumer
  have hfac : nodal xs n = (X - C pix) * basisNumer xs n i := by
    unfold nodal basisNumer
    rw [← Finset.mul_prod_erase (Finset.range n) (fun k => X - C (GF16.ofU16 xs.val[k]!))
      (Finset.mem_range.mpr hi)]
  -- multiply-back with remainder 0: (X - C pix) * synQuot = nodal
  have hmb := synDiv_mul_back (fun k => coeffs.val[k]!) pix (n + 1)
  rw [hnodal, synTail_eq_eval, hnodal] at hmb
  -- eval pix nodal = 0 (pix = xs[i] is a root)
  have hroot : eval pix (nodal xs n) = 0 := by
    rw [hfac, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul]
  rw [hroot, map_zero, add_zero] at hmb
  -- hmb : (X - C pix) * synQuot = nodal = (X - C pix) * basisNumer
  rw [hfac] at hmb
  -- cancel the monic (X - C pix) via /ₘ
  calc synQuot (fun k => coeffs.val[k]!) pix (n + 1)
      = (X - C pix) * synQuot (fun k => coeffs.val[k]!) pix (n + 1) /ₘ (X - C pix) := by
        rw [mul_divByMonic_cancel_left _ hmono]
    _ = (X - C pix) * basisNumer xs n i /ₘ (X - C pix) := by rw [hmb]
    _ = basisNumer xs n i := by rw [mul_divByMonic_cancel_left _ hmono]

/-! ### P2. `gf.complete ∘ gf.prepare` is the scaled Lagrange basis numerator (UNCONDITIONAL). -/

/-- **`gf.complete` of the `gf.prepare` template is `scale · X · ℓ̃_i` — the scaled Lagrange basis
numerator times `X`** (UNCONDITIONAL, in-boundary). For `n ≤ 36` and `i < n`, run on the template
`coeffs` that `gf.prepare xs n` produces — i.e. `gpoly coeffs (n+1) = ∏_{k<n}(X − xs[k])`, the
banked `RsPrepareBridge.prepare_eq_nodal` — the extracted `gf.complete coeffs xs ys n i` succeeds
with an array `r` whose `GF16` coefficient polynomial is

    gpoly (r[·]) (n+1) = C(scale) · X · ∏_{k ∈ (range n).erase i}(X − C(ofU16 xs[k]))

where `scale = ofU16 (gfDivV ys[i] (denomV …))` is the Lagrange weight. So `gf.complete` divides the
master nodal product by `(X − xs[i])` (removing the `i`-th factor, leaving the basis numerator
`ℓ̃_i = ∏_{j≠i}(X − xs[j])`), scales by the Lagrange weight, and shifts up by one (`× X`, the upstream
"working is `x · <basis poly>`" offset). This is the per-`i` summand of the Lagrange interpolant
(modulo the `× X` shift the `lagrange_interpolate` loops then divide out by reading `working[k+1]`).

Assembled from `complete_eq_synDiv_root` (remainder vanishes at the root `xs[i]`) and
`synQuot_nodal_eq` (the synthetic quotient of the nodal product is the basis numerator). Mentions
`gf.complete` (and, via the `hprep` hypothesis, the `gf.prepare` nodal product). UNCONDITIONAL over
the `GF16` CommRing — NO field inverse, NO irreducibility, NO `axiom`/`sorry`/`native_decide`. -/
theorem complete_prepare_eq_scaled_basis (coeffs : Array Std.U16 37#usize)
    (xs ys : Array Std.U16 36#usize) (n i : Std.Usize) (hn : n.val ≤ 36) (hi : i.val < n.val)
    (hprep : gpoly (fun k => coeffs.val[k]!) (n.val + 1) = nodal xs n.val) :
    gf.complete coeffs xs ys n i
      ⦃ r =>
        gpoly (fun k => r.val[k]!) (n.val + 1)
          = C (GF16.ofU16 (gfDivV ys.val[i.val]! (denomV xs n xs.val[i.val]! 1#u16 0)))
              * X * basisNumer xs n.val i.val ⦄ := by
  -- the root hypothesis: eval (ofU16 xs[i]) of the nodal product is 0
  have hroot : eval (GF16.ofU16 xs.val[i.val]!) (gpoly (fun k => coeffs.val[k]!) (n.val + 1)) = 0 := by
    rw [hprep]
    unfold nodal
    rw [eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_range.mpr hi)
    rw [eval_sub, eval_X, eval_C, sub_self]
  have hce := complete_eq_synDiv_root coeffs xs ys n i hn hi hroot
  apply Std.WP.spec_mono hce
  intro r hr
  rw [hr, synQuot_nodal_eq coeffs xs n.val i.val hi hprep]

end Spqr.RsCompleteBridge