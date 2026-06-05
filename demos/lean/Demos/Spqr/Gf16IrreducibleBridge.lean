/-
  SPQR Reed–Solomon codec — Layer B-irr (bridge): TRANSPORT the kernel-checked mirror
  result `noSmallFactor POLY 8 = true` into an UNCONDITIONAL proof of
  `Irreducible (POLY_poly : (ZMod 2)[X])`, `POLY_poly = X¹⁶+X¹²+X³+X+1`.

  ## Structure

  The Mathlib-free mirror (`Gf16IrreducibleMirror.lean`) proves, by a pure-kernel `decide`,
  that no monic `List Bool` polynomial of degree `1..8` divides the bit pattern `POLY`.
  This file transports that to the real `(ZMod 2)[X]`:

  1. `toPoly : List Bool → (ZMod 2)[X]` — the Horner-form transport (`toPoly (b::l) =
     b + X·toPoly l`), with a coefficient master lemma `coeff_toPoly`. NOT defined to be
     `POLY_poly`; `toPoly POLY = POLY_poly` is a separate honest 5-term unfolding.
  2. `toPoly_bmod` — the LOAD-BEARING correspondence: the mirror's schoolbook remainder
     `bmod` equals the polynomial `%ₘ` for a trimmed monic divisor. Proved via a
     reduction-step degree-decrease lemma (`modStep_deg1_lt`), a divisibility invariant
     (`toPoly_modFuel_dvd_diff`), and `Polynomial.div_modByMonic_unique`.
  3. `bdvd_iff_dvd` — divisibility test agreement, via `modByMonic_eq_zero_iff_dvd`.
  4. `completeness` — every monic `q` of `natDegree e ∈ [1,8]` is `toPoly (monicOf e m)`
     for some `m < 2^e` enumerated by the mirror (`Polynomial.ext` on coefficients).
  5. `POLY_poly_irreducible` — assembled via `Monic.irreducible_iff_lt_natDegree_lt`
     (`natDegree POLY_poly / 2 = 8`, matching the mirror's `k = 8`).

  ## Integrity

  `#print axioms POLY_poly_irreducible` reports ONLY `propext, Classical.choice, Quot.sound`
  (the three standard Mathlib axioms) — NO `sorryAx`, NO `ofReduceBool`, NO `native`, NO
  custom axiom. The mirror's `noSmallFactor_POLY` reports NO axioms at all (pure kernel
  Bool reduction). This file imports Mathlib and is `noncomputable`; the mirror stays
  Mathlib-free so its `decide` reduces in the kernel.
-/
import Mathlib
import Demos.Spqr.Gf16IrreducibleMirror
import Demos.Spqr.Gf16Field
import Demos.Spqr.RsFieldBridge
import Demos.Spqr.RsDivInverse
import Demos.Spqr.Gf16FieldAssembly
import Demos.Spqr.Gf16FieldInstance

open Polynomial
namespace Spqr.Gf16IrreducibleBridge
open Spqr.Gf16IrreducibleMirror

/-- Horner-form transport: `toPoly (b::l) = b + X * toPoly l`. Matches the mirror's
head-first list recursion (`pmulX = false ::`, `padd` is head-first). -/
noncomputable def toPoly : List Bool → (ZMod 2)[X]
  | [] => 0
  | b :: l => (if b then 1 else 0) + X * toPoly l

@[simp] theorem toPoly_nil : toPoly [] = 0 := rfl
theorem toPoly_cons (b : Bool) (l : List Bool) :
    toPoly (b :: l) = (if b then 1 else 0) + X * toPoly l := rfl

theorem toPoly_pmulX (l : List Bool) : toPoly (pmulX l) = X * toPoly l := by
  unfold pmulX; rw [toPoly_cons]; simp

theorem toPoly_padd (a b : List Bool) : toPoly (padd a b) = toPoly a + toPoly b := by
  induction a generalizing b with
  | nil => simp [padd]
  | cons x xs ih =>
    cases b with
    | nil => simp [padd]
    | cons y ys =>
      simp only [padd, toPoly_cons, ih]
      -- (xor x y) + X*(pa+pb) = (x + X pa) + (y + X pb)
      have h2 : (2 : (ZMod 2)[X]) = 0 := by
        simpa using (CharP.cast_eq_zero (R := (ZMod 2)[X]) 2)
      cases x <;> cases y <;>
        simp only [show (xor true true) = false from rfl, show (xor true false) = true from rfl,
          show (xor false true) = true from rfl, show (xor false false) = false from rfl,
          if_true, if_false, Bool.false_eq_true] <;> ring_nf <;>
        first | ring | (rw [h2]; ring)

theorem toPoly_shiftUp (n : Nat) (l : List Bool) :
    toPoly (shiftUp n l) = X^n * toPoly l := by
  induction n with
  | zero => simp [shiftUp]
  | succ k ih => simp only [shiftUp, toPoly_cons, Bool.false_eq_true, if_false]; rw [ih]; ring

/-- `trim` only drops trailing zero coefficients, so it preserves `toPoly`. -/
theorem toPoly_trim (l : List Bool) : toPoly (trim l) = toPoly l := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    unfold trim
    by_cases hr : (trim bs).isEmpty = true
    · -- trim bs = [], so toPoly bs = toPoly (trim bs) = 0
      have hbs0 : toPoly bs = 0 := by
        rw [← ih]; rw [List.isEmpty_iff] at hr; rw [hr]; rfl
      rw [if_pos hr]
      cases b with
      | false => simp [toPoly_cons, hbs0]
      | true => simp [toPoly_cons, hbs0]
    · rw [if_neg hr, toPoly_cons, toPoly_cons, ih]

/-- The transport of the mirror's `POLY` is exactly `POLY_poly`. Honest finite unfolding
(NOT defined to return `POLY_poly`). -/
theorem toPoly_POLY : toPoly POLY = Spqr.Gf16Field.POLY_poly := by
  unfold POLY Spqr.Gf16Field.POLY_poly
  simp only [toPoly_cons, toPoly_nil, if_true, if_false, Bool.false_eq_true]
  ring

/-! ### Coefficient master lemma -/

/-- Coefficient `i` of `toPoly l` is bit `i` of the list (as `ZMod 2`). The single
foundation from which all degree facts follow. -/
theorem coeff_toPoly (l : List Bool) (i : Nat) :
    (toPoly l).coeff i = (if l[i]? = some true then 1 else 0) := by
  induction l generalizing i with
  | nil => simp [toPoly_nil]
  | cons b bs ih =>
    rw [toPoly_cons]
    cases i with
    | zero =>
      simp only [Polynomial.coeff_add, Polynomial.coeff_X_mul_zero, add_zero,
        List.getElem?_cons_zero]
      cases b <;> simp [Polynomial.coeff_one]
    | succ j =>
      rw [Polynomial.coeff_add, Polynomial.coeff_X_mul, ih j]
      simp only [List.getElem?_cons_succ]
      cases b <;> simp [Polynomial.coeff_one]

/-! ### Degree facts -/

/-- Coefficients of `toPoly l` vanish at and beyond `l.length`. -/
theorem toPoly_coeff_eq_zero_of_ge (l : List Bool) (i : Nat) (hi : l.length ≤ i) :
    (toPoly l).coeff i = 0 := by
  rw [coeff_toPoly]
  have : l[i]? = none := List.getElem?_eq_none hi
  simp [this]

/-- `toPoly l` has degree `< l.length`. -/
theorem toPoly_degree_lt (l : List Bool) : (toPoly l).degree < (l.length : WithBot ℕ) := by
  apply Polynomial.degree_lt_iff_coeff_zero _ _ |>.mpr
  intro m hm
  exact toPoly_coeff_eq_zero_of_ge l m (by exact_mod_cast hm)

/-- The top index of a nonempty trimmed list reads `some true` (trim removes trailing
falses, so the last surviving coefficient is `1`). -/
theorem trim_top_true (l : List Bool) (h : trim l ≠ []) :
    (trim l)[(trim l).length - 1]? = some true := by
  induction l with
  | nil => simp [trim] at h
  | cons b bs ih =>
    rw [show trim (b :: bs)
        = (if (trim bs).isEmpty then (if b then [b] else []) else b :: trim bs) from rfl] at *
    by_cases hr : (trim bs).isEmpty = true
    · rw [if_pos hr] at h ⊢
      cases b with
      | false => simp at h
      | true => simp
    · rw [if_neg hr] at h ⊢
      have hne : trim bs ≠ [] := by rwa [List.isEmpty_iff] at hr
      have hpos : 0 < (trim bs).length := List.length_pos_of_ne_nil hne
      have hlen : (b :: trim bs).length - 1 = (trim bs).length - 1 + 1 := by
        simp only [List.length_cons]; omega
      rw [hlen, List.getElem?_cons_succ]
      exact ih hne

/-- For a trimmed nonempty list, `toPoly` has `natDegree = length - 1`. -/
theorem toPoly_natDegree_trim (l : List Bool) (hself : trim l = l) (hnil : l ≠ []) :
    (toPoly l).natDegree = l.length - 1 := by
  have htop : (toPoly l).coeff (l.length - 1) = 1 := by
    rw [coeff_toPoly]
    have := trim_top_true l (by rw [hself]; exact hnil)
    rw [hself] at this
    simp [this]
  apply le_antisymm
  · -- natDegree ≤ length - 1
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    exact toPoly_coeff_eq_zero_of_ge l m (by omega)
  · -- length - 1 ≤ natDegree, since coeff (length-1) ≠ 0
    apply Polynomial.le_natDegree_of_ne_zero
    rw [htop]; exact one_ne_zero

/-- For a trimmed nonempty list, `toPoly` is monic. -/
theorem toPoly_monic_trim (l : List Bool) (hself : trim l = l) (hnil : l ≠ []) :
    (toPoly l).Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, toPoly_natDegree_trim l hself hnil,
    coeff_toPoly]
  have := trim_top_true l (by rw [hself]; exact hnil)
  rw [hself] at this
  simp [this]

/-! ### The remainder is congruent to the input modulo the divisor -/

/-- One reduction step changes `toPoly` by a multiple of `toPoly d`: the difference
`toPoly (modStep d Dlen p) - toPoly p` is divisible by `toPoly d`. -/
theorem toPoly_modStep_dvd_diff (d : List Bool) (Dlen : Nat) (p : List Bool) :
    toPoly d ∣ (toPoly (modStep d Dlen p) - toPoly p) := by
  unfold modStep
  by_cases h : deg1 p < Dlen
  · simp [h, sub_self]
  · simp only [h, if_false]
    rw [toPoly_trim, toPoly_padd, toPoly_shiftUp]
    ring_nf
    exact Dvd.intro_left _ rfl

/-- The whole reduction loop leaves the input congruent modulo `toPoly d`:
`toPoly d ∣ (toPoly (modFuel d Dlen fuel p) - toPoly p)`. -/
theorem toPoly_modFuel_dvd_diff (d : List Bool) (Dlen : Nat) :
    ∀ (fuel : Nat) (p : List Bool),
      toPoly d ∣ (toPoly (modFuel d Dlen fuel p) - toPoly p) := by
  intro fuel
  induction fuel with
  | zero => intro p; simp [modFuel, sub_self]
  | succ k ih =>
    intro p
    unfold modFuel
    by_cases h : deg1 p < Dlen
    · simp [h, sub_self]
    · simp only [h, if_false]
      -- toPoly(modFuel k (modStep p)) - toPoly p
      --   = (toPoly(modFuel k (modStep p)) - toPoly(modStep p)) + (toPoly(modStep p) - toPoly p)
      have e1 := ih (modStep d Dlen p)
      have e2 := toPoly_modStep_dvd_diff d Dlen p
      have : toPoly (modFuel d Dlen k (modStep d Dlen p)) - toPoly p
           = (toPoly (modFuel d Dlen k (modStep d Dlen p)) - toPoly (modStep d Dlen p))
             + (toPoly (modStep d Dlen p) - toPoly p) := by ring
      rw [this]
      exact dvd_add e1 e2

/-! ### Relating the mirror's `deg1` to the polynomial `natDegree` -/

/-- Unfold one layer of `trim` on a cons. -/
theorem trim_cons (b : Bool) (bs : List Bool) :
    trim (b :: bs) = (if (trim bs).isEmpty then (if b then [b] else []) else b :: trim bs) := rfl

/-- `trim` is idempotent. -/
theorem trim_idem (l : List Bool) : trim (trim l) = trim l := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    rw [trim_cons b bs]
    by_cases hr : (trim bs).isEmpty = true
    · rw [if_pos hr]
      cases b with
      | false => rfl
      | true => decide
    · rw [if_neg hr]
      -- goal: trim (b :: trim bs) = b :: trim bs ; trim bs nonempty so isEmpty (trim (trim bs)) = false
      rw [trim_cons b (trim bs), ih, if_neg hr]

/-- `toPoly l = 0` exactly when `l` trims to the empty list. -/
theorem toPoly_eq_zero_iff (l : List Bool) : toPoly l = 0 ↔ trim l = [] := by
  constructor
  · intro h
    by_contra hne
    have hmonic := toPoly_monic_trim (trim l) (trim_idem l) hne
    rw [toPoly_trim] at hmonic
    rw [h] at hmonic
    exact (Polynomial.not_monic_zero) hmonic
  · intro h
    rw [← toPoly_trim, h, toPoly_nil]

/-- `deg1 l = natDegree (toPoly l) + 1` when `toPoly l ≠ 0`. -/
theorem deg1_eq_natDegree_succ (l : List Bool) (h : toPoly l ≠ 0) :
    deg1 l = (toPoly l).natDegree + 1 := by
  have hne : trim l ≠ [] := fun hh => h ((toPoly_eq_zero_iff l).mpr hh)
  have hpos : 0 < (trim l).length := List.length_pos_of_ne_nil hne
  have hnd : (toPoly l).natDegree = (trim l).length - 1 := by
    rw [← toPoly_trim l]; exact toPoly_natDegree_trim (trim l) (trim_idem l) hne
  unfold deg1
  omega

/-- If all coefficients of `toPoly l` from index `n` upward vanish, then `deg1 l ≤ n`. -/
theorem deg1_le_of_coeff_zero (l : List Bool) (n : Nat)
    (h : ∀ m, n ≤ m → (toPoly l).coeff m = 0) : deg1 l ≤ n := by
  by_cases hz : toPoly l = 0
  · have : trim l = [] := (toPoly_eq_zero_iff l).mp hz
    unfold deg1; rw [this]; simp
  · rw [deg1_eq_natDegree_succ l hz]
    -- natDegree < n
    have hnd : (toPoly l).natDegree < n := by
      by_contra hcon
      push_neg at hcon
      have hcoeff := h (toPoly l).natDegree hcon
      have hlc : (toPoly l).leadingCoeff = 0 := hcoeff
      exact (Polynomial.leadingCoeff_ne_zero.mpr hz) hlc
    omega

/-! ### Each reduction step strictly drops `deg1` -/

/-- The reduction step strictly decreases `deg1` when it fires. Requires `dn` trimmed
(so `toPoly dn` is monic of `natDegree = Dlen - 1`) with `Dlen = deg1 dn ≥ 1`, and
`deg1 p ≥ Dlen`. -/
theorem modStep_deg1_lt (dn : List Bool) (Dlen : Nat)
    (hself : trim dn = dn) (hnil : dn ≠ []) (hDlen : Dlen = deg1 dn) (hD1 : 1 ≤ Dlen)
    (p : List Bool) (hp : Dlen ≤ deg1 p) :
    deg1 (modStep dn Dlen p) < deg1 p := by
  -- toPoly dn monic, natDegree = Dlen - 1
  have hdnnd : (toPoly dn).natDegree = Dlen - 1 := by
    rw [hDlen]; unfold deg1; rw [hself]
    exact toPoly_natDegree_trim dn hself hnil
  have hdnmonic : (toPoly dn).Monic := toPoly_monic_trim dn hself hnil
  -- p nonzero, natDegree = deg1 p - 1
  have hpz : toPoly p ≠ 0 := by
    intro hh
    have hpe : deg1 p = 0 := by unfold deg1; rw [(toPoly_eq_zero_iff p).mp hh]; rfl
    omega
  have hpnd : (toPoly p).natDegree = deg1 p - 1 := by
    have := deg1_eq_natDegree_succ p hpz; omega
  -- the step is not the trivial branch
  have hfire : ¬ deg1 p < Dlen := by omega
  set k := deg1 p - Dlen with hk
  have hmod : modStep dn Dlen p = trim (padd p (shiftUp k dn)) := by
    unfold modStep; rw [if_neg hfire]
  -- N = top index = deg1 p - 1
  set N := deg1 p - 1 with hN
  -- coeff N of (toPoly p + X^k * toPoly dn) is 0, and coeffs above N vanish
  have hsum : toPoly (padd p (shiftUp k dn)) = toPoly p + X ^ k * toPoly dn := by
    rw [toPoly_padd, toPoly_shiftUp]
  -- bound: deg1 (modStep) ≤ N < deg1 p
  rw [hmod]
  have hdeg1trim : deg1 (trim (padd p (shiftUp k dn))) = deg1 (padd p (shiftUp k dn)) := by
    unfold deg1; rw [trim_idem]
  rw [hdeg1trim]
  apply lt_of_le_of_lt (b := N)
  · apply deg1_le_of_coeff_zero
    intro m hm
    rw [hsum, Polynomial.coeff_add]
    -- coeff of toPoly p at m
    have hpc : (toPoly p).coeff m = if m = N then 1 else 0 := by
      rcases eq_or_lt_of_le hm with hmeq | hmlt
      · subst hmeq
        rw [if_pos rfl]
        have : (toPoly p).coeff N = (toPoly p).coeff (toPoly p).natDegree := by rw [hpnd]
        rw [this, ← Polynomial.leadingCoeff]
        have := toPoly_monic_trim (trim p) (trim_idem p) (by
          intro hh; exact hpz ((toPoly_eq_zero_iff p).mpr hh))
        rw [toPoly_trim] at this
        exact this
      · rw [if_neg (by omega)]
        apply Polynomial.coeff_eq_zero_of_natDegree_lt; omega
    -- coeff of X^k * toPoly dn at m
    have hdc : (X ^ k * toPoly dn).coeff m = if m = N then 1 else 0 := by
      have hknd : (X ^ k * toPoly dn).natDegree = N := by
        rw [Polynomial.natDegree_mul (by simp) hdnmonic.ne_zero, Polynomial.natDegree_X_pow, hdnnd]
        omega
      rcases eq_or_lt_of_le hm with hmeq | hmlt
      · subst hmeq
        rw [if_pos rfl]
        have hlc : (X ^ k * toPoly dn).coeff N = (X ^ k * toPoly dn).coeff (X ^ k * toPoly dn).natDegree := by rw [hknd]
        rw [hlc, ← Polynomial.leadingCoeff, Polynomial.Monic.leadingCoeff]
        exact (Polynomial.monic_X_pow k).mul hdnmonic
      · rw [if_neg (by omega)]
        apply Polynomial.coeff_eq_zero_of_natDegree_lt; omega
    rw [hpc, hdc]
    by_cases hmN : m = N
    · rw [if_pos hmN]; decide
    · rw [if_neg hmN]; simp
  · omega

/-- The reduction loop terminates with `deg1 < Dlen`, given enough fuel. -/
theorem modFuel_deg1_lt (dn : List Bool) (Dlen : Nat)
    (hself : trim dn = dn) (hnil : dn ≠ []) (hDlen : Dlen = deg1 dn) (hD1 : 1 ≤ Dlen) :
    ∀ (fuel : Nat) (p : List Bool), deg1 p ≤ fuel + Dlen - 1 →
      deg1 (modFuel dn Dlen fuel p) < Dlen := by
  intro fuel
  induction fuel with
  | zero =>
    intro p hpf
    unfold modFuel
    -- fuel 0: modFuel returns p; deg1 p ≤ Dlen - 1 < Dlen
    omega
  | succ k ih =>
    intro p hpf
    unfold modFuel
    by_cases h : deg1 p < Dlen
    · rw [if_pos h]; exact h
    · rw [if_neg h]
      apply ih
      -- modStep strictly decreases deg1, so deg1 (modStep) ≤ deg1 p - 1 ≤ k + Dlen - 1
      have hdec := modStep_deg1_lt dn Dlen hself hnil hDlen hD1 p (by omega)
      omega

/-! ### The mirror remainder IS the polynomial `%ₘ` -/

/-- For a trimmed monic divisor `d` of degree `≥ 1`, the mirror's `bmod` computes exactly
the polynomial remainder `%ₘ`. This is the load-bearing correspondence. -/
theorem toPoly_bmod (d : List Bool) (hself : trim d = d) (hlen : 2 ≤ d.length) (p : List Bool) :
    toPoly (bmod p d) = toPoly p %ₘ toPoly d := by
  have hnil : d ≠ [] := by intro h; rw [h] at hlen; simp at hlen
  have hDdef : d.length = deg1 d := by unfold deg1; rw [hself]
  set Dlen := d.length with hDlen
  have hD2 : 2 ≤ Dlen := hlen
  -- bmod unfolds (dn = trim d = d)
  have hbmod : bmod p d = trim (modFuel d Dlen (deg1 p + 1) p) := by
    unfold bmod
    rw [hself]
    have hnle : ¬ Dlen ≤ 1 := by omega
    rw [if_neg hnle]
  -- divisor poly is monic
  have hdmonic : (toPoly d).Monic := toPoly_monic_trim d hself hnil
  -- the remainder list and its degree bound
  set rl := modFuel d Dlen (deg1 p + 1) p with hrl
  have hrdeg1 : deg1 rl < Dlen := by
    apply modFuel_deg1_lt d Dlen hself hnil hDdef (by omega)
    omega
  -- toPoly (bmod p d) = toPoly rl  (trim preserves toPoly)
  have htb : toPoly (bmod p d) = toPoly rl := by rw [hbmod, toPoly_trim]
  -- degree bound: degree (toPoly rl) < degree (toPoly d)
  have hdegbound : (toPoly rl).degree < (toPoly d).degree := by
    have h1 : (toPoly rl).degree < ((trim rl).length : WithBot ℕ) := by
      rw [← toPoly_trim rl]; exact toPoly_degree_lt (trim rl)
    have hdd : (toPoly d).degree = ((d.length : ℕ) - 1 : ℕ) := by
      rw [Polynomial.degree_eq_natDegree hdmonic.ne_zero, toPoly_natDegree_trim d hself hnil]
    -- (trim rl).length = deg1 rl < Dlen = d.length, so degree rl < d.length - 1
    have hrl_len : (trim rl).length = deg1 rl := rfl
    rw [hdd]
    rw [hrl_len] at h1
    calc (toPoly rl).degree < (deg1 rl : WithBot ℕ) := h1
      _ ≤ (((d.length : ℕ) - 1 : ℕ) : WithBot ℕ) := by
          rw [Nat.cast_le]; omega
  -- divisibility: toPoly d ∣ (toPoly rl - toPoly p)
  have hdvd : toPoly d ∣ (toPoly rl - toPoly p) := toPoly_modFuel_dvd_diff d Dlen _ p
  obtain ⟨Q, hQ⟩ := hdvd
  -- assemble via uniqueness of div/mod
  have key : toPoly p %ₘ toPoly d = toPoly rl := by
    have hid : toPoly rl + toPoly d * (-Q) = toPoly p := by
      have : toPoly rl - toPoly p = toPoly d * Q := hQ
      linear_combination this
    exact (div_modByMonic_unique (-Q) (toPoly rl) hdmonic ⟨hid, hdegbound⟩).2
  rw [htb, key]

/-! ### `bdvd` corresponds to polynomial divisibility -/

/-- `isZero l = true ↔ toPoly l = 0`. -/
theorem isZero_iff (l : List Bool) : isZero l = true ↔ toPoly l = 0 := by
  unfold isZero
  rw [List.isEmpty_iff, ← toPoly_eq_zero_iff]

/-- The mirror divisibility test agrees with polynomial divisibility, for a trimmed monic
divisor of degree `≥ 1`. -/
theorem bdvd_iff_dvd (d : List Bool) (hself : trim d = d) (hlen : 2 ≤ d.length) (p : List Bool) :
    bdvd d p = true ↔ toPoly d ∣ toPoly p := by
  unfold bdvd
  rw [isZero_iff, toPoly_bmod d hself hlen p,
    Polynomial.modByMonic_eq_zero_iff_dvd (toPoly_monic_trim d hself
      (by intro h; rw [h] at hlen; simp at hlen))]

/-! ### Enumeration completeness: every monic poly of degree `e` is a `monicOf` -/

/-- Little-endian bit value of a bool list (inverse of `natToBits`). -/
def bitsToNat : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitsToNat bs

theorem natToBits_length (d m : Nat) : (natToBits d m).length = d := by
  induction d generalizing m with
  | zero => rfl
  | succ k ih => simp [natToBits, ih]

theorem bitsToNat_lt (bs : List Bool) : bitsToNat bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [bitsToNat]
  | cons b bs ih =>
    simp only [bitsToNat, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

/-- `natToBits` recovers any bool list from its little-endian value. -/
theorem natToBits_bitsToNat (bs : List Bool) :
    natToBits bs.length (bitsToNat bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons, natToBits, bitsToNat]
    refine List.cons_eq_cons.mpr ⟨?_, ?_⟩
    · cases b <;> simp <;> omega
    · have : ((if b then 1 else 0) + 2 * bitsToNat bs) / 2 = bitsToNat bs := by
        cases b <;> simp <;> omega
      rw [this]; exact ih

theorem monicOf_length (e m : Nat) : (monicOf e m).length = e + 1 := by
  unfold monicOf; rw [List.length_append, natToBits_length]; simp

/-- Index `e` (the top) of `monicOf e m` reads `some true`. -/
theorem monicOf_top (e m : Nat) : (monicOf e m)[e]? = some true := by
  unfold monicOf
  rw [List.getElem?_append_right (by rw [natToBits_length])]
  rw [natToBits_length]; simp

/-- A `monicOf` list is its own trim (it ends in `true`). -/
theorem monicOf_trim (e m : Nat) : trim (monicOf e m) = monicOf e m := by
  -- the last element is `true`, so trim removes nothing
  unfold monicOf
  induction natToBits e m with
  | nil => rfl
  | cons b bs ih =>
    rw [List.cons_append, trim_cons]
    have hne : ¬ (trim (bs ++ [true])).isEmpty = true := by
      rw [ih]; simp
    rw [if_neg hne, ih]

/-- Decode a `ZMod 2` element to `Bool`. -/
def decZ (z : ZMod 2) : Bool := z = 1

theorem toPoly_coeff_decZ (z : ZMod 2) : (if decZ z then (1 : ZMod 2) else 0) = z := by
  unfold decZ
  fin_cases z <;> decide

/-- **Enumeration completeness.** Every monic `q : (ZMod 2)[X]` of `natDegree = e` (with
`e ≥ 1`) equals `toPoly (monicOf e m)` for some `m < 2^e` — i.e. it is one of the candidates
`monicDeg e` enumerated by the mirror. -/
theorem completeness (q : (ZMod 2)[X]) (hq : q.Monic) (e : Nat) (he : 1 ≤ e)
    (hdeg : q.natDegree = e) :
    ∃ m, m < 2 ^ e ∧ toPoly (monicOf e m) = q := by
  -- the lower-coefficient bits
  set bits := (List.range e).map (fun i => decZ (q.coeff i)) with hbits
  have hbl : bits.length = e := by rw [hbits]; simp
  refine ⟨bitsToNat bits, ?_, ?_⟩
  · rw [← hbl]; exact bitsToNat_lt bits
  · -- monicOf e (bitsToNat bits) = bits ++ [true]
    have hmo : monicOf e (bitsToNat bits) = bits ++ [true] := by
      unfold monicOf
      rw [show e = bits.length from hbl.symm, natToBits_bitsToNat]
    rw [hmo]
    -- coeff-by-coeff
    apply Polynomial.ext
    intro i
    rw [coeff_toPoly]
    by_cases hlt : i < e
    · -- i < e: list index i is bits[i] = decZ (q.coeff i)
      have hidx : (bits ++ [true])[i]? = some (decZ (q.coeff i)) := by
        rw [List.getElem?_append_left (by rw [hbl]; exact hlt)]
        rw [hbits, List.getElem?_map, List.getElem?_range (by exact hlt)]
        simp
      rw [hidx]
      simp only [Option.some.injEq]
      -- if decZ (q.coeff i) = true then 1 else 0 = q.coeff i — exactly toPoly_coeff_decZ
      exact toPoly_coeff_decZ (q.coeff i)
    · by_cases hie : i = e
      · -- top coefficient: both 1
        subst hie
        rw [List.getElem?_append_right (by rw [hbl]), hbl]
        simp only [Nat.sub_self, List.getElem?_cons_zero, if_true]
        have hlead : q.coeff i = 1 := by
          rw [← hdeg]; exact hq.coeff_natDegree
        rw [hlead]
      · -- i > e: both 0
        have hgt : e < i := by omega
        have hnone : (bits ++ [true])[i]? = none := by
          apply List.getElem?_eq_none
          rw [List.length_append, hbl]; simp; omega
        rw [hnone]
        simp only [reduceCtorEq, if_false]
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

/-! ### Extracting non-divisibility from the mirror headline -/

/-- From `noSmallFactor POLY 8 = true`, no `monicOf e m` (degree `e ∈ [1,8]`, `m < 2^e`)
divides `POLY`. -/
theorem not_bdvd_of_noSmallFactor (e m : Nat) (he : 1 ≤ e) (he8 : e ≤ 8) (hm : m < 2 ^ e) :
    bdvd (monicOf e m) POLY = false := by
  have hns := noSmallFactor_POLY
  unfold noSmallFactor at hns
  rw [List.all_eq_true] at hns
  -- instantiate at i = e - 1 ∈ range 8
  have hi : (e - 1) ∈ List.range 8 := by rw [List.mem_range]; omega
  have hrow := hns (e - 1) hi
  rw [List.all_eq_true] at hrow
  -- monicOf e m ∈ monicDeg ((e-1)+1) = monicDeg e
  have he1 : e - 1 + 1 = e := by omega
  have hmem : monicOf e m ∈ monicDeg e := by
    unfold monicDeg
    rw [List.mem_map]
    exact ⟨m, by rw [List.mem_range]; exact hm, rfl⟩
  have hcell := hrow (monicOf e m) (by rw [he1]; exact hmem)
  -- hcell : (! bdvd (monicOf e m) POLY) = true
  rw [Bool.not_eq_true'] at hcell
  exact hcell

/-! ### THE THEOREM: `POLY_poly` is irreducible (unconditional). -/

/-- The half-degree non-divisibility hypothesis of `Monic.irreducible_iff_lt_natDegree_lt`,
discharged via the mirror: no monic polynomial of degree `1..8` divides `POLY_poly`. -/
theorem no_factor_le_8 :
    ∀ q : (ZMod 2)[X], q.Monic → q.natDegree ∈ Finset.Ioc 0 8 → ¬ q ∣ Spqr.Gf16Field.POLY_poly := by
  intro q hq hqdeg
  rw [Finset.mem_Ioc] at hqdeg
  obtain ⟨he, he8⟩ := hqdeg
  set e := q.natDegree with hedef
  -- completeness: q = toPoly (monicOf e m)
  obtain ⟨m, hm, hmq⟩ := completeness q hq e he rfl
  -- the divisor list is trimmed monic of length e+1 ≥ 2
  have hself : trim (monicOf e m) = monicOf e m := monicOf_trim e m
  have hlen : 2 ≤ (monicOf e m).length := by rw [monicOf_length]; omega
  -- no mirror factor
  have hnf : bdvd (monicOf e m) POLY = false := not_bdvd_of_noSmallFactor e m he he8 hm
  -- transport: ¬ toPoly (monicOf e m) ∣ toPoly POLY
  intro hdvd
  rw [← toPoly_POLY] at hdvd
  rw [← hmq] at hdvd
  have := (bdvd_iff_dvd (monicOf e m) hself hlen POLY).mpr hdvd
  rw [hnf] at this
  exact Bool.false_ne_true this

/-- **`POLY_poly = X¹⁶+X¹²+X³+X+1` is irreducible over `ZMod 2`** — proved unconditionally
via the kernel-checked `List Bool` mirror and the transport to `(ZMod 2)[X]`. -/
theorem POLY_poly_irreducible : Irreducible (Spqr.Gf16Field.POLY_poly : (ZMod 2)[X]) := by
  rw [Spqr.Gf16Field.POLY_poly_monic.irreducible_iff_lt_natDegree_lt Spqr.Gf16Field.POLY_poly_ne_one]
  rw [Spqr.Gf16Field.POLY_poly_natDegree]
  -- bound is 16 / 2 = 8
  exact no_factor_le_8

/-- The `Fact (Irreducible POLY_poly)` instance — UNCONDITIONALLY discharges the premise
carried by the seven downstream field/RS files (`Gf16FieldInstance`, `Gf16FieldAssembly`,
`Gf16Field`, `RsDivInverse`, `RsLagrangeBridge`, `RsFieldBridge`, `Gf16Irreducible`). -/
instance fact_POLY_poly_irreducible : Fact (Irreducible (Spqr.Gf16Field.POLY_poly : (ZMod 2)[X])) :=
  ⟨POLY_poly_irreducible⟩

/-! ### Unconditional capstone wrappers

The seven downstream files bind `[Fact (Irreducible POLY_poly)]` on their headline theorems.
Now that `fact_POLY_poly_irreducible` is a real (axiom-clean) instance, those binders are
discharged automatically. The wrappers below restate the Reed–Solomon `decode ∘ encode = id`
capstone with the `[Fact …]` binder DROPPED — the instance above supplies it — making the
unconditional upgrade explicit and giving a clean `#print axioms` target (no `sorryAx`, no
`ofReduceBool`, no custom axiom — only the three standard Mathlib axioms). -/

open Aeneas Std in
open Spqr.Gf in
open Spqr.Gf16Field (POLY_poly) in
open Spqr.Gf16FieldAssembly (phi) in
open Polynomial in
/-- **Reed–Solomon `decode ∘ encode = id` over the genuine GF(2¹⁶), UNCONDITIONAL on
irreducibility.** Same statement as `RsFieldBridge.decode_value_at_roundtrip_gf16_of_dist`
but with the `[Fact (Irreducible POLY_poly)]` binder DROPPED: it is discharged by the
real instance `fact_POLY_poly_irreducible` (proved via the kernel-checked mirror).
The only remaining hypotheses are the genuine non-degeneracy premises (distinct nodes,
low message degree, codeword-of-`f`) — NO algebraic premise, NO axiom. -/
theorem decode_value_at_roundtrip_gf16_unconditional
    (xs ys : Array Std.U16 36#usize) (n : Std.Usize) (x : Std.U16)
    {f : (AdjoinRoot POLY_poly)[X]}
    (hn : n.val ≤ 36)
    (hdist : ∀ a b, a < n.val → b < n.val → xs.val[a]! = xs.val[b]! → a = b)
    (hdeg : f.degree < (Finset.range n.val).card)
    (henc : ∀ i ∈ Finset.range n.val, Polynomial.eval (phi xs.val[i]!) f = phi ys.val[i]!) :
    (gf.decode_value_at xs ys n x >>= fun v => .ok (phi v))
      = .ok (Polynomial.eval (phi x) f) :=
  Spqr.RsFieldBridge.decode_value_at_roundtrip_gf16_of_dist xs ys n x hn hdist hdeg henc

/-! ### Unconditional field-law / division wrappers

The remaining load-bearing downstream headlines carry the same `[Fact (Irreducible POLY_poly)]`
binder. With `fact_POLY_poly_irreducible` in scope, the binder is discharged automatically; the
wrappers below restate each with the binder DROPPED, making the unconditional upgrade explicit.
Each is `#print axioms`-clean (only the three standard Mathlib axioms — no `sorryAx`, no
`ofReduceBool`, no custom axiom). -/

open Spqr.Gf16Field (POLY_poly) in
/-- **Fermat inverse in `AdjoinRoot POLY_poly`, UNCONDITIONAL on irreducibility.** Same as
`RsDivInverse.adjoinRoot_pow_eq_inv` with the `[Fact (Irreducible POLY_poly)]` binder dropped;
the real instance `fact_POLY_poly_irreducible` supplies it. -/
theorem adjoinRoot_pow_eq_inv_unconditional
    (a : AdjoinRoot POLY_poly) (ha : a ≠ 0) :
    a ^ (2 ^ 16 - 2) = a⁻¹ :=
  Spqr.RsDivInverse.adjoinRoot_pow_eq_inv a ha

open Aeneas Std in
open Spqr.Gf in
/-- **`gf.gf_div` is the genuine GF(2¹⁶) field inverse, UNCONDITIONAL on irreducibility.** Same
statement as `RsDivInverse.gf_div_eq_inv` with the `[Fact (Irreducible POLY_poly)]` binder
dropped — discharged by `fact_POLY_poly_irreducible`. -/
theorem gf_div_eq_inv_unconditional
    (numer denom : Std.U16) (hd : denom ≠ 0#u16) :
    Spqr.Gf16FieldInstance.gfRingEquiv (Spqr.Gf16FieldInstance.GF16.ofU16 (Spqr.RsInterp.gfDivV numer denom))
      = Spqr.Gf16FieldInstance.gfRingEquiv (Spqr.Gf16FieldInstance.GF16.ofU16 numer)
        * (Spqr.Gf16FieldInstance.gfRingEquiv (Spqr.Gf16FieldInstance.GF16.ofU16 denom))⁻¹ :=
  Spqr.RsDivInverse.gf_div_eq_inv numer denom hd

open Aeneas Std in
open Spqr.Gf (gfMulV) in
open Spqr.Gf16FieldAssembly (phi) in
/-- **Nonzero `(U16, gfMulV)` elements have a multiplicative inverse, UNCONDITIONAL on
irreducibility.** Same as `Gf16FieldAssembly.gfMulV_exists_inv` with the
`[Fact (Irreducible POLY_poly)]` binder dropped (still conditional on the multiplicative bridge
`hmul`, which is a separate computational fact, not an algebraic axiom). -/
theorem gfMulV_exists_inv_unconditional
    (hmul : ∀ a b, phi (gfMulV a b) = phi a * phi b)
    (a : Std.U16) (ha : a ≠ 0#u16) :
    ∃ b : Std.U16, gfMulV a b = 1#u16 :=
  Spqr.Gf16FieldAssembly.gfMulV_exists_inv hmul a ha

end Spqr.Gf16IrreducibleBridge
