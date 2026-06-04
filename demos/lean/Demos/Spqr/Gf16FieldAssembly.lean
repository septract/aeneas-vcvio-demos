/-
  SPQR Reed–Solomon codec — Layer B, FIELD ASSEMBLY (CONDITIONAL).

  ## What this file establishes

  This file assembles the ring/field structure on the extracted field arithmetic
  `(U16, gfAddV = XOR, gfMulV = poly_reduce ∘ poly_mul)` along the NON-CIRCULAR route:
  the field-ness comes from Mathlib's quotient `AdjoinRoot POLY_poly`, transported back
  through the embedding `φ = AdjoinRoot.mk POLY_poly ∘ toPoly : U16 → AdjoinRoot POLY_poly`.

  The route requires `φ` to be a ring homomorphism. Its two halves split exactly as B-mul:

  * **Additive half (UNCONDITIONAL, banked):** `toPoly_gfAddV` (XOR = polynomial addition)
    + `map_add` of `AdjoinRoot.mk` gives `φ (gfAddV a b) = φ a + φ b`. Proved here.

  * **Injectivity (UNCONDITIONAL):** a `U16` embeds to a polynomial of degree < 16; two such
    differ by a polynomial of degree < 16 = `natDegree POLY_poly`, so `POLY_poly` divides the
    difference only if it is `0`. Hence `φ` is injective. Proved here, NO irreducibility.

  * **Multiplicative half (the B-mul GAP):** `φ (gfMulV a b) = φ a * φ b` is exactly the full
    multiplicative bridge `toPoly (gfMulV a b) ≡ toPoly a · toPoly b  (mod POLY_poly)`. Stage 1
    (`toPoly32_polyMulV`, the carryless multiply = polynomial product) is banked; Stage 2
    (`poly_reduce` = remainder mod POLY) is the documented open gap. So this half is NOT proved
    unconditionally — it is carried as an EXPLICIT, SATISFIABLE HYPOTHESIS `hmul` (never an axiom).

  ## The headlines (CONDITIONAL on the stated, satisfiable premises — NOT axioms)

  Under the multiplicative-bridge hypothesis `hmul`, we transport the COMMUTATIVE-RING
  multiplicative laws onto `(U16, gfAddV, gfMulV)` — proved by reflecting equalities through the
  injective ring map `φ` (so the laws come from `AdjoinRoot`'s genuine ring structure, NOT
  assumed on `U16`). The ring laws need NO irreducibility. The FIELD (inverse) law additionally
  needs `Irreducible POLY_poly` (B-irr, open) — so it too is carried as an explicit `Fact` premise.

  Every headline mentions the extracted `gfMulV`/`gfAddV` (it is a statement ABOUT the codec's
  field ops), with the unproved field laws appearing only as honest hypotheses, never axioms.

  ## What is NOT done / faked

  - NO `axiom`, `sorry`, `native_decide`, or circular field instance.
  - `Irreducible POLY_poly` (B-irr) is OPEN; carried as `[Fact (Irreducible POLY_poly)]`.
  - The multiplicative bridge `hmul` (full B-mul, incl. the open Stage-2 reduction correctness)
    is carried as an explicit hypothesis. Both premises are SATISFIABLE (the field really is
    GF(2¹⁶) and `POLY_poly` really is irreducible), so the conditional theorems are non-vacuous.
-/
import Demos.Spqr.Gf16Field
import Demos.Spqr.Gf16Mul
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Field.ZMod

open Aeneas Std Result
open Spqr.Gf
open Polynomial

namespace Spqr.Gf16FieldAssembly

/-- `2` is prime — makes `ZMod 2` a field (hence an integral domain / `NoZeroDivisors`), which
the degree-divisibility argument for `phi_injective` uses. Standard, not a field-law cheat. -/
instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

open Spqr.Gf16Field (bitZ toPoly POLY_poly POLY_poly_monic POLY_poly_natDegree
  POLY_poly_ne_zero gfAddV_comm toPoly_gfAddV)
open Spqr.Gf16Mul (coeff_toPoly)

/-! ### 1. The degree bound on `toPoly` (UNCONDITIONAL building block) -/

/-- Every `U16` embeds to a polynomial of degree `< 16` (only coefficients `0..15` can be set). -/
theorem toPoly_degree_lt (a : Std.U16) : (toPoly a).degree < 16 := by
  unfold Spqr.Gf16Field.toPoly
  apply _root_.lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
  rw [Finset.sup_lt_iff (by decide)]
  intro i hi
  simp only [Finset.mem_range] at hi
  exact _root_.lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le i (bitZ a i)) (by exact_mod_cast hi)

/-! ### 2. `toPoly` is injective (UNCONDITIONAL building block)

If `toPoly a = toPoly b`, then for each bit index `i < 16` the coefficients agree, so the bits of
`a` and `b` agree; since both values are `< 2^16` (no high bits), `a = b`. -/

/-- The embedding `toPoly : U16 → (ZMod 2)[X]` is injective. -/
theorem toPoly_injective : Function.Injective toPoly := by
  intro a b hab
  -- coefficients agree at every index
  have hcoeff : ∀ i, bitZ a i = bitZ b i := by
    intro i
    have := congrArg (fun p => Polynomial.coeff p i) hab
    simpa only [coeff_toPoly] using this
  -- turn coefficient equality into bit equality
  have hbit : ∀ i, a.val.testBit i = b.val.testBit i := by
    intro i
    have h := hcoeff i
    unfold Spqr.Gf16Field.bitZ at h
    by_cases ha : a.val.testBit i <;> by_cases hb : b.val.testBit i <;>
      simp only [ha, hb, if_true] at h ⊢ <;> first
        | rfl
        | (exfalso; revert h; decide)
  -- equal bit patterns ⇒ equal Nat values ⇒ equal U16
  have hval : a.val = b.val := Nat.eq_of_testBit_eq hbit
  exact UScalar.val_eq_imp_iff.mpr hval

/-! ### 3. The quotient embedding `φ = mk ∘ toPoly` and its proven properties -/

/-- The embedding into the quotient `(ZMod 2)[X] ⧸ (POLY_poly)`. The field-ness of the target
comes from `AdjoinRoot` (Mathlib), NOT assumed on `U16` — this is the NON-CIRCULAR route. -/
noncomputable def phi (a : Std.U16) : AdjoinRoot POLY_poly :=
  AdjoinRoot.mk POLY_poly (toPoly a)

/-- **`φ` is additive** (the additive half of the ring hom): from the banked XOR = poly-add bridge
`toPoly_gfAddV` and `map_add` of the ring hom `AdjoinRoot.mk`. UNCONDITIONAL. -/
theorem phi_gfAddV (a b : Std.U16) : phi (gfAddV a b) = phi a + phi b := by
  unfold phi
  rw [toPoly_gfAddV, map_add]

/-- **`φ` is injective.** If `mk (toPoly a) = mk (toPoly b)` then `POLY_poly ∣ toPoly a - toPoly b`;
but that difference has degree `< 16 = natDegree POLY_poly`, so it is `0`, i.e. `toPoly a = toPoly b`,
and `toPoly` is injective. NO irreducibility needed. -/
theorem phi_injective : Function.Injective phi := by
  intro a b hab
  unfold phi at hab
  rw [AdjoinRoot.mk_eq_mk] at hab
  -- the difference has degree < 16
  have hdeg : (toPoly a - toPoly b).degree < POLY_poly.degree := by
    have h1 : (toPoly a - toPoly b).degree < 16 :=
      _root_.lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
        (max_lt (toPoly_degree_lt a) (toPoly_degree_lt b))
    have h2 : POLY_poly.degree = (16 : ℕ) := by
      rw [Polynomial.degree_eq_natDegree POLY_poly_ne_zero, POLY_poly_natDegree]
    rw [h2]; exact_mod_cast h1
  have hzero : toPoly a - toPoly b = 0 :=
    Polynomial.eq_zero_of_dvd_of_degree_lt hab hdeg
  have : toPoly a = toPoly b := sub_eq_zero.mp hzero
  exact toPoly_injective this

/-- **`φ` sends the multiplicative unit `1#u16` to `1`** (`toPoly 1 = 1`, then `mk 1 = 1`).
UNCONDITIONAL. -/
theorem phi_one : phi 1#u16 = 1 := by
  unfold phi
  have htoPoly : toPoly 1#u16 = 1 := by
    apply Polynomial.ext
    intro n
    rw [coeff_toPoly, Polynomial.coeff_one]
    unfold Spqr.Gf16Field.bitZ
    have h1 : (1#u16 : Std.U16).val = 1 := by decide
    rw [h1]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have hb : Nat.testBit 1 n = false := by
        rw [Bool.eq_false_iff, ne_eq, Nat.testBit_one_eq_true_iff_self_eq_zero]; omega
      rw [hb]; simp; omega
  rw [htoPoly, map_one]

/-! ### 3b. `φ` is SURJECTIVE (UNCONDITIONAL)

Every residue of `AdjoinRoot POLY_poly` has a unique representative of degree `< 16` (reduce mod
the degree-16 monic `POLY_poly`), and every degree-`<16` polynomial over `ZMod 2` is `toPoly` of
the `U16` whose bit `i` is `coeff i`. So `φ` is onto — NO irreducibility, NO B-mul needed. This
makes the field-inverse law (section 5) depend ONLY on the two genuine gaps (`hmul` + `Irreducible`),
not on an extra surjectivity assumption. -/

/-- The bit `j` of the indicator bit-sum `∑_{i<n} [P i]·2^i` is `[j < n] ∧ [P j]`. The standard
"bits of a sum of distinct powers of two" fact, by induction on `n`. -/
theorem testBit_indicator_sum (P : Nat → Prop) [DecidablePred P] (n j : Nat) :
    (∑ i ∈ Finset.range n, if P i then 2 ^ i else 0).testBit j
      = (decide (j < n) && decide (P j)) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hbound : (∑ i ∈ Finset.range k, if P i then 2 ^ i else 0) < 2 ^ k := by
      have hle : (∑ i ∈ Finset.range k, if P i then 2 ^ i else 0) ≤ ∑ i ∈ Finset.range k, 2 ^ i := by
        apply Finset.sum_le_sum; intro i _; split
        · exact _root_.le_refl _
        · exact Nat.zero_le _
      have hg : (∑ i ∈ Finset.range k, (2 : Nat) ^ i) = 2 ^ k - 1 := by
        rw [Nat.geomSum_eq (by norm_num) k]; simp
      have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
      omega
    rw [Finset.sum_range_succ]
    set S := ∑ i ∈ Finset.range k, if P i then 2 ^ i else 0 with hSdef
    by_cases hPk : P k
    · -- the added term is 2^k; S < 2^k so S and 2^k have disjoint bits
      simp only [hPk, if_true]
      have hSk : S.testBit k = false := Nat.testBit_eq_false_of_lt hbound
      rcases lt_trichotomy j k with hjk | hjk | hjk
      · -- j < k : low bit unaffected by + 2^k
        rw [show S + 2 ^ k = 2 ^ k + S from by ring, Nat.testBit_two_pow_add_gt hjk S, ih]
        rw [decide_eq_true hjk, decide_eq_true (show j < k + 1 by omega)]
      · -- j = k : the new top bit is set
        subst hjk
        rw [show S + 2 ^ j = 2 ^ j + S from by ring, Nat.testBit_two_pow_add_eq S j, hSk]
        simp [hPk]
      · -- j > k : above both
        have hbig : S + 2 ^ k < 2 ^ j := by
          calc S + 2 ^ k < 2 ^ k + 2 ^ k := by omega
            _ = 2 ^ (k + 1) := by ring
            _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [Nat.testBit_eq_false_of_lt hbig]
        have hj1 : ¬ j < k + 1 := by omega
        simp [hj1]
    · -- the added term is 0
      simp only [hPk, if_false, add_zero, ih]
      rcases lt_trichotomy j k with hjk | hjk | hjk
      · rw [decide_eq_true hjk, decide_eq_true (show j < k + 1 by omega)]
      · subst hjk
        rw [decide_eq_false hPk, Bool.and_false, Bool.and_false]
      · rw [decide_eq_false (show ¬ j < k by omega),
            decide_eq_false (show ¬ j < k + 1 by omega)]

/-- The bit-sum used by `fromPoly` is `< 2^16` (so `ofNatCore` does not wrap). -/
theorem fromPoly_sum_lt (q : (ZMod 2)[X]) :
    (∑ i ∈ Finset.range 16, if q.coeff i = 1 then 2 ^ i else 0) < 2 ^ UScalarTy.U16.numBits := by
  have hle : (∑ i ∈ Finset.range 16, if q.coeff i = 1 then 2 ^ i else 0)
      ≤ ∑ i ∈ Finset.range 16, 2 ^ i := by
    apply Finset.sum_le_sum; intro i _; split
    · exact _root_.le_refl _
    · exact Nat.zero_le _
  have hg : (∑ i ∈ Finset.range 16, (2 : Nat) ^ i) = 65535 := by decide
  have hnb : (2 : Nat) ^ UScalarTy.U16.numBits = 65536 := by decide
  omega

/-- The inverse embedding: the `U16` whose bit `i` is `1` exactly when `q.coeff i = 1` (read off the
`16` low coefficients of `q`). For a degree-`<16` poly this recovers it under `toPoly`. -/
noncomputable def fromPoly (q : (ZMod 2)[X]) : Std.U16 :=
  Std.U16.ofNatCore (∑ i ∈ Finset.range 16, if q.coeff i = 1 then 2 ^ i else 0) (fromPoly_sum_lt q)

/-- `fromPoly q`'s value is exactly the bit-sum (no wraparound, since it is `< 2^16`). -/
theorem fromPoly_val (q : (ZMod 2)[X]) :
    (fromPoly q).val = ∑ i ∈ Finset.range 16, if q.coeff i = 1 then 2 ^ i else 0 := by
  unfold fromPoly
  exact Std.U16.ofNatCore_val_eq (fromPoly_sum_lt q)

/-- Bit `n` of `fromPoly q` is set iff `n < 16` and `q.coeff n = 1` (from `testBit_indicator_sum`). -/
theorem fromPoly_testBit (q : (ZMod 2)[X]) (n : Nat) :
    (fromPoly q).val.testBit n = (decide (n < 16) && decide (q.coeff n = 1)) := by
  rw [fromPoly_val]
  exact testBit_indicator_sum (fun i => q.coeff i = 1) 16 n

/-- **Roundtrip: `toPoly (fromPoly q) = q` for any degree-`<16` polynomial `q`.** This is the
left inverse of `toPoly` on the degree-`<16` representatives — the heart of surjectivity of `φ`.
UNCONDITIONAL (NO irreducibility, NO B-mul). -/
theorem toPoly_fromPoly (q : (ZMod 2)[X]) (hq : q.degree < 16) : toPoly (fromPoly q) = q := by
  apply Polynomial.ext
  intro n
  rw [coeff_toPoly]
  unfold Spqr.Gf16Field.bitZ
  rw [fromPoly_testBit]
  by_cases hn : n < 16
  · -- in range: the indicator recovers the coefficient (ZMod 2 ∈ {0,1})
    rw [decide_eq_true hn, Bool.true_and]
    -- the coefficient is 0 or 1 in ZMod 2
    have hc : q.coeff n = 0 ∨ q.coeff n = 1 := by
      generalize q.coeff n = c; revert c; decide
    rcases hc with hc | hc
    · rw [hc]; simp
    · rw [hc]; simp
  · -- out of range: coeff is 0 (degree < 16) and the bit is unset
    rw [decide_eq_false hn, Bool.false_and]
    have hcz : q.coeff n = 0 := by
      apply Polynomial.coeff_eq_zero_of_degree_lt
      exact _root_.lt_of_lt_of_le hq (by exact_mod_cast (show (16 : ℕ) ≤ n by omega))
    rw [hcz, if_neg (by decide)]

/-- **`φ` is surjective** onto `AdjoinRoot POLY_poly`: any residue equals `φ` of some `U16`.
Reduce a representative mod the degree-16 monic `POLY_poly` to degree `< 16`, then recover it via
`fromPoly`. UNCONDITIONAL. -/
theorem phi_surjective : Function.Surjective phi := by
  intro r
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective r
  -- the canonical degree-<16 representative
  have hqdeg : (p %ₘ POLY_poly).degree < 16 := by
    have hlt := Polynomial.degree_modByMonic_lt p POLY_poly_monic
    have hpd : POLY_poly.degree = (16 : ℕ) := by
      rw [Polynomial.degree_eq_natDegree POLY_poly_ne_zero, POLY_poly_natDegree]
    rw [hpd] at hlt; exact_mod_cast hlt
  refine ⟨fromPoly (p %ₘ POLY_poly), ?_⟩
  unfold phi
  rw [toPoly_fromPoly (p %ₘ POLY_poly) hqdeg]
  -- mk (p %ₘ POLY) = mk p = r, since they differ by a POLY-multiple
  rw [← hp, AdjoinRoot.mk_eq_mk]
  have hmd := Polynomial.modByMonic_add_div p POLY_poly
  exact ⟨-(p /ₘ POLY_poly), by linear_combination hmd⟩

/-! ### 4. The CONDITIONAL ring/field laws on the extracted `(U16, gfAddV, gfMulV)`

These are the FIELD-ASSEMBLY headlines. The field-ness comes from the genuine ring/field
`AdjoinRoot POLY_poly` (Mathlib), reflected back through the injective ring map `φ` — the
NON-CIRCULAR route. The multiplicative compatibility of `φ` is exactly the full B-mul bridge
(Stage 1 banked + Stage 2 open), so it is carried as the EXPLICIT, SATISFIABLE hypothesis

  `hmul : ∀ a b, phi (gfMulV a b) = phi a * phi b`

(equivalently `toPoly (gfMulV a b) ≡ toPoly a · toPoly b  (mod POLY_poly)`), NEVER an axiom.
Under `hmul` alone (NO irreducibility) we get the COMMUTATIVE-RING multiplicative laws on the
extracted field-multiply; the field (inverse) law additionally needs `Fact (Irreducible POLY_poly)`
(B-irr, open), also carried as an explicit premise. Each theorem mentions the extracted `gfMulV` /
`gfAddV` — it is a statement ABOUT the codec's field ops under the stated (satisfiable) hypotheses. -/

/-- **`gfMulV` is commutative**, CONDITIONAL on the multiplicative bridge `hmul`. Reflected through
the injective `φ` from the commutativity of `AdjoinRoot POLY_poly`. NO irreducibility needed. -/
theorem gfMulV_comm (hmul : ∀ a b, phi (gfMulV a b) = phi a * phi b) (a b : Std.U16) :
    gfMulV a b = gfMulV b a := by
  apply phi_injective
  rw [hmul, hmul, mul_comm]

/-- **`gfMulV` is associative**, CONDITIONAL on `hmul`. NO irreducibility needed. -/
theorem gfMulV_assoc (hmul : ∀ a b, phi (gfMulV a b) = phi a * phi b) (a b c : Std.U16) :
    gfMulV (gfMulV a b) c = gfMulV a (gfMulV b c) := by
  apply phi_injective
  rw [hmul, hmul, hmul, hmul, mul_assoc]

/-- **`1#u16` is a right identity for `gfMulV`**, CONDITIONAL on `hmul`. -/
theorem gfMulV_one (hmul : ∀ a b, phi (gfMulV a b) = phi a * phi b) (a : Std.U16) :
    gfMulV a 1#u16 = a := by
  apply phi_injective
  rw [hmul, phi_one, mul_one]

/-- **`1#u16` is a left identity for `gfMulV`**, CONDITIONAL on `hmul`. -/
theorem gfMulV_one_left (hmul : ∀ a b, phi (gfMulV a b) = phi a * phi b) (a : Std.U16) :
    gfMulV 1#u16 a = a := by
  apply phi_injective
  rw [hmul, phi_one, one_mul]

/-- **`gfMulV` distributes over `gfAddV`** (left), CONDITIONAL on `hmul`. Combines the banked
additive bridge `phi_gfAddV` with `hmul` and `AdjoinRoot`'s ring distributivity. -/
theorem gfMulV_gfAddV_distrib (hmul : ∀ a b, phi (gfMulV a b) = phi a * phi b) (a b c : Std.U16) :
    gfMulV a (gfAddV b c) = gfAddV (gfMulV a b) (gfMulV a c) := by
  apply phi_injective
  rw [hmul, phi_gfAddV, phi_gfAddV, hmul, hmul, mul_add]

/-- **`gfMulV` distributes over `gfAddV`** (right), CONDITIONAL on `hmul`. -/
theorem gfMulV_gfAddV_distrib_right (hmul : ∀ a b, phi (gfMulV a b) = phi a * phi b)
    (a b c : Std.U16) :
    gfMulV (gfAddV a b) c = gfAddV (gfMulV a c) (gfMulV b c) := by
  apply phi_injective
  rw [hmul, phi_gfAddV, phi_gfAddV, hmul, hmul, add_mul]

/-! ### 5. The FIELD law (multiplicative inverse): CONDITIONAL on `hmul` AND `Irreducible POLY_poly`

`AdjoinRoot POLY_poly` is a FIELD exactly when `POLY_poly` is irreducible (B-irr, OPEN). Under
`[Fact (Irreducible POLY_poly)]` it has inverses, and — `φ` being an injective ring map onto the
finite subring `φ '' univ` (the degree-`<16` residues, all of `AdjoinRoot POLY_poly`) — every
nonzero `gfMulV`-element has a `gfMulV`-inverse. We state the EXISTENCE of a two-sided inverse for
nonzero elements (the field law), reflected through `φ`. The irreducibility is a PREMISE
(`Fact …`), never an axiom; it is satisfiable, so the theorem is non-vacuous. -/

/-- **Nonzero elements of `(U16, gfMulV)` have a multiplicative inverse**, CONDITIONAL on the
multiplicative bridge `hmul` AND `Irreducible POLY_poly` (B-irr). For `a ≠ 0#u16`, there is some
`b` with `gfMulV a b = 1#u16`. Proved by inverting `φ a ≠ 0` in the field `AdjoinRoot POLY_poly`
and pulling the inverse residue back through `φ` — using the UNCONDITIONAL `phi_surjective`
(no extra surjectivity assumption). NO axiom: irreducibility is the explicit `Fact` premise. -/
theorem gfMulV_exists_inv [Fact (Irreducible POLY_poly)]
    (hmul : ∀ a b, phi (gfMulV a b) = phi a * phi b)
    (a : Std.U16) (ha : a ≠ 0#u16) :
    ∃ b : Std.U16, gfMulV a b = 1#u16 := by
  -- φ a ≠ 0, since φ is injective and φ 0 = 0
  have hphi0 : phi 0#u16 = 0 := by
    unfold phi
    have : toPoly 0#u16 = 0 := by
      apply Polynomial.ext; intro n
      rw [coeff_toPoly]; unfold Spqr.Gf16Field.bitZ
      have : (0#u16 : Std.U16).val = 0 := by decide
      rw [this]; simp
    rw [this, map_zero]
  have hane : phi a ≠ 0 := by
    intro h; apply ha; apply phi_injective; rw [h, hphi0]
  -- invert in the field AdjoinRoot POLY_poly; pull the inverse residue back through φ (surjective)
  obtain ⟨y, hy⟩ := phi_surjective (phi a)⁻¹
  exact ⟨y, by apply phi_injective; rw [hmul, hy, phi_one, mul_inv_cancel₀ hane]⟩

end Spqr.Gf16FieldAssembly
