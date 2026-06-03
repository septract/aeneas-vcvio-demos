/-
  Step-indexed generic ratchet hybrid — the generator may DIFFER at every hop.

  `Generic.lean` (namespace `RatchetGeneric`) proves the ratchet hybrid over a single,
  step-invariant block generator `G : K → B`. SPQR's symmetric ratchet step is *counter-indexed*:
  the running counter is fed into the HKDF `info`, so the effective block generator differs at
  every hop. This file generalizes the hybrid to a **step-indexed family** `G : ℕ → K → B`,
  threading an absolute base step index `t` through every construction: the length-`n` keystream
  starting from base `t` uses generators `G t, G (t+1), …, G (t+n-1)`, and hop `i`'s reduction runs
  against the *distinct* `PRGScheme` `genBlockPRG (G (t+i))`.

  No new game is introduced: every advantage term is VCVio's `PRGScheme.prgAdvantage` on a
  `genBlockPRG (G j)` instance, and `prgRealExp` / `prgIdealExp` / `negligible` are reused verbatim.
  The per-step PRG-security assumption is carried as a hypothesis (a `prgAdvantage` bound premise),
  exactly as `RatchetGeneric.gen_secure_asymptotic_width` carries its single-generator bound — never
  an axiom. This is the sanctioned "separate development" pattern: the audited `Generic.lean` and
  `Chain.lean` are left untouched. The single-`G` development is the constant-family collapse
  (`G := fun _ => G₀`) of this one.

  We reuse `RatchetGeneric`'s width-independent helpers verbatim: `prod_uniform_bind`,
  `genUniformVec`, `gen_cons_bijective`, `gen_uniformVec_eq` — these are independent of `G`.
-/
import Demos.Ratchet.Generic

open OracleComp ENNReal PRGScheme
open List (Vector)

namespace RatchetGenericIndexed

open RatchetGeneric (prod_uniform_bind genUniformVec gen_uniformVec_eq)

section FixedWidth

variable {K B : Type} [Fintype K] [Inhabited K] [SampleableType K] [SampleableType B]

/-! ## Step-indexed construction over an abstract length-doubling split.

`G : ℕ → K → B` is a *family* of block generators; hop `j` uses `G j`. -/

/-- Step-indexed ratchet step at absolute index `t`: split the `t`-th generator's block output. -/
def genStepI (split : B → K × K) (G : ℕ → K → B) (t : ℕ) (ck : K) : K × K := split (G t ck)

/-- Step-indexed message-key stream from base index `t`: uses `G t, G (t+1), …, G (t+n-1)`. -/
def genKeystreamI (split : B → K × K) (G : ℕ → K → B) :
    (n : ℕ) → (t : ℕ) → K → List.Vector K n
  | 0, _, _ => .nil
  | _ + 1, t, ck =>
      (genStepI split G t ck).2 ::ᵥ genKeystreamI split G _ (t + 1) (genStepI split G t ck).1

/-- The step-indexed ratchet from base index `t` as a PRG. -/
def genRatchetPRGI (split : B → K × K) (G : ℕ → K → B) (n t : ℕ) :
    PRGScheme K (List.Vector K n) where
  gen ck := genKeystreamI split G n t ck

/-- The hop-`j` block generator as a PRG (its pseudorandomness is the per-step hardness assumption).
Definitionally `genBlockPRGI G j = RatchetGeneric.genBlockPRG (G j)`. -/
def genBlockPRGI (G : ℕ → K → B) (j : ℕ) : PRGScheme K B where gen := G j

/-- Step-indexed hybrid reduction stream. Base index `t` is the head of the *remaining* real
stream; the challenge block at relative hop `i` is the output of `G (t + i)`. The base only
advances (`t + 1`) on the real continuation after a split (relative hop `0`); the uniform-prefix
recursion (`i + 1`) keeps the same base `t`. -/
def genRedStreamI (split : B → K × K) (G : ℕ → K → B) (b : B) :
    (n : ℕ) → (t : ℕ) → (i : ℕ) → ProbComp (List.Vector K n)
  | 0, _, _ => pure .nil
  | _ + 1, t, 0 => pure ((split b).2 ::ᵥ genKeystreamI split G _ (t + 1) (split b).1)
  | _ + 1, t, i + 1 => do
      let k ← $ᵗ K
      let rest ← genRedStreamI split G b _ (t + 1) i
      pure (k ::ᵥ rest)

/-- Step-indexed reduction adversary for hop `i` (relative to base `t`); runs against
`genBlockPRGI G (t + i)`. -/
def genReductionI (split : B → K × K) (G : ℕ → K → B) (n t i : ℕ)
    (A : PRGAdversary (List.Vector K n)) : PRGAdversary B :=
  fun b => genRedStreamI split G b n t i >>= A

/-! ## The step-indexed hybrid: endpoints, glue, telescoping advantage bound.

Each lemma mirrors a `RatchetGeneric` lemma with the base index `t` threaded through and `G`
applied at the hop index. -/

omit [Fintype K] [Inhabited K] [SampleableType B] in
theorem genRedStreamI_real_zero (split : B → K × K) (G : ℕ → K → B) (s : K) (n t : ℕ) :
    genRedStreamI split G (G t s) n t 0 = pure (genKeystreamI split G n t s) := by
  cases n with
  | zero => rfl
  | succ n => simp only [genRedStreamI, genKeystreamI, genStepI]

omit [Fintype K] [Inhabited K] [SampleableType B] in
theorem gen_real_start (split : B → K × K) (G : ℕ → K → B) (n t : ℕ)
    (A : PRGAdversary (List.Vector K n)) :
    prgRealExp (genBlockPRGI G t) (genReductionI split G n t 0 A)
      = prgRealExp (genRatchetPRGI split G n t) A := by
  simp only [PRGScheme.prgRealExp, genReductionI, genBlockPRGI, genRatchetPRGI]
  refine bind_congr fun s => ?_
  rw [genRedStreamI_real_zero, pure_bind]

theorem genGlue (split : B → K × K) (hsplit : Function.Bijective split) (G : ℕ → K → B) :
    ∀ (n t i : ℕ) (A : List.Vector K n → ProbComp Bool),
      Pr[= true | (do let b ← $ᵗ B; genRedStreamI split G b n t i >>= A)]
        = Pr[= true |
            (do let s ← $ᵗ K; genRedStreamI split G (G (t + (i + 1)) s) n t (i + 1) >>= A)] := by
  intro n
  induction n with
  | zero =>
    intro t i A
    simp only [genRedStreamI, pure_bind]
    rw [probOutput_bind_const ($ᵗ B) (A .nil) true, probOutput_bind_const ($ᵗ K) (A .nil) true]
    simp
  | succ m ih =>
    intro t i A
    cases i with
    | zero =>
      have hL : (do let b ← $ᵗ B; genRedStreamI split G b (m + 1) t 0 >>= A)
          = ($ᵗ B) >>= fun b =>
              (fun p : K × K => A (p.2 ::ᵥ genKeystreamI split G m (t + 1) p.1)) (split b) := by
        simp only [genRedStreamI, pure_bind]
      have hR : (do let s ← $ᵗ K; genRedStreamI split G (G (t + 1) s) (m + 1) t 1 >>= A)
          = (do let s ← $ᵗ K; let k ← $ᵗ K; A (k ::ᵥ genKeystreamI split G m (t + 1) s)) := by
        simp only [genRedStreamI, genRedStreamI_real_zero, pure_bind, bind_assoc]
      rw [hL, hR,
        probOutput_bind_bijective_uniform_cross (α := B) split hsplit
          (fun p : K × K => A (p.2 ::ᵥ genKeystreamI split G m (t + 1) p.1)) true,
        prod_uniform_bind]
    | succ j =>
      rw [show (do let b ← $ᵗ B; genRedStreamI split G b (m + 1) t (j + 1) >>= A)
            = ($ᵗ B) >>= fun b => ($ᵗ K) >>= fun k =>
                genRedStreamI split G b m (t + 1) j >>= fun rest => A (k ::ᵥ rest) from by
          simp only [genRedStreamI, bind_assoc, pure_bind]]
      rw [probOutput_bind_bind_swap ($ᵗ B) ($ᵗ K)
            (fun b k => genRedStreamI split G b m (t + 1) j >>= fun rest => A (k ::ᵥ rest)) true]
      rw [probOutput_bind_congr' ($ᵗ K) true (fun k => ih (t + 1) j (fun rest => A (k ::ᵥ rest)))]
      rw [show (do let s ← $ᵗ K; genRedStreamI split G (G (t + (j + 1 + 1)) s) (m + 1) t (j + 1 + 1) >>= A)
            = ($ᵗ K) >>= fun s => ($ᵗ K) >>= fun k =>
                genRedStreamI split G (G (t + (j + 1 + 1)) s) m (t + 1) (j + 1) >>= fun rest =>
                  A (k ::ᵥ rest) from by
          simp only [genRedStreamI, bind_assoc, pure_bind]]
      rw [probOutput_bind_bind_swap ($ᵗ K) ($ᵗ K)
            (fun s k => genRedStreamI split G (G (t + (j + 1 + 1)) s) m (t + 1) (j + 1) >>= fun rest =>
              A (k ::ᵥ rest)) true]
      -- IH at base `t+1`, hop `j` yields generator `G ((t+1) + (j+1)) = G (t + (j+1+1))`.
      have hidx : (t + 1) + (j + 1) = t + (j + 1 + 1) := by ring
      rw [hidx]

omit [Fintype K] [Inhabited K] [SampleableType B] in
theorem genRedStreamI_diag (split : B → K × K) (G : ℕ → K → B) (b : B) :
    ∀ (n t : ℕ), genRedStreamI split G b n t n = genUniformVec K n := by
  intro n
  induction n with
  | zero => intro t; rfl
  | succ n ih => intro t; simp only [genRedStreamI, genUniformVec, ih]

omit [SampleableType B] in
theorem gen_ideal_end (split : B → K × K) (G : ℕ → K → B) (n t : ℕ)
    (A : PRGAdversary (List.Vector K n)) :
    Pr[= true | prgRealExp (genBlockPRGI G (t + n)) (genReductionI split G n t n A)]
      = Pr[= true | (prgIdealExp A : ProbComp Bool)] := by
  simp only [PRGScheme.prgRealExp, PRGScheme.prgIdealExp, genReductionI, genBlockPRGI]
  have hcomp : ($ᵗ K >>= fun s => genRedStreamI split G (G (t + n) s) n t n >>= A)
      = ($ᵗ K >>= fun _ => genUniformVec K n >>= A) := by
    refine bind_congr fun s => ?_
    rw [genRedStreamI_diag]
  rw [hcomp, probOutput_bind_const ($ᵗ K) (genUniformVec K n >>= A) true, gen_uniformVec_eq]
  simp

theorem gen_ideal_eq_next (split : B → K × K) (hsplit : Function.Bijective split) (G : ℕ → K → B)
    (n t i : ℕ) (A : PRGAdversary (List.Vector K n)) :
    Pr[= true | (prgIdealExp (genReductionI split G n t i A) : ProbComp Bool)]
      = Pr[= true |
          prgRealExp (genBlockPRGI G (t + (i + 1))) (genReductionI split G n t (i + 1) A)] := by
  simp only [PRGScheme.prgIdealExp, PRGScheme.prgRealExp, genReductionI, genBlockPRGI]
  exact genGlue split hsplit G n t i A

/-- Hop `i`'s real-experiment winning probability (step-indexed hybrid sequence); the `i`-th term
uses generator `G (t + i)`. -/
noncomputable def genHyb (split : B → K × K) (G : ℕ → K → B) (n t : ℕ)
    (A : PRGAdversary (List.Vector K n)) (i : ℕ) : ℝ :=
  (Pr[= true | prgRealExp (genBlockPRGI G (t + i)) (genReductionI split G n t i A)]).toReal

/-- **Step-indexed hybrid bound.** For any length-doubling split bijection and any step-indexed
generator family, the keystream's advantage (from base index `t`) is bounded by the sum of the
per-hop block PRG advantages, where hop `i` is against `genBlockPRGI G (t + i)`. -/
theorem gen_advantage_le_sum (split : B → K × K) (hsplit : Function.Bijective split)
    (G : ℕ → K → B) (n t : ℕ) (A : PRGAdversary (List.Vector K n)) :
    (genRatchetPRGI split G n t).prgAdvantage A
      ≤ ∑ i ∈ Finset.range n,
          (genBlockPRGI G (t + i)).prgAdvantage (genReductionI split G n t i A) := by
  have hhop : ∀ i, (genBlockPRGI G (t + i)).prgAdvantage (genReductionI split G n t i A)
      = |genHyb split G n t A i - genHyb split G n t A (i + 1)| := by
    intro i
    unfold PRGScheme.prgAdvantage genHyb
    rw [gen_ideal_eq_next split hsplit G n t i A]
    -- `genHyb (i+1)` is `real (genBlockPRGI G (t+(i+1))) (red (i+1))`, matching the RHS above.
  have hstart : (genRatchetPRGI split G n t).prgAdvantage A
      = |genHyb split G n t A 0 - genHyb split G n t A n| := by
    unfold PRGScheme.prgAdvantage genHyb
    rw [show t + 0 = t from rfl, ← gen_real_start split G n t A, ← gen_ideal_end split G n t A]
  rw [hstart]
  simp_rw [hhop]
  calc |genHyb split G n t A 0 - genHyb split G n t A n|
      = |∑ i ∈ Finset.range n, (genHyb split G n t A i - genHyb split G n t A (i + 1))| := by
        rw [Finset.sum_range_sub' (genHyb split G n t A) n]
    _ ≤ ∑ i ∈ Finset.range n, |genHyb split G n t A i - genHyb split G n t A (i + 1)| :=
        Finset.abs_sum_le_sum_abs _ _

end FixedWidth

/-! ## Width scaling, step-indexed.

`K`, `B`, the split bijection, and the step-indexed generator family are all indexed by the
security parameter `sp`. The single negligible `ε` uniformly bounds the per-hop advantage across
the whole family `{G sp i : i < len sp}` — the standard "PRG family is uniformly secure" hypothesis,
carried as a premise (not an axiom). If the chain length is polynomial, the step-indexed ratchet
keystream family (from base `0`) is pseudorandom. -/
theorem gen_secure_asymptotic_idx
    (K B : ℕ → Type)
    [∀ sp, Fintype (K sp)] [∀ sp, Inhabited (K sp)] [∀ sp, SampleableType (K sp)]
    [∀ sp, SampleableType (B sp)]
    (split : ∀ sp, B sp → K sp × K sp) (hsplit : ∀ sp, Function.Bijective (split sp))
    (G : ∀ sp, ℕ → K sp → B sp) (len : ℕ → ℕ)
    (A : ∀ sp, PRGAdversary (List.Vector (K sp) (len sp)))
    (ε : ℕ → ℝ≥0∞) (hε : negligible ε)
    (hbound : ∀ sp, ∀ i < len sp,
      ENNReal.ofReal ((genBlockPRGI (G sp) i).prgAdvantage
        (genReductionI (split sp) (G sp) (len sp) 0 i (A sp))) ≤ ε sp)
    (hlen : ∃ p : Polynomial ℕ, ∀ sp, len sp ≤ p.eval sp) :
    negligible (fun sp =>
      ENNReal.ofReal ((genRatchetPRGI (split sp) (G sp) (len sp) 0).prgAdvantage (A sp))) := by
  obtain ⟨p, hp⟩ := hlen
  refine negligible_of_le (fun sp => ?_) (negligible_polynomial_mul hε p)
  calc ENNReal.ofReal ((genRatchetPRGI (split sp) (G sp) (len sp) 0).prgAdvantage (A sp))
      ≤ ENNReal.ofReal (∑ i ∈ Finset.range (len sp),
          (genBlockPRGI (G sp) (0 + i)).prgAdvantage
            (genReductionI (split sp) (G sp) (len sp) 0 i (A sp))) :=
        ENNReal.ofReal_le_ofReal
          (gen_advantage_le_sum (split sp) (hsplit sp) (G sp) (len sp) 0 (A sp))
    _ = ∑ i ∈ Finset.range (len sp),
          ENNReal.ofReal ((genBlockPRGI (G sp) (0 + i)).prgAdvantage
            (genReductionI (split sp) (G sp) (len sp) 0 i (A sp))) :=
        ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)
    _ ≤ ∑ _i ∈ Finset.range (len sp), ε sp :=
        Finset.sum_le_sum (fun i hi => by
          rw [Nat.zero_add]; exact hbound sp i (Finset.mem_range.mp hi))
    _ = (len sp : ℝ≥0∞) * ε sp := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (↑(p.eval sp) : ℝ≥0∞) * ε sp := by gcongr; exact_mod_cast hp sp

end RatchetGenericIndexed
