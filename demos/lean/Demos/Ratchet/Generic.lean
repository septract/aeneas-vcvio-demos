/-
  Demo 3 (width scaling) — the ratchet hybrid is width-agnostic.

  The security argument of `Chain.lean` is stated over the fixed types `Key = Array U8 32` and
  `Blk64 = Array U8 64`. But nothing in the hybrid actually uses the *width* (32/64 bytes): it
  only uses that the block generator is **length-doubling**, i.e. that there is a *bijection*
  `split : B ≃ K × K` (split a PRG block into next-chain-key and message-key). This file proves
  the hybrid generically over *any* key type `K`, block type `B`, and split bijection — so the
  result applies to a family whose key/block **width grows with the security parameter**
  (`gen_secure_asymptotic_width`).

  `Chain.lean`'s concrete result is the fixed-width instance of this (`K := Key`, `B := Blk64`,
  `split := splitPure`, `hsplit := splitPure_bijective`). We keep the two separate so the audited
  concrete development is undisturbed; this file is its width-generic generalization. The
  *extracted* node (ChaCha20) is inherently fixed-width, so the committed demo instantiates the
  framework at constant width — the genericity here shows the proof does not depend on that.

  This is the single source of the ratchet hybrid argument: `Chain.lean` instantiates it at the
  fixed byte-array width (`K := Key`, `B := Blk64`, `split := splitPure`), so its concrete
  `ratchetPRG` / `reduction` / `ratchet_advantage_le_sum` are defeq aliases of the generic ones.
-/
import VCVio.CryptoFoundations.PRG
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.CryptoFoundations.Asymptotics.Negligible
import Mathlib.Data.Fintype.Vector

open OracleComp ENNReal PRGScheme
open List (Vector)

namespace RatchetGeneric

/-- Sampling a pair uniformly is two independent uniform draws. (Generic helper, shared by the
fixed-width and width-scaling developments.) -/
theorem prod_uniform_bind {α β γ : Type} [Fintype α] [Inhabited α] [SampleableType α]
    [Fintype β] [Inhabited β] [SampleableType β] (g : α × β → ProbComp γ) :
    (($ᵗ (α × β)) >>= g) = (do let a ← $ᵗ α; let b ← $ᵗ β; g (a, b)) := by
  show (((·, ·) <$> ($ᵗ α) <*> ($ᵗ β)) >>= g) = _
  simp [monad_norm]

section FixedWidth

variable {K B : Type} [Fintype K] [Inhabited K] [SampleableType K] [SampleableType B]

/-! ## Generic construction over an abstract length-doubling split. -/

/-- Generic ratchet step: split the block generator's output into `(next chain key, message key)`. -/
def genStep (split : B → K × K) (G : K → B) (ck : K) : K × K := split (G ck)

/-- Generic message-key stream. -/
def genKeystream (split : B → K × K) (G : K → B) : (n : ℕ) → K → List.Vector K n
  | 0, _ => .nil
  | _ + 1, ck => (genStep split G ck).2 ::ᵥ genKeystream split G _ (genStep split G ck).1

/-- The generic ratchet as a PRG: seed = chain key, output = the `n` message keys. -/
def genRatchetPRG (split : B → K × K) (G : K → B) (n : ℕ) : PRGScheme K (List.Vector K n) where
  gen ck := genKeystream split G n ck

/-- The abstract block generator as a PRG (its pseudorandomness is the hardness assumption). -/
def genBlockPRG (G : K → B) : PRGScheme K B where gen := G

/-- Generic hybrid reduction stream. -/
def genRedStream (split : B → K × K) (G : K → B) (b : B) :
    (n : ℕ) → (i : ℕ) → ProbComp (List.Vector K n)
  | 0, _ => pure .nil
  | _ + 1, 0 => pure ((split b).2 ::ᵥ genKeystream split G _ (split b).1)
  | _ + 1, i + 1 => do
      let k ← $ᵗ K
      let rest ← genRedStream split G b _ i
      pure (k ::ᵥ rest)

/-- Generic reduction adversary for hop `i`. -/
def genReduction (split : B → K × K) (G : K → B) (n i : ℕ)
    (A : PRGAdversary (List.Vector K n)) : PRGAdversary B :=
  fun b => genRedStream split G b n i >>= A

/-! ## Generic helpers (the `uniformVec` lemma re-proved over an abstract key type). -/

/-- `n` independent uniform keys, over an abstract key type. -/
def genUniformVec (K : Type) [SampleableType K] : (n : ℕ) → ProbComp (List.Vector K n)
  | 0 => pure .nil
  | _ + 1 => do let k ← $ᵗ K; let rest ← genUniformVec K _; pure (k ::ᵥ rest)

omit [Fintype K] [Inhabited K] [SampleableType K] in
theorem gen_cons_bijective (m : ℕ) :
    Function.Bijective (fun p : K × List.Vector K m => p.1 ::ᵥ p.2) := by
  constructor
  · rintro ⟨k, v⟩ ⟨k', v'⟩ h
    obtain ⟨rfl, rfl⟩ := Vector.injective2_cons h
    rfl
  · intro w
    exact ⟨(w.head, w.tail), Vector.cons_head_tail w⟩

theorem gen_uniformVec_eq (n : ℕ) (A : List.Vector K n → ProbComp Bool) :
    Pr[= true | genUniformVec K n >>= A] = Pr[= true | ($ᵗ (List.Vector K n)) >>= A] := by
  induction n with
  | zero =>
    simp only [genUniformVec, pure_bind]
    rw [probOutput_bind_eq_tsum]
    rw [tsum_eq_single Vector.nil (by intro v hv; exact absurd (Subsingleton.elim v _) hv)]
    simp
  | succ m ih =>
    rw [← probOutput_bind_bijective_uniform_cross (α := K × List.Vector K m)
          (fun p => p.1 ::ᵥ p.2) (gen_cons_bijective m) A true]
    rw [prod_uniform_bind]
    simp only [genUniformVec, bind_assoc, pure_bind]
    refine probOutput_bind_congr' ($ᵗ K) true (fun k => ?_)
    exact ih (fun v => A (k ::ᵥ v))

/-! ## The generic hybrid: endpoints, glue, telescoping advantage bound. -/

omit [Fintype K] [Inhabited K] [SampleableType B] in
theorem genRedStream_real_zero (split : B → K × K) (G : K → B) (s : K) (n : ℕ) :
    genRedStream split G (G s) n 0 = pure (genKeystream split G n s) := by
  cases n with
  | zero => rfl
  | succ n => simp only [genRedStream, genKeystream, genStep]

omit [Fintype K] [Inhabited K] [SampleableType B] in
theorem gen_real_start (split : B → K × K) (G : K → B) (n : ℕ)
    (A : PRGAdversary (List.Vector K n)) :
    prgRealExp (genBlockPRG G) (genReduction split G n 0 A)
      = prgRealExp (genRatchetPRG split G n) A := by
  simp only [PRGScheme.prgRealExp, genReduction, genBlockPRG, genRatchetPRG]
  refine bind_congr fun s => ?_
  rw [genRedStream_real_zero, pure_bind]

theorem genGlue (split : B → K × K) (hsplit : Function.Bijective split) (G : K → B) :
    ∀ (n i : ℕ) (A : List.Vector K n → ProbComp Bool),
      Pr[= true | (do let b ← $ᵗ B; genRedStream split G b n i >>= A)]
        = Pr[= true | (do let s ← $ᵗ K; genRedStream split G (G s) n (i + 1) >>= A)] := by
  intro n
  induction n with
  | zero =>
    intro i A
    simp only [genRedStream, pure_bind]
    rw [probOutput_bind_const ($ᵗ B) (A .nil) true, probOutput_bind_const ($ᵗ K) (A .nil) true]
    simp
  | succ m ih =>
    intro i A
    cases i with
    | zero =>
      have hL : (do let b ← $ᵗ B; genRedStream split G b (m + 1) 0 >>= A)
          = ($ᵗ B) >>= fun b =>
              (fun p : K × K => A (p.2 ::ᵥ genKeystream split G m p.1)) (split b) := by
        simp only [genRedStream, pure_bind]
      have hR : (do let s ← $ᵗ K; genRedStream split G (G s) (m + 1) 1 >>= A)
          = (do let s ← $ᵗ K; let k ← $ᵗ K; A (k ::ᵥ genKeystream split G m s)) := by
        simp only [genRedStream, genRedStream_real_zero, pure_bind, bind_assoc]
      rw [hL, hR,
        probOutput_bind_bijective_uniform_cross (α := B) split hsplit
          (fun p : K × K => A (p.2 ::ᵥ genKeystream split G m p.1)) true,
        prod_uniform_bind]
    | succ j =>
      rw [show (do let b ← $ᵗ B; genRedStream split G b (m + 1) (j + 1) >>= A)
            = ($ᵗ B) >>= fun b => ($ᵗ K) >>= fun k =>
                genRedStream split G b m j >>= fun rest => A (k ::ᵥ rest) from by
          simp only [genRedStream, bind_assoc, pure_bind]]
      rw [probOutput_bind_bind_swap ($ᵗ B) ($ᵗ K)
            (fun b k => genRedStream split G b m j >>= fun rest => A (k ::ᵥ rest)) true]
      rw [probOutput_bind_congr' ($ᵗ K) true (fun k => ih j (fun rest => A (k ::ᵥ rest)))]
      rw [show (do let s ← $ᵗ K; genRedStream split G (G s) (m + 1) (j + 2) >>= A)
            = ($ᵗ K) >>= fun s => ($ᵗ K) >>= fun k =>
                genRedStream split G (G s) m (j + 1) >>= fun rest => A (k ::ᵥ rest) from by
          simp only [genRedStream, bind_assoc, pure_bind]]
      rw [probOutput_bind_bind_swap ($ᵗ K) ($ᵗ K)
            (fun s k => genRedStream split G (G s) m (j + 1) >>= fun rest => A (k ::ᵥ rest)) true]

omit [Fintype K] [Inhabited K] [SampleableType B] in
theorem genRedStream_diag (split : B → K × K) (G : K → B) (b : B) :
    ∀ n, genRedStream split G b n n = genUniformVec K n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp only [genRedStream, genUniformVec, ih]

omit [SampleableType B] in
theorem gen_ideal_end (split : B → K × K) (G : K → B) (n : ℕ)
    (A : PRGAdversary (List.Vector K n)) :
    Pr[= true | prgRealExp (genBlockPRG G) (genReduction split G n n A)]
      = Pr[= true | (prgIdealExp A : ProbComp Bool)] := by
  simp only [PRGScheme.prgRealExp, PRGScheme.prgIdealExp, genReduction, genBlockPRG]
  have hcomp : ($ᵗ K >>= fun s => genRedStream split G (G s) n n >>= A)
      = ($ᵗ K >>= fun _ => genUniformVec K n >>= A) := by
    refine bind_congr fun s => ?_
    rw [genRedStream_diag]
  rw [hcomp, probOutput_bind_const ($ᵗ K) (genUniformVec K n >>= A) true, gen_uniformVec_eq]
  simp

theorem gen_ideal_eq_next (split : B → K × K) (hsplit : Function.Bijective split) (G : K → B)
    (n i : ℕ) (A : PRGAdversary (List.Vector K n)) :
    Pr[= true | (prgIdealExp (genReduction split G n i A) : ProbComp Bool)]
      = Pr[= true | prgRealExp (genBlockPRG G) (genReduction split G n (i + 1) A)] := by
  simp only [PRGScheme.prgIdealExp, PRGScheme.prgRealExp, genReduction, genBlockPRG]
  exact genGlue split hsplit G n i A

/-- Hop `i`'s real-experiment winning probability (generic hybrid sequence). -/
noncomputable def genHyb (split : B → K × K) (G : K → B) (n : ℕ)
    (A : PRGAdversary (List.Vector K n)) (i : ℕ) : ℝ :=
  (Pr[= true | prgRealExp (genBlockPRG G) (genReduction split G n i A)]).toReal

/-- **Generic hybrid bound (width-agnostic).** For any length-doubling split bijection, the
ratchet keystream's advantage is bounded by the sum of the block PRG's per-step advantages. -/
theorem gen_advantage_le_sum (split : B → K × K) (hsplit : Function.Bijective split) (G : K → B)
    (n : ℕ) (A : PRGAdversary (List.Vector K n)) :
    (genRatchetPRG split G n).prgAdvantage A
      ≤ ∑ i ∈ Finset.range n, (genBlockPRG G).prgAdvantage (genReduction split G n i A) := by
  have hhop : ∀ i, (genBlockPRG G).prgAdvantage (genReduction split G n i A)
      = |genHyb split G n A i - genHyb split G n A (i + 1)| := by
    intro i
    unfold PRGScheme.prgAdvantage genHyb
    rw [gen_ideal_eq_next split hsplit G n i A]
  have hstart : (genRatchetPRG split G n).prgAdvantage A
      = |genHyb split G n A 0 - genHyb split G n A n| := by
    unfold PRGScheme.prgAdvantage genHyb
    rw [← gen_real_start split G n A, ← gen_ideal_end split G n A]
  rw [hstart]
  simp_rw [hhop]
  calc |genHyb split G n A 0 - genHyb split G n A n|
      = |∑ i ∈ Finset.range n, (genHyb split G n A i - genHyb split G n A (i + 1))| := by
        rw [Finset.sum_range_sub' (genHyb split G n A) n]
    _ ≤ ∑ i ∈ Finset.range n, |genHyb split G n A i - genHyb split G n A (i + 1)| :=
        Finset.abs_sum_le_sum_abs _ _

end FixedWidth

/-! ## Width scaling: the key/block width may grow with the security parameter.

`K`, `B`, the split bijection, and the block PRG are all indexed by the security parameter `sp`,
so the *width* of the keys and blocks scales with `sp` (unlike `Chain.lean`, where it is fixed).
If the per-step reductions have negligible advantage and the chain length is polynomial, the
ratchet keystream family is pseudorandom — the hybrid argument is uniform in the width. -/
theorem gen_secure_asymptotic_width
    (K B : ℕ → Type)
    [∀ sp, Fintype (K sp)] [∀ sp, Inhabited (K sp)] [∀ sp, SampleableType (K sp)]
    [∀ sp, SampleableType (B sp)]
    (split : ∀ sp, B sp → K sp × K sp) (hsplit : ∀ sp, Function.Bijective (split sp))
    (G : ∀ sp, K sp → B sp) (len : ℕ → ℕ)
    (A : ∀ sp, PRGAdversary (List.Vector (K sp) (len sp)))
    (ε : ℕ → ℝ≥0∞) (hε : negligible ε)
    (hbound : ∀ sp, ∀ i < len sp,
      ENNReal.ofReal ((genBlockPRG (G sp)).prgAdvantage
        (genReduction (split sp) (G sp) (len sp) i (A sp))) ≤ ε sp)
    (hlen : ∃ p : Polynomial ℕ, ∀ sp, len sp ≤ p.eval sp) :
    negligible (fun sp =>
      ENNReal.ofReal ((genRatchetPRG (split sp) (G sp) (len sp)).prgAdvantage (A sp))) := by
  obtain ⟨p, hp⟩ := hlen
  refine negligible_of_le (fun sp => ?_) (negligible_polynomial_mul hε p)
  calc ENNReal.ofReal ((genRatchetPRG (split sp) (G sp) (len sp)).prgAdvantage (A sp))
      ≤ ENNReal.ofReal (∑ i ∈ Finset.range (len sp),
          (genBlockPRG (G sp)).prgAdvantage (genReduction (split sp) (G sp) (len sp) i (A sp))) :=
        ENNReal.ofReal_le_ofReal
          (gen_advantage_le_sum (split sp) (hsplit sp) (G sp) (len sp) (A sp))
    _ = ∑ i ∈ Finset.range (len sp),
          ENNReal.ofReal ((genBlockPRG (G sp)).prgAdvantage
            (genReduction (split sp) (G sp) (len sp) i (A sp))) :=
        ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)
    _ ≤ ∑ _i ∈ Finset.range (len sp), ε sp :=
        Finset.sum_le_sum (fun i hi => hbound sp i (Finset.mem_range.mp hi))
    _ = (len sp : ℝ≥0∞) * ε sp := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (↑(p.eval sp) : ℝ≥0∞) * ε sp := by gcongr; exact_mod_cast hp sp

end RatchetGeneric
