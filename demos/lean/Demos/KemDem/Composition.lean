/-
  Demo 5 — KEM/DEM → PKE IND-CPA composition with a real extracted-Rust DEM.

  We instantiate VCVio's already-proven KEM+DEM → public-key encryption composition
  (`KEMScheme.composeWithDEM` and `ind_cpa_one_time_bias_advantage_compose_with_dem_le`)
  with a concrete *one-time symmetric* DEM whose encryption is the **Aeneas-extracted**
  32-byte stream-cipher XOR (`StreamByteSecurity.enc`, the extracted `combine` loop from
  Demo 2). No new security *game* is defined — every notion (KEM IND-CPA, DEM one-time
  IND-CPA, PKE one-time IND-CPA) is reused verbatim from VCVio, keeping the result on the
  supervisable side (see `TRUST.md`).

  Milestones:
  * M1 — the extracted-XOR DEM is perfectly correct (`streamDEM_perfectlyCorrect`).
  * M3 — for an abstract IND-CPA-secure KEM, the composed PKE is one-time IND-CPA secure,
    with advantage bounded by two KEM advantages plus the DEM advantage
    (`composed_ind_cpa_le`), and is perfectly correct (`composed_correct`).
  * M2 — the DEM's one-time IND-CPA advantage is bounded by the PRG advantage of an
    explicit reduction (`streamDEM_ind_cpa_le_prg`): one-time semantic security of the
    extracted stream cipher, expressed in VCVio's DEM game and reduced to PRG security.

  The DEM key type is a PRG seed `S`; message = ciphertext = the 32-byte `Block`.
  We work in `ProbComp = OracleComp unifSpec` with `runtime := ProbCompRuntime.probComp`.
-/
import Demos.StreamCipher.ByteArray
import VCVio.CryptoFoundations.KEMDEM

open OracleSpec OracleComp ENNReal Aeneas Std PRGScheme
open StreamByteSecurity (Block enc enc_spec enc_enc encEquiv uniform_perm_invariant streamGen)

namespace Demo5KemDem

/-! ## The extracted-stream-cipher DEM

`streamDEM prg` is a one-time symmetric DEM: the key is a PRG seed `s : S`, encryption
XORs the message with the PRG-stretched keystream `prg.gen s` via the Aeneas-extracted
`combine` loop (`StreamByteSecurity.enc`). Decryption is the same XOR (the cipher is its
own inverse, `enc_enc`). Both are deterministic, hence `pure`. -/

variable {S : Type}

/-- The 32-byte block type has decidable equality (it is `List.Vector U8 32`, and `U8`
wraps a `BitVec 8`), as required by the DEM correctness experiment. -/
instance : DecidableEq Block :=
  inferInstanceAs (DecidableEq (List.Vector Std.U8 32))

/-- The one-time symmetric DEM whose encryption is the extracted 32-byte stream-cipher XOR
keyed by a PRG seed. `M = C = Block`, `K = S` (a PRG seed). -/
def streamDEM (prg : PRGScheme S Block) :
    DEMScheme (OracleComp unifSpec) S Block Block where
  encrypt k m := pure (enc (prg.gen k) m)
  decrypt k c := pure (enc (prg.gen k) c)

/-! ## M1 — DEM perfect correctness -/

/-- Decryption inverts encryption pointwise: applying the extracted XOR with the *same*
keystream `ks` twice recovers the message, `enc ks (enc ks m) = m`. This is the
second-argument analogue of `enc_enc` (which fixes the message); here the key/keystream
is fixed, matching how the DEM uses one keystream `prg.gen k` for both directions. Proved
the same way as `enc_enc`, via the extracted loop's value adequacy `enc_spec`. -/
theorem enc_enc_key (ks m : Block) : enc ks (enc ks m) = m := by
  apply Subtype.ext
  apply List.ext_getElem!
  · simp only [Std.Array.length_eq]
  · intro n
    by_cases hn : n < 32
    · rw [enc_spec ks (enc ks m) n hn, enc_spec ks m n hn]
      -- ks ^^^ (ks ^^^ m) = m
      rw [U8.eq_equiv_bv_eq]
      simp only [UScalar.bv_xor, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    · rw [getElem!_neg, getElem!_neg] <;> (simp only [Std.Array.length_eq]; scalar_tac)

/-- **M1.** The extracted-XOR DEM is perfectly correct: for every seed and message, the
correctness experiment returns `true` with probability `1`. The body reduces to the
extracted-loop involution `enc (prg.gen k) (enc (prg.gen k) msg) = msg` (`enc_enc_key`). -/
theorem streamDEM_perfectlyCorrect (prg : PRGScheme S Block) :
    (streamDEM prg).PerfectlyCorrect ProbCompRuntime.probComp := by
  intro k msg
  -- The correctness experiment is a pure computation returning a single Boolean.
  simp only [ProbCompRuntime.evalDist, ProbCompRuntime.probComp,
    SPMFSemantics.ofHasEvalSPMF_evalDist, ← evalDist_def,
    DEMScheme.CorrectExp, streamDEM, bind_pure_comp, map_pure, evalDist_pure]
  -- `Pr[= true | pure (decide (enc (prg.gen k) (enc (prg.gen k) msg) = msg))] = 1`
  rw [enc_enc_key]
  simp

/-! ## Runtime coherence for `ProbCompRuntime.probComp`

The composition bound `ind_cpa_one_time_bias_advantage_compose_with_dem_le` takes four
coherence hypotheses on the runtime. For the canonical `probComp` runtime they all hold:
its `evalDist` is literally `HasEvalSPMF.toSPMF` (a monad homomorphism, so it preserves
`pure` and `bind`), its `liftProbComp` is the identity monad homomorphism, and `ProbComp`
distributions never fail (`OracleComp` has a `HasEvalPMF` instance). -/

/-- `probComp.evalDist` agrees with the ambient `𝒟[·]` semantics on `ProbComp`. -/
@[simp] theorem probComp_evalDist {α : Type} (mx : ProbComp α) :
    ProbCompRuntime.probComp.evalDist mx = 𝒟[mx] := rfl

theorem probComp_heval_pure {α : Type} (a : α) :
    ProbCompRuntime.probComp.evalDist (pure a : ProbComp α) = pure a := by
  rw [probComp_evalDist, evalDist_pure]

theorem probComp_heval_bind {α β : Type} (mx : ProbComp α) (f : α → ProbComp β) :
    ProbCompRuntime.probComp.evalDist (mx >>= f) =
      ProbCompRuntime.probComp.evalDist mx >>= fun a =>
        ProbCompRuntime.probComp.evalDist (f a) := by
  rw [probComp_evalDist, probComp_evalDist]
  simp_rw [probComp_evalDist]
  rw [evalDist_bind]

theorem probComp_heval_liftProbComp {α : Type} (pc : ProbComp α) :
    ProbCompRuntime.probComp.evalDist (ProbCompRuntime.probComp.liftProbComp pc) = 𝒟[pc] :=
  rfl

theorem probComp_hno_fail (mx : ProbComp Bool) :
    Pr[= true | ProbCompRuntime.probComp.evalDist mx] +
      Pr[= false | ProbCompRuntime.probComp.evalDist mx] = 1 := by
  rw [probComp_evalDist]
  -- `𝒟[mx] : SPMF Bool`; `Pr[= b | 𝒟[mx]]` on the SPMF coincides with `Pr[= b | mx]`,
  -- and `ProbComp` never fails, so the two Boolean outputs sum to `1`.
  have h := tsum_probOutput_add_probFailure (mx := mx)
  rw [tsum_fintype, Fintype.sum_bool, probFailure_eq_zero, add_zero] at h
  simpa only [probOutput_def] using h

/-! ## M2 — discharging the DEM term to the PRG assumption

The DEM term in `composed_ind_cpa_le` is itself bounded by the security of the underlying
PRG. The DEM one-time IND-CPA game encrypts `m_b ⊕ keystream` for a *uniform seed* `k`,
where `keystream = prg.gen k`. We build a PRG distinguisher that uses the PRG challenge
block directly as the keystream: if the block is `prg.gen k` the simulation *is* the DEM
game, while if the block is uniform then `enc r m_b` is a uniform block independent of `b`
(`enc · m` is a permutation, `encEquiv`), so the guess `b == b'` succeeds with probability
exactly `1/2` (bias `0`). Hence the DEM bias is at most twice the PRG advantage. -/

section DemToPRG

variable [SampleableType S]

/-- Uniform sampling is invariant under any permutation at the level of the *whole* output
distribution (not just the `true`-output probability) — the `evalDist` strengthening of
`StreamByteSecurity.uniform_perm_invariant`, needed to swap `enc r m₀` for `enc r m₁`
inside the all-random hybrid. -/
theorem evalDist_uniform_perm_invariant {R β : Type} [SampleableType R] [Fintype R]
    (A : R → ProbComp β) (e : R ≃ R) :
    𝒟[(do let r ← $ᵗ R; A r)] = 𝒟[(do let r ← $ᵗ R; A (e r))] := by
  refine evalDist_ext (fun x => ?_)
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  simp only [probOutput_uniformSample]
  exact (Equiv.tsum_eq e (fun r => (Fintype.card R : ℝ≥0∞)⁻¹ * Pr[= x | A r])).symm

/-- The PRG distinguisher used to discharge the DEM one-time IND-CPA term. Given a candidate
keystream block, it internally samples the hidden bit, asks the DEM adversary for its two
messages, encrypts the selected one by XOR-ing in the candidate block (the extracted
`enc`), and returns whether the adversary guessed the bit. When the block is `prg.gen k`
this is exactly the DEM game; when the block is uniform the guess is a fair coin. -/
def demReduction (dem : DEMScheme (OracleComp unifSpec) S Block Block)
    (adv : dem.IND_CPA_Adversary) : PRGScheme.PRGAdversary Block :=
  fun keystream => do
    let b ← $ᵗ Bool
    let (m₀, m₁, st) ← adv.chooseMessages
    let b' ← adv.distinguish st (enc keystream (if b then m₁ else m₀))
    pure (b == b')

/-- **M2.** The one-time IND-CPA advantage of the extracted-stream-cipher DEM is bounded by
twice the PRG advantage of `demReduction` — one-time semantic security of the stream cipher
reduced to PRG security. The factor `2` is the standard bias-vs-distinguishing conversion
(`IND_CPA_Advantage` is the single-game `boolBiasAdvantage`, twice the `|Pr[true] - 1/2|`
the PRG advantage measures). -/
theorem streamDEM_ind_cpa_le_prg (prg : PRGScheme S Block)
    (adv : (streamDEM prg).IND_CPA_Adversary) :
    (streamDEM prg).IND_CPA_Advantage ProbCompRuntime.probComp adv ≤
      2 * prg.prgAdvantage (demReduction (streamDEM prg) adv) := by
  set A := demReduction (streamDEM prg) adv with hA
  -- The DEM one-time IND-CPA game as a plain `ProbComp Bool` (probComp `evalDist`/`liftProbComp`
  -- collapse definitionally).
  set gameBody : ProbComp Bool := do
    let b ← $ᵗ Bool
    let k ← $ᵗ S
    let p ← adv.chooseMessages
    let b' ← adv.distinguish p.2.2 (enc (prg.gen k) (if b then p.2.1 else p.1))
    pure (b == b') with hgame
  -- Reduce the SPMF bias to the ProbComp bias of `gameBody`.
  show (𝒟[gameBody]).boolBiasAdvantage ≤ 2 * prg.prgAdvantage A
  have hbridge : (𝒟[gameBody]).boolBiasAdvantage = gameBody.boolBiasAdvantage := by
    unfold SPMF.boolBiasAdvantage ProbComp.boolBiasAdvantage
    simp only [SPMF.probOutput_eq_apply, probOutput_def]
  rw [hbridge, ProbComp.boolBiasAdvantage_eq_two_mul_abs_sub_half]
  -- The PRG advantage, expanded.
  unfold PRGScheme.prgAdvantage
  -- Real experiment: equals `gameBody` up to swapping the two independent uniform samples.
  have hreal : Pr[= true | prg.prgRealExp A] = Pr[= true | gameBody] := by
    rw [hgame, hA]
    simp only [PRGScheme.prgRealExp, demReduction]
    -- prgReal samples s then b; gameBody samples b then k(=s).
    rw [probOutput_bind_bind_swap ($ᵗ S) ($ᵗ Bool)]
  -- Ideal experiment: success probability is exactly 1/2 (bias 0).
  -- The bit-branched inner computation `g b` (sample keystream uniformly, encrypt the
  -- `b`-selected message, distinguish) is independent of `b`, because XOR-ing in a uniform
  -- keystream is a permutation (`encEquiv`).
  set g : Bool → ProbComp Bool := fun b => do
    let p ← adv.chooseMessages
    let r ← $ᵗ Block
    adv.distinguish p.2.2 (enc r (if b then p.2.1 else p.1)) with hg
  have hg_indep : 𝒟[g true] = 𝒟[g false] := by
    refine evalDist_ext (fun x => ?_)
    simp only [hg]
    refine probOutput_bind_congr (fun p _ => ?_)
    -- For fixed messages, `do r; distinguish st (enc r m_b)` is the same for both `b`,
    -- since each equals `do r; distinguish st r` by uniform permutation invariance.
    have htrue := evalDist_ext_iff.mp
      (evalDist_uniform_perm_invariant (fun r => adv.distinguish p.2.2 r) (encEquiv p.2.1)) x
    have hfalse := evalDist_ext_iff.mp
      (evalDist_uniform_perm_invariant (fun r => adv.distinguish p.2.2 r) (encEquiv p.1)) x
    simp only [encEquiv, Equiv.coe_fn_mk] at htrue hfalse
    simp only [if_true, Bool.false_eq_true, if_false]
    rw [← htrue, ← hfalse]
  have hideal : Pr[= true | prgIdealExp A] = 1 / 2 := by
    rw [hA]
    simp only [PRGScheme.prgIdealExp, demReduction]
    -- Pull the bit `b` to the front (swap with the uniform keystream `r`), then fold the
    -- keystream and message selection into `g b`.
    have hstep : Pr[= true | (do
          let r ← $ᵗ Block
          let b ← $ᵗ Bool
          let p ← adv.chooseMessages
          let b' ← adv.distinguish p.2.2 (enc r (if b then p.2.1 else p.1))
          pure (b == b') : ProbComp Bool)] =
        Pr[= true | (do
          let b ← $ᵗ Bool
          let b' ← g b
          pure (b == b') : ProbComp Bool)] := by
      rw [probOutput_bind_bind_swap ($ᵗ Block) ($ᵗ Bool)
        (fun r b => adv.chooseMessages >>= fun p =>
          adv.distinguish p.2.2 (enc r (if b then p.2.1 else p.1)) >>= fun b' => pure (b == b'))]
      refine probOutput_bind_congr' ($ᵗ Bool) true (fun b => ?_)
      simp only [hg, bind_assoc]
      rw [probOutput_bind_bind_swap ($ᵗ Block) adv.chooseMessages]
    rw [hstep]
    -- Apply the all-random hybrid lemma; `b == b'` is `decide (b = b')` for Booleans.
    simp only [show ∀ b b' : Bool, (b == b') = decide (b = b') from
      fun b b' => by cases b <;> cases b' <;> rfl]
    exact probOutput_decide_eq_uniformBool_half g hg_indep
  -- Assemble: bias = 2|Pr[true|gameBody] - 1/2| = 2|Pr[true|real] - Pr[true|ideal]| = 2·adv.
  rw [← hreal, hideal]
  rw [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one, abs_sub_comm]

end DemToPRG

/-! ## M3 — composition with an abstract KEM

For an arbitrary KEM scheme over the DEM's key space `S` (so `composeWithDEM` type-checks)
and any one-time IND-CPA adversary against the composed PKE, we specialize VCVio's bound:
the composed scheme's one-time IND-CPA advantage is at most two KEM advantages plus the
DEM advantage. We also transport perfect correctness from M1 (given KEM correctness). -/

section Compose

variable {PK SK CKEM : Type} [SampleableType S]

omit [SampleableType S] in
/-- **M3 (correctness).** If the abstract KEM is perfectly correct (and our extracted DEM
is, by M1), the composed KEM+DEM public-key encryption is perfectly correct. -/
theorem composed_correct [DecidableEq S]
    (kem : KEMScheme (OracleComp unifSpec) S PK SK CKEM)
    (prg : PRGScheme S Block)
    (hkem : Pr[= true | kem.CorrectExp] = 1) :
    ∀ msg, Pr[= true | (kem.composeWithDEM (streamDEM prg)).CorrectExp msg] = 1 :=
  KEMScheme.perfectlyCorrect_composeWithDEM kem (streamDEM prg) hkem
    (fun k msg => streamDEM_perfectlyCorrect prg k msg)

/-- **M3 (headline).** The one-time IND-CPA advantage of the composed KEM+DEM public-key
encryption (instantiated with our extracted-stream-cipher DEM) is bounded by the left and
right KEM IND-CPA advantages plus the DEM one-time IND-CPA advantage — a direct
specialization of VCVio's `ind_cpa_one_time_bias_advantage_compose_with_dem_le`, with the
four runtime-coherence hypotheses discharged for `probComp`. -/
theorem composed_ind_cpa_le
    (kem : KEMScheme (OracleComp unifSpec) S PK SK CKEM)
    (prg : PRGScheme S Block)
    (adversary : AsymmEncAlg.IND_CPA_Adv (kem.composeWithDEM (streamDEM prg))) :
    AsymmEncAlg.IND_CPA_OneTime_biasAdvantage
        (kem.composeWithDEM (streamDEM prg)) ProbCompRuntime.probComp adversary ≤
      kem.IND_CPA_Advantage ProbCompRuntime.probComp
        (kem.composeWithDEM_toKEMLeftReduction (streamDEM prg) adversary) +
      kem.IND_CPA_Advantage ProbCompRuntime.probComp
        (kem.composeWithDEM_toKEMRightReduction (streamDEM prg) adversary) +
      (streamDEM prg).IND_CPA_Advantage ProbCompRuntime.probComp
        (kem.composeWithDEM_toDEMReduction (streamDEM prg) adversary) :=
  kem.ind_cpa_one_time_bias_advantage_compose_with_dem_le (streamDEM prg)
    ProbCompRuntime.probComp adversary
    (fun a => probComp_heval_pure a)
    (fun mx f => probComp_heval_bind mx f)
    (fun pc => probComp_heval_liftProbComp pc)
    (fun mx => probComp_hno_fail mx)

/-- **M3 (end-to-end headline).** Chaining `composed_ind_cpa_le` with the M2 reduction
`streamDEM_ind_cpa_le_prg`: the composed KEM+DEM public-key encryption's one-time IND-CPA advantage
bottoms out on **just the KEM's IND-CPA security and the PRG's security** — at most the two KEM
IND-CPA advantages plus twice the PRG advantage of the explicit final distinguisher. No DEM term
remains; the DEM (our extracted stream cipher) is fully discharged to the PRG assumption. -/
theorem composed_ind_cpa_le_prg
    (kem : KEMScheme (OracleComp unifSpec) S PK SK CKEM)
    (prg : PRGScheme S Block)
    (adversary : AsymmEncAlg.IND_CPA_Adv (kem.composeWithDEM (streamDEM prg))) :
    AsymmEncAlg.IND_CPA_OneTime_biasAdvantage
        (kem.composeWithDEM (streamDEM prg)) ProbCompRuntime.probComp adversary ≤
      kem.IND_CPA_Advantage ProbCompRuntime.probComp
        (kem.composeWithDEM_toKEMLeftReduction (streamDEM prg) adversary) +
      kem.IND_CPA_Advantage ProbCompRuntime.probComp
        (kem.composeWithDEM_toKEMRightReduction (streamDEM prg) adversary) +
      2 * prg.prgAdvantage (demReduction (streamDEM prg)
        (kem.composeWithDEM_toDEMReduction (streamDEM prg) adversary)) := by
  have hcomp := composed_ind_cpa_le kem prg adversary
  have hdem := streamDEM_ind_cpa_le_prg prg
    (kem.composeWithDEM_toDEMReduction (streamDEM prg) adversary)
  linarith

/-! ## M3 — asymptotic security (reusing VCVio's `Negligible`)

Indexing the KEM, PRG, and adversary by a security parameter `sp`, the concrete bound
`composed_ind_cpa_le_prg` lifts to an asymptotic statement in VCVio's already-trusted
`negligible` framework (exactly as Demos 2–3 do, via `Negligible.lean`): if the KEM family
is IND-CPA-secure (negligible advantage against the two canonical KEM reductions) and the
PRG family is secure (negligible advantage against the final distinguisher), then the
composed KEM+DEM public-key encryption family's one-time IND-CPA advantage is negligible.
No new security *game* is introduced — every advantage notion is reused verbatim from
VCVio, keeping Demo 5 on the supervisable side. -/
theorem composed_secure_asymptotic
    {S : ℕ → Type} [∀ sp, SampleableType (S sp)]
    {PK SK CKEM : ℕ → Type}
    (kem : ∀ sp, KEMScheme (OracleComp unifSpec) (S sp) (PK sp) (SK sp) (CKEM sp))
    (prg : ∀ sp, PRGScheme (S sp) Block)
    (adversary : ∀ sp, AsymmEncAlg.IND_CPA_Adv ((kem sp).composeWithDEM (streamDEM (prg sp))))
    (hkemL : negligible fun sp => ENNReal.ofReal
      ((kem sp).IND_CPA_Advantage ProbCompRuntime.probComp
        ((kem sp).composeWithDEM_toKEMLeftReduction (streamDEM (prg sp)) (adversary sp))))
    (hkemR : negligible fun sp => ENNReal.ofReal
      ((kem sp).IND_CPA_Advantage ProbCompRuntime.probComp
        ((kem sp).composeWithDEM_toKEMRightReduction (streamDEM (prg sp)) (adversary sp))))
    (hprg : negligible fun sp => ENNReal.ofReal
      ((prg sp).prgAdvantage (demReduction (streamDEM (prg sp))
        ((kem sp).composeWithDEM_toDEMReduction (streamDEM (prg sp)) (adversary sp))))) :
    negligible fun sp => ENNReal.ofReal
      (AsymmEncAlg.IND_CPA_OneTime_biasAdvantage
        ((kem sp).composeWithDEM (streamDEM (prg sp))) ProbCompRuntime.probComp
        (adversary sp)) := by
  -- Dominate by the (negligible) bound `ofReal(kemL) + ofReal(kemR) + 2 * ofReal(prg)`.
  refine negligible_of_le (g := fun sp =>
    (ENNReal.ofReal ((kem sp).IND_CPA_Advantage ProbCompRuntime.probComp
        ((kem sp).composeWithDEM_toKEMLeftReduction (streamDEM (prg sp)) (adversary sp))) +
      ENNReal.ofReal ((kem sp).IND_CPA_Advantage ProbCompRuntime.probComp
        ((kem sp).composeWithDEM_toKEMRightReduction (streamDEM (prg sp)) (adversary sp)))) +
      2 * ENNReal.ofReal ((prg sp).prgAdvantage (demReduction (streamDEM (prg sp))
        ((kem sp).composeWithDEM_toDEMReduction (streamDEM (prg sp)) (adversary sp)))))
    (fun sp => ?_) ?_
  · -- Pointwise: push the real bound `composed ≤ kemL + kemR + 2·prg` through `ofReal`.
    have hbound := composed_ind_cpa_le_prg (kem sp) (prg sp) (adversary sp)
    calc ENNReal.ofReal _
        ≤ ENNReal.ofReal
            (((kem sp).IND_CPA_Advantage ProbCompRuntime.probComp
                ((kem sp).composeWithDEM_toKEMLeftReduction (streamDEM (prg sp)) (adversary sp)) +
              (kem sp).IND_CPA_Advantage ProbCompRuntime.probComp
                ((kem sp).composeWithDEM_toKEMRightReduction (streamDEM (prg sp)) (adversary sp))) +
              2 * (prg sp).prgAdvantage (demReduction (streamDEM (prg sp))
                ((kem sp).composeWithDEM_toDEMReduction (streamDEM (prg sp)) (adversary sp)))) :=
          ENNReal.ofReal_le_ofReal hbound
      _ ≤ ENNReal.ofReal
              ((kem sp).IND_CPA_Advantage ProbCompRuntime.probComp
                ((kem sp).composeWithDEM_toKEMLeftReduction (streamDEM (prg sp)) (adversary sp)) +
              (kem sp).IND_CPA_Advantage ProbCompRuntime.probComp
                ((kem sp).composeWithDEM_toKEMRightReduction (streamDEM (prg sp)) (adversary sp))) +
            ENNReal.ofReal
              (2 * (prg sp).prgAdvantage (demReduction (streamDEM (prg sp))
                ((kem sp).composeWithDEM_toDEMReduction (streamDEM (prg sp)) (adversary sp)))) :=
          ENNReal.ofReal_add_le
      _ ≤ _ := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
          exact add_le_add ENNReal.ofReal_add_le le_rfl
  · -- The dominating family is negligible.
    exact negligible_add (negligible_add hkemL hkemR)
      (negligible_const_mul hprg (by simp))

end Compose

end Demo5KemDem
