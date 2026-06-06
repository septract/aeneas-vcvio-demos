/-
  Triple Ratchet component bridge — the SPQR symmetric-ratchet keystream as the antecedent of
  Triple Ratchet's "KDF2 is a secure PRG" hypothesis.

  This file does NOT prove a new theorem about SPQR; it is an explicit, cited WIRING of two results
  we already proved over the EXTRACTED SPQR chain step (`Demos.Spqr.RatchetPrg`) to a *named
  hypothesis of a published theorem*:

      Triple Ratchet (TR).  A. Dodis, D. Jost, S. Katsumata, T. Prest, R. Schmidt,
      "The Triple Ratchet: A Bandwidth Efficient Hybrid-Secure Signal Protocol",
      EUROCRYPT 2025 / IACR ePrint 2025/078.

  -- The hypothesis we connect to (verbatim from the paper) ----------------------------------------

  * THEOREM 4.2 (Security of TR), p.21-22 (the bound spills onto p.22), third assumption bullet:
        "KDF1 is a secure PRF-PRNG, KDF2 is a secure PRG, and KDF3 is a secure dual-PRF."
  * KDF2 is the SINGLE-INPUT symmetric-ratchet chain step `KR ↦ (KR', K_aead)`:
        Fig. 9 (the receive algorithm of A), p.20,
          line 15:  ⟨KR, K^C_aead⟩ ← KDF2(KR)   (classical part),
          line 50:  ⟨KR, K_aead⟩   ← KDF2(KR)   (post-quantum part).
    SPQR's extracted `spqr_chain_next next ctr` realises exactly this step:
        genr8r = HKDF-Expand(HKDF-Extract(0³², next), info = (ctr+1)_be ‖ CHAIN_NEXT_LABEL, 64)
    split into `(KR', K_aead) = (genr8r[0..32], genr8r[32..64])`.
  * DEFINITION 2.6 (Pseudorandom generator (PRG)), p.10:
        "A KDF with one input argument is said to behave like a PRG, with domain {0,1}^λ and
         codomain Y, if  Adv^PRG_A := | Pr[x ←$ {0,1}^λ, y ← KDF(x), b' ←$ A(y) : b'=1]
                                       − Pr[y ←$ Y,        b' ←$ A(y) : b'=1] |  is negligible."
    This is *definitionally* the shape of VCVio's shipped `PRGScheme.prgAdvantage`:
        `prgRealExp prg A`  = `do let s ←$ S; A (prg.gen s)`   (real:  KDF output on a uniform seed),
        `prgIdealExp A`     = `do let r ←$ R; A r`             (ideal: uniform on the codomain),
        `prgAdvantage prg A = |Pr[real] − Pr[ideal]|`.
    We introduce NO new game — `prgAdvantage`/`prgRealExp`/`prgIdealExp`/`negligible` are VCVio's.
  * LEMMA 4.7, p.23 (confidentiality of TR): the KDF2-PRG assumption is *consumed* there as the
        `q · Adv^PRG_D(1^λ)`  term of the SM-conf-ss bound.

  -- What this file contributes (and, crucially, what it does NOT claim) ----------------------------

  SCOPE — DISCHARGED.  Over the EXTRACTED SPQR chain step (`spqrGen` / `spqr_chain_next`), we show
  that the SPQR symmetric-ratchet KEYSTREAM (seed = chain key, output = the emitted `K_aead` keys)
  is pseudorandom in VCVio's `PRGScheme` sense, REDUCED — via our unconditional `Σε` telescoping
  hybrid (`spqr_ratchet_advantage_le_sum`) and its asymptotic form (`spqr_ratchet_secure_asymptotic`)
  — to the per-hop PRG-ness of the extracted chain block. The keystream therefore satisfies the
  SHAPE of TR's "KDF2 is a secure PRG" hypothesis, over the real code rather than an abstract KDF2.

  SCOPE — STAYS AN ASSUMPTION (the PRG floor).  The per-hop PRG-ness of the chain block is the
  explicit premise `hblockPRG`. It is NOT proved here and is NOT an axiom. This is by DESIGN and is
  exactly the structure of TR itself: TR Thm 4.2 *assumes* "KDF2 is a secure PRG" rather than
  proving it; proving it would require the HKDF/HMAC-PRF → SHA-256 compression-function floor,
  which is a separate, unproven assumption outside this development. Our premise is the faithful
  Lean image of that assumption, phrased against the genuine extracted block.

  SCOPE — INHERITED MODELING BOUNDARY (from `RatchetPrg.lean` / `Chain.lean`).  The `Σε` hybrid
  treats each hop's seed (chain key) as UNIFORM, whereas the real chain key is HKDF-EXTRACTED from
  the previous block. The single-`G` `Chain.lean` development has the exact same gap; step-indexing
  inherits it, it does not introduce a new one. Reducing the Extract step (PRK pseudorandomness) is
  out of scope. We do not imply this seed-uniformity gap is closed.

  SCOPE — NOT CLAIMED.  We do NOT prove the PRG floor (SHA-256/HKDF pseudorandomness). We do NOT
  prove TR's CKA scheme security or its SM (secure-messaging) game, nor its FS/PCS windows
  (Δ_FS/Δ_PCS) — those are protocol-game-level statements; ours is the symmetric-ratchet,
  PRG-level *antecedent* that TR's Lemma 4.7 hybrid consumes. We define NO new security game.

  The honest one-line summary: *the extracted SPQR symmetric ratchet, modeled as VCVio's
  `PRGScheme`, has its keystream pseudorandomness reduced (via our `Σε` hybrid) to the per-hop
  PRG-ness of the extracted chain block — which is exactly the "KDF2 is a secure PRG" hypothesis
  that TR Thm 4.2 assumes and consumes as its `q · Adv^PRG` term.*
-/
import Demos.Spqr.RatchetPrg

open Aeneas Std OracleComp ENNReal PRGScheme
open List (Vector)

namespace Spqr.TripleRatchetComponent

open RatchetSecurity (Key Blk64)
open Spqr.RatchetPrg
  (spqrGen spqrRatchetPRG spqrReduction
   spqr_ratchet_advantage_le_sum spqr_ratchet_secure_asymptotic)
open RatchetGenericIndexed (genBlockPRGI)

/-! ## The KDF2-PRG hypothesis, named over the extracted SPQR chain block.

`tr_kdf2_PRG_hypothesis len A ε` is the Lean image of TR Thm 4.2's "KDF2 is a secure PRG" bullet,
*specialised to the genuine extracted chain block*: for every security parameter `sp` and every
hop `i < len sp`, the per-hop counter-indexed block PRG `genBlockPRGI (spqrGen 0) i` — whose `gen`
is exactly SPQR's `spqr_chain_next`-derived 64-byte block — has its `PRGScheme.prgAdvantage`
(Def 2.6's `Adv^PRG`) against the protocol reduction bounded by a single negligible `ε`.

This is a `def`-named PREDICATE on the inputs, NOT a proof: it makes the discharged-vs-assumed
boundary explicit and reusable. It is structurally identical to the `hbound` premise of
`spqr_ratchet_secure_asymptotic` (and to `RatchetSecurity.ratchet_secure_asymptotic`'s per-step
bound); it is NEVER an axiom. -/
def tr_kdf2_PRG_hypothesis
    (len : ℕ → ℕ)
    (A : ∀ sp, PRGAdversary (List.Vector Key (len sp)))
    (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ sp, ∀ i < len sp,
    ENNReal.ofReal ((genBlockPRGI (spqrGen 0) i).prgAdvantage
      (spqrReduction 0 (len sp) i (A sp))) ≤ ε sp

/-! ## The component lemma: SPQR's keystream discharges the SHAPE of TR's KDF2-PRG hypothesis. -/

/-- **The extracted SPQR symmetric ratchet supplies the antecedent of TR Thm 4.2's "KDF2 is a
secure PRG" bullet.**

UNDER the per-hop PRG assumption on the genuine extracted chain block — `tr_kdf2_PRG_hypothesis`,
the faithful Lean image of TR's *assumed* (not proved) "KDF2 is a secure PRG" hypothesis (Def 2.6,
p.10) — together with a polynomially-bounded chain length, the SPQR symmetric-ratchet keystream
(`spqrRatchetPRG 0 (len sp)`, modeled as VCVio's shipped `PRGScheme`) has NEGLIGIBLE
pseudorandomness advantage.

This is proved by INVOKING the already-banked `spqr_ratchet_secure_asymptotic` (whose engine is the
unconditional `Σε` telescoping hybrid `spqr_ratchet_advantage_le_sum`) — it re-proves nothing.

CITATION.  TR (Dodis, Jost, Katsumata, Prest, Schmidt; EUROCRYPT 2025 / ePrint 2025/078):
Thm 4.2 p.21-22 (assumption "KDF2 is a secure PRG"); KDF2 = Fig 9 p.20 lines 15/50 (`KR ↦ (KR',K_aead)`);
"secure PRG" = Def 2.6 p.10; consumed as the `q · Adv^PRG` term of Lemma 4.7 p.23.

SCOPE.  DISCHARGED: the keystream of the EXTRACTED step satisfies the SHAPE of the KDF2-PRG
antecedent. STAYS AN ASSUMPTION: the per-hop PRG floor (`hblockPRG`) — exactly as TR assumes it.
NOT CLAIMED: the HKDF/SHA-256 PRG floor itself; TR's CKA/SM game; TR's FS/PCS windows. NO new game. -/
theorem spqr_chain_step_discharges_TR_KDF2_PRG
    (len : ℕ → ℕ)
    (A : ∀ sp, PRGAdversary (List.Vector Key (len sp)))
    (ε : ℕ → ℝ≥0∞) (hε : negligible ε)
    (hblockPRG : tr_kdf2_PRG_hypothesis len A ε)
    (hlen : ∃ p : Polynomial ℕ, ∀ sp, len sp ≤ p.eval sp) :
    negligible (fun sp => ENNReal.ofReal ((spqrRatchetPRG 0 (len sp)).prgAdvantage (A sp))) :=
  spqr_ratchet_secure_asymptotic len A ε hε hblockPRG hlen

/-- **Concrete `Σε` form of the same bridge.** Unconditionally — with NO PRG assumption — the SPQR
keystream's `PRGScheme.prgAdvantage` (TR Def 2.6's `Adv^PRG`, p.10) is bounded by the sum over the
`n` hops of the per-hop extracted-chain-block PRG advantages. This is the protocol-shaped `Σε`
term: feeding it the KDF2-PRG hypothesis (each summand negligible) is precisely how TR's Lemma 4.7
(p.23) turns the assumption into its `q · Adv^PRG` contribution. A verbatim re-export of
`spqr_ratchet_advantage_le_sum`; proves nothing new. -/
theorem spqr_keystream_advantage_le_kdf2_sum (n : ℕ) (A : PRGAdversary (List.Vector Key n)) :
    (spqrRatchetPRG 0 n).prgAdvantage A
      ≤ ∑ i ∈ Finset.range n,
          (genBlockPRGI (spqrGen 0) (0 + i)).prgAdvantage (spqrReduction 0 n i A) :=
  spqr_ratchet_advantage_le_sum 0 n A

end Spqr.TripleRatchetComponent
