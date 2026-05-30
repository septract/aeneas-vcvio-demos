/-
  Demo 2: a PRG-based stream cipher, with a *reduction* proof (harder than demo 1's
  information-theoretic perfect secrecy).

  The cipher encrypts a fixed message by XORing it with a PRG's output:
      enc(seed, msg) = G(seed) ⊕ msg
  where the XOR is the **Aeneas-extracted** `otp.xor`. We show that the ciphertext is
  pseudorandom — indistinguishable from a uniformly random value — by a tight reduction
  to the PRG's own security: breaking the cipher *is* breaking the PRG, via the reduction
  adversary `r ↦ A (r ⊕ msg)`. This is a genuine game-hop with advantage `= prgAdvantage`,
  not `0`; the base case (XOR-with-uniform = uniform) reuses the OTP uniformity argument.

  Not present in VCVio's example set (which has OneTimePad / ElGamal / Schnorr).
-/
import Demos.Extracted.Otp
import VCVio.CryptoFoundations.PRG
import VCVio.OracleComp.Constructions.BitVec
import VCVio.CryptoFoundations.Asymptotics.Negligible

open Aeneas Std OracleComp ENNReal PRGScheme

namespace StreamSecurity

variable {S : Type}

/-- XOR-by-`msg` as an involutive permutation of `BitVec n` (it is its own inverse). -/
def xorEquiv (n : ℕ) (msg : BitVec n) : BitVec n ≃ BitVec n where
  toFun r := r ^^^ msg
  invFun r := r ^^^ msg
  left_inv r := by simp [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  right_inv r := by simp [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- The PRG-based stream cipher for a fixed message, viewed as a `PRGScheme`:
its output is `G(seed) ⊕ msg`, where the `⊕` is the Aeneas-extracted `otp.xor`.
The `fail`/`div` branches are provably unreachable (`otp.xor` is total); they use a
distinguished *wrong* value so the totality lemma genuinely does the work. -/
def streamGen (prg : PRGScheme S (BitVec 64)) (msg : BitVec 64) : PRGScheme S (BitVec 64) where
  gen s := match otp.xor ⟨prg.gen s⟩ ⟨msg⟩ with
    | .ok c => c.bv
    | _ => 0

/-- **Value adequacy.** The cipher's output is exactly `G(seed) ⊕ msg`, i.e. the extracted
`otp.xor` computes `BitVec` xor and never fails. -/
@[simp] theorem streamGen_gen (prg : PRGScheme S (BitVec 64)) (msg : BitVec 64) (s : S) :
    (streamGen prg msg).gen s = prg.gen s ^^^ msg := rfl

/-- **Base case / OTP uniformity.** A uniform value XORed with a constant is still uniform,
so it is invisible to any distinguisher. (Reindex the sum by the xor-involution.) -/
theorem uniform_xor_invariant (A : PRGAdversary (BitVec 64)) (msg : BitVec 64) :
    Pr[= true | (do let r ← $ᵗ BitVec 64; A r)]
      = Pr[= true | (do let r ← $ᵗ BitVec 64; A (r ^^^ msg))] := by
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  simp only [probOutput_uniformSample]
  exact (Equiv.tsum_eq (xorEquiv 64 msg)
    (fun r => (Fintype.card (BitVec 64) : ℝ≥0∞)⁻¹ * Pr[= true | A r])).symm

/-- **Main reduction.** The stream cipher's pseudorandomness advantage (for any fixed
message and any distinguisher `A`) equals the underlying PRG's advantage against the
reduced adversary `r ↦ A (r ⊕ msg)`. In particular, if `G` is a secure PRG, the cipher's
ciphertexts are pseudorandom. -/
theorem streamGen_advantage [SampleableType S]
    (prg : PRGScheme S (BitVec 64)) (msg : BitVec 64) (A : PRGAdversary (BitVec 64)) :
    (streamGen prg msg).prgAdvantage A
      = prg.prgAdvantage (fun r => A (r ^^^ msg)) := by
  have hreal : Pr[= true | (streamGen prg msg).prgRealExp A]
      = Pr[= true | prg.prgRealExp (fun r => A (r ^^^ msg))] := by
    simp only [PRGScheme.prgRealExp, streamGen_gen]
  have hideal : Pr[= true | (prgIdealExp A : ProbComp Bool)]
      = Pr[= true | (prgIdealExp (fun r => A (r ^^^ msg)) : ProbComp Bool)] := by
    simp only [PRGScheme.prgIdealExp]
    exact uniform_xor_invariant A msg
  unfold PRGScheme.prgAdvantage
  rw [hreal, hideal]

/-- The explicit reduction adversary: distinguish the PRG's output by first XORing in the
fixed message. It is exactly `A` plus one XOR, so no heavier than `A`. -/
def reduction (msg : BitVec 64) (A : PRGAdversary (BitVec 64)) : PRGAdversary (BitVec 64) :=
  fun r => A (r ^^^ msg)

/-- **Security (concrete).** The stream cipher whose encryption is the Aeneas-extracted
`otp.xor` is at least as secure as the underlying PRG: every distinguisher's advantage
against the cipher is bounded by its PRG-advantage against the explicit `reduction`. -/
theorem streamGen_secure [SampleableType S]
    (prg : PRGScheme S (BitVec 64)) (msg : BitVec 64) (A : PRGAdversary (BitVec 64)) :
    (streamGen prg msg).prgAdvantage A ≤ prg.prgAdvantage (reduction msg A) :=
  _root_.le_of_eq (streamGen_advantage prg msg A)

/-- **Security (asymptotic).** Index the PRG and the distinguisher by a security parameter
(the cipher reuses the same fixed extracted `otp.xor` block at every `sp`). If the PRG family
is secure — its advantage against the `reduction` is negligible — then the cipher family is
secure: its distinguishing advantage is negligible. This is the honest end-to-end statement
that the extracted Rust, used as a stream cipher, is pseudorandom assuming `G` is a PRG. -/
theorem streamGen_secure_asymptotic {S : ℕ → Type} [∀ sp, SampleableType (S sp)]
    (G : ∀ sp, PRGScheme (S sp) (BitVec 64)) (msg : ℕ → BitVec 64)
    (A : ∀ _sp, PRGAdversary (BitVec 64))
    (hG : negligible fun sp => ENNReal.ofReal ((G sp).prgAdvantage (reduction (msg sp) (A sp)))) :
    negligible fun sp => ENNReal.ofReal ((streamGen (G sp) (msg sp)).prgAdvantage (A sp)) := by
  have heq : (fun sp => ENNReal.ofReal ((streamGen (G sp) (msg sp)).prgAdvantage (A sp)))
      = (fun sp => ENNReal.ofReal ((G sp).prgAdvantage (reduction (msg sp) (A sp)))) := by
    funext sp
    exact congrArg ENNReal.ofReal (streamGen_advantage (G sp) (msg sp) (A sp))
  rw [heq]; exact hG

end StreamSecurity
