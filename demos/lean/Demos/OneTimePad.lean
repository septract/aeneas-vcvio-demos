/-
  End-to-end: the Rust-extracted one-time pad is perfectly secret (VCVio's notion).

    otp.rs ──Charon/Aeneas──▶ `otp.xor` (Otp.lean) ──this file──▶ SymmEncAlg.perfectSecrecyAt

  `otpAeneas.encrypt` is driven by the genuinely-extracted `otp.xor`; we prove value
  adequacy (`otp.xor` is total and computes BitVec xor), reduce `encrypt` to `pure (k ^^^ m)`,
  and discharge VCVio's `perfectSecrecyAt` by reusing VCVio's XOR-uniformity lemmas — exactly
  as VCVio's own `oneTimePad` does, but with the encryption coming from real Rust.
-/
import Demos.Extracted.Otp
import VCVio.CryptoFoundations.SymmEncAlg
import VCVio.OracleComp.Constructions.BitVec

open Aeneas Std OracleComp ENNReal

namespace OtpSecurity

/-- A one-time pad whose encryption is the **Aeneas-extracted** `otp.xor`.
Keys/messages/ciphertexts are `BitVec 64`; `otp.xor` operates on `Std.U64`, which wraps a
`BitVec 64`. The `fail`/`div` branches are provably unreachable (`otp.xor` is total); they use
a distinguished *wrong* value so that the totality lemma genuinely does the work — a real
failure could not be silently masked. -/
def otpAeneas : SymmEncAlg ProbComp (BitVec 64) (BitVec 64) (BitVec 64) where
  keygen := $ᵗ BitVec 64
  encrypt k m :=
    match otp.xor ⟨k⟩ ⟨m⟩ with
    | .ok c => pure c.bv
    | _ => pure 0
  decrypt k c :=
    match otp.xor ⟨k⟩ ⟨c⟩ with
    | .ok m => pure (some m.bv)
    | _ => pure none

/-- **Value adequacy.** The Rust-extracted `otp.xor` is total and computes `BitVec` xor.
Stated as an equation in `Result`, so it certifies there is no `fail`/`div`. -/
theorem otp_xor_spec (k m : BitVec 64) : otp.xor ⟨k⟩ ⟨m⟩ = .ok ⟨k ^^^ m⟩ := rfl

@[simp] theorem keygen_eq : otpAeneas.keygen = ($ᵗ BitVec 64 : ProbComp (BitVec 64)) := rfl

/-- The extracted encryption reduces to the pure spec `pure (k ^^^ m)` (via totality). -/
@[simp] theorem encrypt_eq (k m : BitVec 64) :
    otpAeneas.encrypt k m = (pure (k ^^^ m) : ProbComp (BitVec 64)) := rfl

/-- **Perfect secrecy** (VCVio's `SymmEncAlg.perfectSecrecyAt`) of the Rust-extracted OTP. -/
theorem otpAeneas_perfectSecrecyAt : otpAeneas.perfectSecrecyAt := by
  intro mgen msg σ
  have hpair : Pr[= (msg, σ) | otpAeneas.PerfectSecrecyExp mgen]
      = Pr[= msg | mgen] * (Fintype.card (BitVec 64) : ℝ≥0∞)⁻¹ := by
    simpa [SymmEncAlg.PerfectSecrecyExp, monad_norm] using
      probOutput_pair_xor_uniform 64 (mx := mgen) msg σ
  have hcipher : Pr[= σ | otpAeneas.PerfectSecrecyCipherExp mgen]
      = (Fintype.card (BitVec 64) : ℝ≥0∞)⁻¹ := by
    simpa [SymmEncAlg.PerfectSecrecyCipherExp, SymmEncAlg.PerfectSecrecyExp, monad_norm] using
      probOutput_cipher_from_pair_uniform 64 (mx := mgen) σ
  rw [hpair, hcipher]

end OtpSecurity
