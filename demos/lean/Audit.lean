/-
  Soundness audit: prints the axiom dependencies of every headline theorem.
  `#print axioms` is transitive, so anything relying on `sorry` would show `sorryAx`.
  Run via `make verify` (which fails the build if `sorryAx` appears).
-/
import Demos.OneTimePad
import Demos.StreamCipher.Word
import Demos.StreamCipher.LoopCorrectness
import Demos.StreamCipher.ByteArray
import Demos.Ratchet.Step
import Demos.Ratchet.Chain

-- Demo 1: one-time pad, perfect secrecy (unconditional).
#print axioms OtpSecurity.otpAeneas_perfectSecrecyAt

-- Demo 2a: PRG stream cipher (word) — tight reduction + asymptotic security.
#print axioms StreamSecurity.streamGen_advantage
#print axioms StreamSecurity.streamGen_secure_asymptotic

-- Demo 2b: combiner loop correctness, and byte-array security (reduction + asymptotic).
#print axioms stream.combine_spec
#print axioms StreamByteSecurity.streamGen_advantage
#print axioms StreamByteSecurity.streamGen_secure_asymptotic

-- Demo 3: symmetric KDF ratchet — value adequacy, the telescoping hybrid bound (Σε over the
-- chain), and asymptotic security under the poly-many-hops side condition.
#print axioms ratchet.ratchet_split_spec
#print axioms RatchetSecurity.ratchet_advantage_le_sum
#print axioms RatchetSecurity.ratchet_secure_asymptotic
