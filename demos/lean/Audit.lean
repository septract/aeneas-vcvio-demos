/-
  Soundness audit: prints the axiom dependencies of every headline theorem.
  `#print axioms` is transitive, so anything relying on `sorry` would show `sorryAx`.
  Run via `make verify` (which fails the build if `sorryAx` appears).
-/
import Demos.OneTimePad
import Demos.StreamCipher.Word
import Demos.StreamCipher.LoopCorrectness
import Demos.StreamCipher.ByteArray

-- Demo 1: one-time pad, perfect secrecy (unconditional).
#print axioms OtpSecurity.otpAeneas_perfectSecrecyAt

-- Demo 2a: PRG stream cipher (word) — tight reduction + asymptotic security.
#print axioms StreamSecurity.streamGen_advantage
#print axioms StreamSecurity.streamGen_secure_asymptotic

-- Demo 2b: combiner loop correctness, and byte-array security (reduction + asymptotic).
#print axioms stream.combine_spec
#print axioms StreamByteSecurity.streamGen_advantage
#print axioms StreamByteSecurity.streamGen_secure_asymptotic
