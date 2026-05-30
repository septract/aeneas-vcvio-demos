/-
  Entry point: imports every demo so `lake build` checks them all.

  Each demo: real Rust (../rust) ──Charon/Aeneas──▶ Demos.Extracted.* (generated, gitignored)
  ──▶ a hand-written security proof in VCVio. See ../README.md.
-/
import Demos.OneTimePad
import Demos.StreamCipher.Word
import Demos.StreamCipher.LoopCorrectness
import Demos.StreamCipher.ByteArray
import Demos.Ratchet.Step
import Demos.Ratchet.Chain
import Demos.Ratchet.Chacha
import Demos.Ratchet.Cost
import Demos.Ratchet.ForwardSecrecy
import Demos.Ratchet.Generic
import Demos.Pqxdh.KeySchedule
import Demos.Spqr.Gf
import Demos.Spqr.Authenticator
import Demos.AuthChannel.Mac
import Demos.AuthChannel.SufCma
