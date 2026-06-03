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
import Demos.Ratchet.GenericIndexed
import Demos.Pqxdh.KeySchedule
import Demos.Pqxdh.Correctness
import Demos.Spqr.Gf
import Demos.Spqr.Gf16Field
import Demos.Spqr.RsBridge
import Demos.Spqr.RsRoundtrip
import Demos.Spqr.Authenticator
import Demos.Spqr.ChainSplit
import Demos.Spqr.RatchetPrg
import Demos.Spqr.AuthMac
import Demos.Spqr.StatesGraph
import Demos.AuthChannel.Mac
import Demos.AuthChannel.SufCma
import Demos.AuthChannel.MacCost
import Demos.KemDem.Composition
import Demos.Spqr.States
import Demos.Crypto.Sha256
import Demos.Crypto.Hkdf
import Demos.Crypto.HmacPrf
