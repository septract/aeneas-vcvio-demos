/-
  PQXDH node — key-agreement *correctness* (functional, no security game).

  The headline of the Option-B mirror: the initiator's `pqxdh_initiate` and the recipient's
  `pqxdh_accept` derive the **same** `HandshakeKeys` for corresponding parameters, *given* the two
  cryptographic floor properties as explicit hypotheses (NOT axioms):

    • X25519 symmetry      — `dh(a, pub b) = dh(b, pub a)`, here stated as equality of the two
                             corresponding `x25519_agree` call results per leg; and
    • ML-KEM round-trip    — `decaps(sk, encaps(pk).ct) = encaps(pk).ss`, stated as equality of the
                             recipient's `mlkem_decapsulate` result with the initiator's `ss`.

  Route (per `KeySchedule.lean`'s spec layer):
    per-leg correspondences  ⇒  initiator's `secret_input` array = recipient's (as a Lean value)
    ⇒  same HKDF input  ⇒  HKDF determinism gives the same `okm`  ⇒  `derive_split` determinism
    ⇒  the three 32-byte keys (`root_key`, `chain_key`, `pqr_key`) are identical.

  Because the secret-input assembly, the HKDF call, and the split are *deterministic Lean
  functions* of their inputs, value-equality of the agreed legs propagates to value-equality of the
  derived `HandshakeKeys` by plain congruence — no per-byte bookkeeping is needed at the headline.
  The opaque primitives stay abstract; the floor properties are quantified hypotheses on exactly the
  legs the two roles agree on (see the spec §2.2 leg table).

  NB: this file proves no security property and introduces no security game. It is a functional
  correctness result over the extracted orchestration `pqxdh_initiate`/`pqxdh_accept`, taking the
  X25519/ML-KEM floor properties as explicit HYPOTHESES (it adds NO new axiom: the five gate-confined
  PQXDH primitive axioms are exactly the ones `KeySchedule.lean` already uses).
-/
import Demos.Pqxdh.KeySchedule

open Aeneas Std Result

namespace Pqxdh

noncomputable section

/-! ### Helper: the shared `okm → HandshakeKeys` tail is a function of `okm`.

Both roles, after assembling `secret_input` and calling HKDF, run the *same*
`derive_split okm` and package the three slices. We isolate that tail so the headline is a
congruence over equal `okm`. -/

/-- The deterministic tail shared by both roles in the no-OPK path, as a pure `Result`
expression in the agreed legs.  This is exactly the body of `pqxdh_initiate` /
`pqxdh_accept` from `secret_input` onward (no-OPK branch), abstracted over the four legs. -/
def okm_no_opk (dh1 dh2 dh3 ss : Array Std.U8 32#usize) :
    Result (Array Std.U8 96#usize) := do
  let secret_input ← pqxdh.pqxdh_secret_input dh1 dh2 dh3 ss
  let s ← lift (Array.to_slice secret_input)
  let s1 ← lift (Array.to_slice pqxdh.PQXDH_LABEL)
  pqxdh.hkdf_sha256_derive s s1

/-- The deterministic tail shared by both roles in the with-OPK path. -/
def okm_with_opk (dh1 dh2 dh3 dh4 ss : Array Std.U8 32#usize) :
    Result (Array Std.U8 96#usize) := do
  let secret_input ← pqxdh.pqxdh_secret_input_with_opk dh1 dh2 dh3 dh4 ss
  let s ← lift (Array.to_slice secret_input)
  let s1 ← lift (Array.to_slice pqxdh.PQXDH_LABEL)
  pqxdh.hkdf_sha256_derive s s1

/-! ### Key projections.

The two roles return different envelopes (`InitiatorAgreement` carrying the Kyber ciphertext, vs.
`Option HandshakeKeys` carrying the recipient's success/failure of the base-key guard).  We project
out the shared `HandshakeKeys` from each, as a `Result HandshakeKeys`, so the headline is a clean
value-equality `initiatorKeys … = recipientKeys …`. -/

/-- The `HandshakeKeys` derived by the initiator, as a `Result` (dropping the Kyber ciphertext). -/
def initiatorKeys (params : pqxdh.InitiatorParameters) (coins : Array Std.U8 32#usize) :
    Result pqxdh.HandshakeKeys := do
  let a ← pqxdh.pqxdh_initiate params coins
  ok a.keys

/-- The `HandshakeKeys` derived by the recipient, as a `Result` (`none` from the base-key guard
becomes a `fail`, so the projection is total exactly when the recipient accepts). -/
def recipientKeys (params : pqxdh.RecipientParameters) : Result pqxdh.HandshakeKeys := do
  let o ← pqxdh.pqxdh_accept params
  match o with
  | some k => ok k
  | none => fail .panic

/-! ### The shared `okm → keys` tail propagates value-equality.

`derive_split okm` then packaging into a `HandshakeKeys` is a deterministic function of `okm`.  We
prove the initiator's and recipient's *key projection* both equal `okm >>= derive_split >>= package`
for their respective `okm`; equal `okm` then yields equal keys by `rw`. -/

/-- `derive_split` then packaging is a deterministic function of `okm`. -/
def keysOfOkm (okm : Result (Array Std.U8 96#usize)) : Result pqxdh.HandshakeKeys := do
  let (root_key, chain_key, pqr_key) ← okm >>= pqxdh.derive_split
  ok { root_key, chain_key, pqr_key }

theorem keysOfOkm_congr {okm okm' : Result (Array Std.U8 96#usize)} (h : okm = okm') :
    keysOfOkm okm = keysOfOkm okm' := by rw [h]

/-! ### Per-role reductions to `keysOfOkm`.

These are pure equational rewrites: each role's key projection, in its respective OPK branch, is
exactly `keysOfOkm` of that role's `okm_*` tail, with the agreed legs bound monadically in the
role's own call order.  No floor property is used here — this is structural unfolding of the
extracted orchestration's deterministic plumbing. -/

theorem initiatorKeys_no_opk (params : pqxdh.InitiatorParameters) (coins : Array Std.U8 32#usize)
    (hopk : params.their_one_time_pre_key = none) :
    initiatorKeys params coins =
      (do
        let dh1 ← pqxdh.x25519_agree params.our_identity_key_pair.private_key
                    params.their_signed_pre_key
        let dh2 ← pqxdh.x25519_agree params.our_ephemeral_key_pair.private_key
                    params.their_identity_key
        let dh3 ← pqxdh.x25519_agree params.our_ephemeral_key_pair.private_key
                    params.their_signed_pre_key
        let (ss, _ct) ← pqxdh.mlkem_encapsulate params.their_kyber_pre_key coins
        keysOfOkm (okm_no_opk dh1 dh2 dh3 ss)) := by
  unfold initiatorKeys pqxdh.pqxdh_initiate
  simp [hopk, okm_no_opk, keysOfOkm, bind_assoc]

theorem initiatorKeys_with_opk (params : pqxdh.InitiatorParameters) (coins : Array Std.U8 32#usize)
    (opk : Array Std.U8 32#usize) (hopk : params.their_one_time_pre_key = some opk) :
    initiatorKeys params coins =
      (do
        let dh1 ← pqxdh.x25519_agree params.our_identity_key_pair.private_key
                    params.their_signed_pre_key
        let dh2 ← pqxdh.x25519_agree params.our_ephemeral_key_pair.private_key
                    params.their_identity_key
        let dh3 ← pqxdh.x25519_agree params.our_ephemeral_key_pair.private_key
                    params.their_signed_pre_key
        let (ss, _ct) ← pqxdh.mlkem_encapsulate params.their_kyber_pre_key coins
        let dh4 ← pqxdh.x25519_agree params.our_ephemeral_key_pair.private_key opk
        keysOfOkm (okm_with_opk dh1 dh2 dh3 dh4 ss)) := by
  unfold initiatorKeys pqxdh.pqxdh_initiate
  simp [hopk, okm_with_opk, keysOfOkm, bind_assoc]

theorem recipientKeys_no_opk (params : pqxdh.RecipientParameters)
    (hcanon : pqxdh.ec_is_canonical params.their_ephemeral_key = ok true)
    (hopk : params.our_one_time_pre_key_pair = none) :
    recipientKeys params =
      (do
        let dh1 ← pqxdh.x25519_agree params.our_signed_pre_key_pair.private_key
                    params.their_identity_key
        let dh2 ← pqxdh.x25519_agree params.our_identity_key_pair.private_key
                    params.their_ephemeral_key
        let dh3 ← pqxdh.x25519_agree params.our_signed_pre_key_pair.private_key
                    params.their_ephemeral_key
        let ss ← pqxdh.mlkem_decapsulate params.our_kyber_secret_key
                    params.their_kyber_ciphertext
        keysOfOkm (okm_no_opk dh1 dh2 dh3 ss)) := by
  unfold recipientKeys pqxdh.pqxdh_accept
  simp [hcanon, hopk, okm_no_opk, keysOfOkm, bind_assoc]

theorem recipientKeys_with_opk (params : pqxdh.RecipientParameters)
    (hcanon : pqxdh.ec_is_canonical params.their_ephemeral_key = ok true)
    (opk_pair : pqxdh.KeyPair) (hopk : params.our_one_time_pre_key_pair = some opk_pair) :
    recipientKeys params =
      (do
        let dh1 ← pqxdh.x25519_agree params.our_signed_pre_key_pair.private_key
                    params.their_identity_key
        let dh2 ← pqxdh.x25519_agree params.our_identity_key_pair.private_key
                    params.their_ephemeral_key
        let dh3 ← pqxdh.x25519_agree params.our_signed_pre_key_pair.private_key
                    params.their_ephemeral_key
        let ss ← pqxdh.mlkem_decapsulate params.our_kyber_secret_key
                    params.their_kyber_ciphertext
        let dh4 ← pqxdh.x25519_agree opk_pair.private_key params.their_ephemeral_key
        keysOfOkm (okm_with_opk dh1 dh2 dh3 dh4 ss)) := by
  unfold recipientKeys pqxdh.pqxdh_accept
  simp [hcanon, hopk, okm_with_opk, keysOfOkm, bind_assoc]

/-! ### The headline: corresponding initiator and recipient derive identical keys.

We now combine the per-role reductions with the two floor properties, specialized to the legs the
two roles agree on:

  • **X25519 symmetry** (`dh(a, pub b) = dh(b, pub a)`): each of the three (or four) `x25519_agree`
    legs on the initiator side produces the *same `Result`* as the corresponding recipient leg.
    Here this is a hypothesis on exactly the matched legs — the spec §2.2 leg table:

        init DH1 = x25519(IK_A.priv, SPK_B)   ↔   recip DH1 = x25519(SPK_B.priv, IK_A)
        init DH2 = x25519(EK_A.priv, IK_B)    ↔   recip DH2 = x25519(IK_B.priv,  EK_A)
        init DH3 = x25519(EK_A.priv, SPK_B)   ↔   recip DH3 = x25519(SPK_B.priv, EK_A)
        init DH4 = x25519(EK_A.priv, OPK_B)   ↔   recip DH4 = x25519(OPK_B.priv, EK_A)   (OPK path)

  • **ML-KEM correctness** (`decaps(sk, encaps(pk).ct) = encaps(pk).ss`): the recipient's
    `mlkem_decapsulate` recovers exactly the shared secret `ss` the initiator's `mlkem_encapsulate`
    produced — stated as: encapsulation succeeds with `(ss, ct)`, and decapsulation of that
    ciphertext recovers `ss`.

Given these, both roles assemble the *same* `secret_input` (byte-equal, building on
`pqxdh_secret_input_spec`), feed it to the *same* deterministic HKDF call, and `derive_split` the
*same* `okm` — so the three derived keys are identical.  Because the secret-input assembly, HKDF,
and split are deterministic Lean functions, value-equality of the agreed legs propagates by
`keysOfOkm_congr`; no per-byte bookkeeping is needed at the headline. -/

/-- **PQXDH key-agreement correctness, no one-time-prekey path.**  For corresponding parameters
(the X25519 legs symmetric per the §2.2 leg table, and ML-KEM round-trip recovering the initiator's
shared secret), the initiator's and recipient's derived `HandshakeKeys` are **identical**.

The hypotheses `hleg1`/`hleg2`/`hleg3` (X25519 symmetry on the three matched legs) and
`hencaps`/`hdecaps` (ML-KEM correctness) are the cryptographic floor properties, supplied as
explicit hypotheses on exactly the legs the two roles agree on — no new axiom is introduced. -/
theorem pqxdh_keys_agree_no_opk
    (pI : pqxdh.InitiatorParameters) (pR : pqxdh.RecipientParameters)
    (coins : Array Std.U8 32#usize)
    (ss : Array Std.U8 32#usize) (ct : Array Std.U8 1569#usize)
    (hIopk : pI.their_one_time_pre_key = none)
    (hRopk : pR.our_one_time_pre_key_pair = none)
    (hcanon : pqxdh.ec_is_canonical pR.their_ephemeral_key = ok true)
    -- X25519 symmetry, specialized to the three agreed legs:
    (hleg1 : pqxdh.x25519_agree pI.our_identity_key_pair.private_key pI.their_signed_pre_key
           = pqxdh.x25519_agree pR.our_signed_pre_key_pair.private_key pR.their_identity_key)
    (hleg2 : pqxdh.x25519_agree pI.our_ephemeral_key_pair.private_key pI.their_identity_key
           = pqxdh.x25519_agree pR.our_identity_key_pair.private_key pR.their_ephemeral_key)
    (hleg3 : pqxdh.x25519_agree pI.our_ephemeral_key_pair.private_key pI.their_signed_pre_key
           = pqxdh.x25519_agree pR.our_signed_pre_key_pair.private_key pR.their_ephemeral_key)
    -- ML-KEM correctness: encaps yields (ss, ct); decaps of that ct recovers ss:
    (hencaps : pqxdh.mlkem_encapsulate pI.their_kyber_pre_key coins = ok (ss, ct))
    (hdecaps : pqxdh.mlkem_decapsulate pR.our_kyber_secret_key pR.their_kyber_ciphertext = ok ss) :
    initiatorKeys pI coins = recipientKeys pR := by
  rw [initiatorKeys_no_opk pI coins hIopk,
      recipientKeys_no_opk pR hcanon hRopk,
      hleg1, hleg2, hleg3, hencaps, hdecaps]
  simp

/-- **PQXDH key-agreement correctness, one-time-prekey path.**  As `pqxdh_keys_agree_no_opk`, but
both roles include the one-time prekey, adding the fourth X25519 leg (`hleg4`). -/
theorem pqxdh_keys_agree_with_opk
    (pI : pqxdh.InitiatorParameters) (pR : pqxdh.RecipientParameters)
    (coins : Array Std.U8 32#usize)
    (ss : Array Std.U8 32#usize) (ct : Array Std.U8 1569#usize)
    (opk : Array Std.U8 32#usize) (opk_pair : pqxdh.KeyPair)
    (hIopk : pI.their_one_time_pre_key = some opk)
    (hRopk : pR.our_one_time_pre_key_pair = some opk_pair)
    (hcanon : pqxdh.ec_is_canonical pR.their_ephemeral_key = ok true)
    (hleg1 : pqxdh.x25519_agree pI.our_identity_key_pair.private_key pI.their_signed_pre_key
           = pqxdh.x25519_agree pR.our_signed_pre_key_pair.private_key pR.their_identity_key)
    (hleg2 : pqxdh.x25519_agree pI.our_ephemeral_key_pair.private_key pI.their_identity_key
           = pqxdh.x25519_agree pR.our_identity_key_pair.private_key pR.their_ephemeral_key)
    (hleg3 : pqxdh.x25519_agree pI.our_ephemeral_key_pair.private_key pI.their_signed_pre_key
           = pqxdh.x25519_agree pR.our_signed_pre_key_pair.private_key pR.their_ephemeral_key)
    -- the OPK leg: init x25519(EK_A.priv, OPK_B) ↔ recip x25519(OPK_B.priv, EK_A):
    (hleg4 : pqxdh.x25519_agree pI.our_ephemeral_key_pair.private_key opk
           = pqxdh.x25519_agree opk_pair.private_key pR.their_ephemeral_key)
    (hencaps : pqxdh.mlkem_encapsulate pI.their_kyber_pre_key coins = ok (ss, ct))
    (hdecaps : pqxdh.mlkem_decapsulate pR.our_kyber_secret_key pR.their_kyber_ciphertext = ok ss) :
    initiatorKeys pI coins = recipientKeys pR := by
  rw [initiatorKeys_with_opk pI coins opk hIopk,
      recipientKeys_with_opk pR hcanon opk_pair hRopk,
      hleg1, hleg2, hleg3, hencaps, hleg4, hdecaps]
  simp

end

end Pqxdh
