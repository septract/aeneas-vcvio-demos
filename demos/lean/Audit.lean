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
import Demos.Ratchet.Chacha
import Demos.Ratchet.Cost
import Demos.Ratchet.ForwardSecrecy
import Demos.Ratchet.Generic
import Demos.Pqxdh.KeySchedule
import Demos.Pqxdh.Correctness
import Demos.Spqr.Gf
import Demos.Spqr.Authenticator
import Demos.Spqr.AuthMac
import Demos.AuthChannel.Mac
import Demos.AuthChannel.SufCma
import Demos.AuthChannel.MacCost
import Demos.KemDem.Composition
import Demos.Spqr.States
import Demos.Spqr.StatesGraph
import Demos.Crypto.Sha256
import Demos.Crypto.Hkdf
import Demos.Crypto.HmacPrf
import Demos.Crypto.PrfReduction
import Demos.Crypto.OracleHybrid
import Demos.Crypto.Sha256Wire
import Demos.Spqr.ChainSplit
import Demos.Ratchet.GenericIndexed
import Demos.Spqr.RatchetPrg
import Demos.Spqr.TripleRatchetComponent
import Demos.Spqr.Gf16Field
import Demos.Spqr.RsBridge
import Demos.Spqr.RsInterp
import Demos.Spqr.Gf16Mul
import Demos.Spqr.Gf16Reduce
import Demos.Spqr.Gf16FieldAssembly
import Demos.Spqr.Gf16ReduceTable
import Demos.Spqr.RsCapstone
import Demos.Spqr.Gf16FieldInstance
import Demos.Spqr.RsFieldBridge
import Demos.Spqr.RsEvalBridge
import Demos.Spqr.RsDivInverse
import Demos.Spqr.RsPrepareBridge
import Demos.Spqr.RsCompleteBridge
import Demos.Spqr.RsLagrangeBridge
import Demos.Spqr.Gf16IrreducibleMirror
import Demos.Spqr.Gf16IrreducibleBridge

-- Demo 1: one-time pad, perfect secrecy (unconditional).
#print axioms OtpSecurity.otpAeneas_perfectSecrecyAt

-- Demo 2a: PRG stream cipher (word) — tight reduction + asymptotic security.
#print axioms StreamSecurity.streamGen_advantage
#print axioms StreamSecurity.streamGen_secure_asymptotic
-- Class-relative security (audit M3): the PRG assumption made relative to the query-bounded
-- adversary class (the satisfiable form of "G is a secure PRG"), with the reduction proved to
-- stay in that class. Mirrors RatchetCost.ratchet_secure_against_polyQuery.
#print axioms StreamSecurity.streamGen_secure_against_queryBounded

-- Demo 2b: combiner loop correctness, and byte-array security (reduction + asymptotic).
#print axioms stream.combine_spec
#print axioms StreamByteSecurity.streamGen_advantage
#print axioms StreamByteSecurity.streamGen_secure_asymptotic
-- Class-relative security over the meaty extracted `combine` loop (audit M3).
#print axioms StreamByteSecurity.streamGen_secure_against_queryBounded

-- Demo 3: symmetric KDF ratchet — value adequacy, the telescoping hybrid bound (Σε over the
-- chain), and asymptotic security under the poly-many-hops side condition.
#print axioms ratchet.ratchet_split_spec
#print axioms RatchetSecurity.ratchet_advantage_le_sum
#print axioms RatchetSecurity.ratchet_secure_asymptotic

-- Demo 3 (meaty node): the ratchet's block generator is the real, extracted ChaCha20 block
-- function. Value adequacy = totality of the ARX code; security = the generic hybrid bound,
-- now over genuine arithmetic Rust.
#print axioms RatchetChacha.chacha20_block_total
#print axioms RatchetChacha.chacha_ratchet_advantage_le_sum
#print axioms RatchetChacha.chacha_ratchet_secure_asymptotic
-- Functional correctness of the ARX core (audit ChaCha gap): the extracted quarter-round computes
-- exactly the RFC 8439 §2.1 add/xor/rotate formula on BitVec 32 — strictly beyond totality, pinning
-- the named "ChaCha20 is a PRG" assumption to the genuine algorithm (security itself is necessarily
-- an assumption; the theorem is generic over G by correct reduction methodology).
#print axioms RatchetChacha.quarter_spec

-- Demo 3 (cost adequacy): the reduction is efficient relative to the adversary (query bound),
-- and the ratchet is secure against the poly-query adversary class (PRG assumption made
-- relative to that class; efficiency preservation proved, not assumed).
#print axioms RatchetCost.exists_totalQueryBound
#print axioms RatchetCost.reduction_queryBound
#print axioms RatchetCost.ratchet_secure_against_polyQuery

-- Demo 3 (forward secrecy): the joint (message-key prefix, surviving chain key) is
-- pseudorandom — compromising a later chain key leaves earlier message keys safe — by the
-- same n-step hybrid, instantiated at the extracted ChaCha20.
#print axioms RatchetFS.fs_advantage_le_sum
#print axioms RatchetFS.fs_secure_asymptotic
#print axioms RatchetFS.chacha_forward_secrecy_asymptotic
-- Forward secrecy is genuinely STRONGER than plain keystream pseudorandomness (audit M7): the
-- two were related only in prose. `ratchet_advantage_eq_fs` proves the keystream advantage equals
-- the fsGen advantage against the final-key-projecting distinguisher; `keystream_secure_of_fs_asymptotic`
-- is the resulting implication (fsGen-secure ⇒ keystream-secure), now machine-checked.
#print axioms RatchetFS.ratchet_advantage_eq_fs
#print axioms RatchetFS.keystream_secure_of_fs_asymptotic

-- Demo 3 (width scaling): the hybrid is width-agnostic — proven over an abstract length-doubling
-- split bijection, so security holds for a family whose key/block width grows with the security
-- parameter (Chain.lean is the fixed-width instance).
#print axioms RatchetGeneric.gen_advantage_le_sum
#print axioms RatchetGeneric.gen_secure_asymptotic_width

-- PQXDH node: functional correctness of the extracted key-schedule glue — the discontinuity
-- prefix is all-0xFF, the HKDF-output split is exactly the three 32-byte slices, and
-- DecodeEC ∘ EncodeEC = id (the spec §2.1 inverse the AD construction relies on).
#print axioms Pqxdh.secret_prefix_loop_spec
#print axioms Pqxdh.derive_split_spec
#print axioms Pqxdh.encode_ec_spec
#print axioms Pqxdh.decode_encode_roundtrip
-- Full HKDF secret-input byte layout (both paths): 0xFF^32 ‖ DH1 ‖ DH2 ‖ DH3 [‖ DH4] ‖ SS — the
-- KDF-input premise the AKE proof rests on. (NB: the BJKS re-encapsulation attack turned on binding
-- the KEM public key PQSPK into the transcript, not on the ordering of these DH/SS segments; SS is
-- the shared secret, no PQSPK is present — see KeySchedule.lean's scope caveat.)
#print axioms Pqxdh.pqxdh_secret_input_spec
#print axioms Pqxdh.pqxdh_secret_input_with_opk_spec
-- The associated data AD = EncodeEC(IK_A) ‖ EncodeEC(IK_B) (two 0x05-tagged 33-byte keys) — the
-- transcript-MACed identity binding. (NB: the BJKS attack turned on this AD *not* binding PQSPK;
-- the layout proved here is the identity-key binding only, i.e. the pre-fix shape.)
#print axioms Pqxdh.associated_data_spec
-- Initiator/recipient orchestration envelope: value adequacy (totality) of pqxdh_initiate /
-- pqxdh_accept — the one-time-prekey 3-leg/4-leg branch and the recipient base-key validation
-- guard (is_canonical → None), with DH/ML-KEM/HKDF as the typed boundary (outputs are inputs).
#print axioms Pqxdh.pqxdh_initiate_total
#print axioms Pqxdh.pqxdh_accept_total

-- PQXDH key-agreement CORRECTNESS (functional, no security game): for corresponding parameters,
-- pqxdh_initiate and pqxdh_accept derive IDENTICAL HandshakeKeys. The X25519 symmetry
-- (dh(a,pub b)=dh(b,pub a)) on the three/four matched legs and ML-KEM round-trip (decaps recovers
-- the encaps shared secret) are supplied as explicit HYPOTHESES on exactly the agreed legs — no new
-- axiom. Both roles assemble the same secret_input (building on pqxdh_secret_input_spec), feed the
-- same deterministic HKDF, derive_split the same okm; key-equality follows by congruence. These two
-- headlines also bottom out on the five gate-confined PQXDH floor axioms (the opaque primitives
-- appear in the leg/decaps hypotheses), so they join the FLOOR_OK confinement set in audit.sh.
#print axioms Pqxdh.pqxdh_keys_agree_no_opk
#print axioms Pqxdh.pqxdh_keys_agree_with_opk

-- SPQR node (GF(2^16) field arithmetic): value adequacy (totality) of the genuine carryless
-- multiply + table reduction Signal's own hax/F* build verifies — gf_add is XOR, gf_mul/
-- poly_reduce/gf_div are total pure functions on u16.
#print axioms Spqr.Gf.gf_add_total
#print axioms Spqr.Gf.poly_reduce_total
#print axioms Spqr.Gf.gf_mul_total
#print axioms Spqr.Gf.gf_div_total

-- SPQR node (authenticator glue): big-endian epoch encoding is total; the KDF-output split is
-- exactly the two 32-byte halves; the update IKM is root_key ‖ k (the documented salt/IKM swap);
-- and the constant-time comparator: it leaves its accumulator unchanged on equal inputs
-- (accept), inz evaluates the bit-twiddle (0↦0, ≠0↦1), and compare REJECTS (nonzero) any tag
-- that differs at some byte — the unforgeability direction the SCKA authentication argument needs.
#print axioms Spqr.Auth.epoch_to_be_bytes_total
#print axioms Spqr.Auth.update_split_spec
#print axioms Spqr.Auth.auth_update_ikm_spec
#print axioms Spqr.Auth.compare_loop_refl
#print axioms Spqr.Auth.inz_spec
#print axioms Spqr.Auth.compare_reject
-- The domain-separation string / MAC-input builders are total. mac_ct_data covers the full
-- 1088-byte ciphertext ct1‖ct2 the authenticator actually MACs (send_ct.rs extends ct1 by ct2).
#print axioms Spqr.Auth.auth_update_info_total
#print axioms Spqr.Auth.mac_hdr_data_total
#print axioms Spqr.Auth.mac_ct_data_total

-- SPQR Ratcheted-Authenticator MAC as a VCVio `MacAlg` (UF-CMA over the extracted constant-time
-- comparator). REUSES VCVio's TRUSTED `MacAlg`/`MacAlg.UF_CMA` game verbatim (no new game). The
-- canonical PRF-MAC `tag k m = F_k(m)`, `verify = (compare F_k(m) t == 0)`, packaged as a
-- `MacAlg ProbComp M K Tag` over SPQR's `authenticator::compare` (0 = accept, the inverse polarity
-- of Demo 4's Bool verify). `compare_accept`: equal tags accept (the accept counterpart of the
-- already-landed `compare_reject`). `compareB_eq_true_iff`: the comparator's Boolean view decides
-- tag equality (value adequacy — accept iff equal; forged/altered tags rejected via compare_reject).
-- `spqrMacAlg_perfectlyComplete`: honest tags always verify (perfect completeness, uniform-key PRF).
-- The full UF-CMA *bound* is Demo 4's chain over the same MacAlg shape; this banks the SPQR-side
-- instance + completeness/verify-adequacy glue.
#print axioms Spqr.AuthMac.compare_accept
#print axioms Spqr.AuthMac.compareB_eq_true_iff
#print axioms Spqr.AuthMac.spqrMacAlg_perfectlyComplete

-- Round 2 — crypto primitive nodes (the construction-tower extraction).
-- SHA-256: faithful FIPS 180-4 compression (genuine ARX, the hash floor).
#print axioms Sha256.sha256_compress_total
-- Variable-length (bounded) multi-block SHA-256: total for `len + 9 ≤ 2048`.
#print axioms Sha256.sha256_total
-- Variable-length HMAC / HKDF / AEAD over the multi-block hash — the functionally-identical
-- (modulo a capacity bound) versions; total for the bounded domain. HMAC is the two-pass
-- ipad/opad structure the HMAC-is-a-PRF reduction lifts; the AEAD is stream cipher +
-- encrypt-then-MAC (libsignal crypto.rs) with constant-time verify.
#print axioms Sha256.hmac_sha256_var_total
#print axioms Sha256.hkdf_extract_total
#print axioms Sha256.hkdf_expand_96_total
#print axioms Sha256.etm_encrypt_var_total
#print axioms Sha256.etm_decrypt_var_total
-- SPQR symmetric ratchet step (chain.rs next_key_internal): a 64-byte HKDF-Expand then split into
-- the next chain key and the emitted output key — the symmetric KDF producing the SCKA output_keys.
#print axioms Sha256.hkdf_expand_64_total
#print axioms Sha256.spqr_chain_next_total

-- HKDF RFC 5869 FUNCTIONAL specs (Demos/Crypto/Hkdf.lean — value layer over totality, NO security
-- game). `hkdf_extract_eq`: HKDF-Extract is definitionally `PRK = HMAC(salt, ikm)` (RFC 5869 §2.2).
-- `hkdf_t1_msg_spec` / `hkdf_tn_msg_spec`: the HKDF-Expand block-input buffers are exactly
-- `info ‖ ctr` resp. `prev ‖ info ‖ ctr` over their live prefix (the `T(i) = HMAC(prk, T(i-1)‖info‖i)`
-- inputs, T(0) empty). `hkdf_expand_64_spec` / `hkdf_expand_96_spec`: the extracted expand outputs
-- are `T(1)‖T(2)[‖T(3)]` with each block the HMAC of `prk` over the corresponding T-input buffer —
-- RFC 5869 §2.3 T-chaining truncated to 64/96 bytes (SPQR KDF_AUTH / PQXDH derive). SHA-256-as-PRF
-- remains the named floor; these are functional-correctness theorems (3 standard axioms only).
#print axioms Sha256.hkdf_extract_eq
#print axioms Sha256.hkdf_t1_msg_spec
#print axioms Sha256.hkdf_tn_msg_spec
#print axioms Sha256.hkdf_expand_64_spec
#print axioms Sha256.hkdf_expand_96_spec

-- Crypto functional specs the reductions lean on (byte layouts, NO security game):
-- the HMAC padded-key block K0⊕pad is `(key[i]⊕pad) ‖ pad^32` (key_pad_block_spec), and the full
-- HMAC two-pass byte equation hmac_sha256_var = H((K0⊕opad) ‖ H((K0⊕ipad) ‖ msg)) over the genuine
-- extracted two-pass code (hmac_sha256_var_byte_eq) — the byte shape HmacPrf's `hmacSpec` lifts,
-- with the two distinct pads 0x36=54 (ipad) / 0x5c=92 (opad). These feed the hmac-prf reduction.
#print axioms Sha256.key_pad_block_spec
#print axioms Sha256.hmac_sha256_var_byte_eq

-- HMAC-is-a-PRF (Bellare CRYPTO 2006), PARTIAL: the Merkle–Damgård cascade / NMAC infrastructure
-- and the closable reduction steps, all over VCVio's TRUSTED `PRFScheme`/`prfAdvantage` (reused
-- verbatim — NO new security game). `cascade_append`: the Merkle–Damgård splitting identity the
-- hybrid iterates over. `prfAdvantage_congr`: the principled bridge — equal keygen+eval ⇒ equal
-- distinguishing advantage against every adversary (the rewrite step every reduction rests on).
-- `cascade1_prfAdvantage_eq`: the base case — the single-block cascade PRF has EXACTLY the
-- compression PRF's advantage (ε = 0, the leaf the hybrid sum bottoms out on).
-- `cascadePRF_prfAdvantage_congr`: the multi-block analogue (variable-length domain).
-- `hmacSpec_eq`/`hmac_pads_distinct`: the functional spec `H((k⊕opad)‖H((k⊕ipad)‖m))` and its
-- two-distinct-pads pin. NOT closed: the multi-block hybrid sum bounding the full cascade advantage
-- by q·(compression advantage), and HMAC = NMAC∘key-derivation — paper-sized, left as future work.
#print axioms HmacPrf.cascade_append
#print axioms HmacPrf.prfAdvantage_congr
#print axioms HmacPrf.cascade1_prfAdvantage_eq
#print axioms HmacPrf.cascadePRF_prfAdvantage_congr
#print axioms HmacPrf.hmacSpec_eq
#print axioms HmacPrf.hmac_pads_distinct

-- HMAC-is-a-PRF, per-hop localization (the genuinely-deep middle of Bellare's cascade proof, stated
-- exactly — over VCVio's TRUSTED randomOracle, NO new game). The depth-`i` unified switching handler
-- on a function query is the lazy random oracle on the length-`i` prefix, its sampled chaining value
-- post-composed with the real suffix cascade. `prefixRandomSuffixRealImpl_inr` exposes that branch
-- definitionally (the structural unfold the per-hop reduction routes through);
-- `prefixRandomSuffixRealImpl_inr_succ` is the SUBSTANTIVE per-hop pin — it factors the depth-`i`
-- handler through the depth-`(i+1)` answer precomposed with EXACTLY ONE real compression call
-- `f c (bs.get i)`, pinning precisely the compression query the reduction swaps to its challenge
-- oracle. The remaining distributional gap (the extended-prefix lazy-RO interpolation) is the honest
-- open obligation localized to a single query — not discharged here, but stated exactly.
#print axioms HmacPrf.prefixRandomSuffixRealImpl_inr
#print axioms HmacPrf.prefixRandomSuffixRealImpl_inr_succ

-- Reusable PRF → random-function reduction (the FCF `PRF.v` `RndR_func`/PRF→RF analog), abstracted
-- from the MAC-specific reduction in SufCma.lean into a primitive-agnostic module over an arbitrary
-- `D →ₒ R` (NO new security game — reuses VCVio's TRUSTED `PRFScheme`/`prfRealQueryImpl`/
-- `prfIdealQueryImpl`/`prfAdvantage`/`randomOracle`). `simulateQ_prfReal_fwdLog`: the real-world
-- correspondence — running any client through the logging forward oracle then the real PRF equals
-- running it through the keyed-function logging handler (the inductive core, generic in the client).
-- `freshQuery_bound`: one fresh random-oracle query matches a fixed target with prob ≤ 1/|R|.
-- `fwdLog_cache_log_inv`: the cache⊆log invariant (unlogged ⟹ uncached) the freshness gate rests on.
-- `reduction_RF_le`: the ideal-world acceptance of the explicit reduction is ≤ 1/|R|.
-- `prfReal_le_prfAdvantage_add_RF`: the deliverable triangle — real-world acceptance of the
-- reduction ≤ `prfAdvantage(reduction) + 1/|R|` (the base case the cascade/MAC floors consume).
#print axioms Demos.Crypto.PrfReduction.simulateQ_prfReal_fwdLog
#print axioms Demos.Crypto.PrfReduction.freshQuery_bound
#print axioms Demos.Crypto.PrfReduction.fwdLog_cache_log_inv
#print axioms Demos.Crypto.PrfReduction.reduction_RF_le
#print axioms Demos.Crypto.PrfReduction.prfReal_le_prfAdvantage_add_RF

-- ── Generic q-query oracle hybrid (REUSABLE INFRASTRUCTURE — the missing VCVio middle) ──────────
-- The Lean analog of FCF's `OracleHybrid.v` (Adam Petcher's Coq framework, which VCVio is modelled
-- on), built ON TOP OF VCVio's shipped telescoping `QueryImpl.Stateful.advantage_hybrid` — NO new
-- security notion. VCVio ships the hybrid SUM and the IND-CPA-specific endpoints, but NOT the
-- primitive-agnostic middle: for arbitrary stateless handlers `O1 O2 : QueryImpl` and a
-- `q`-query-bounded client, `|adv(all-O1) − adv(all-O2)| ≤ Σ_{i<q}` single-query-hop terms. Every
-- floor discharge currently reinvents this by hand (e.g. SufCma.lean / PrfReduction.lean); this
-- ABSTRACTS it once. The endpoints are reconstructed from a counted switching handler `Oi` (FCF's
-- `Oi`, OracleHybrid.v:48): `run'_Oi_zero_eq_ofCounted_right` is FCF `G2_eq_Gi_0` (v:306 — `Oi 0` is
-- the all-`O2` handler); `evalDist_run'_Oi_q_eq_ofCounted_left` is FCF `G1_eq_Gi_q` (v:230, "the most
-- complicated part" — a `q`-bounded client never drives the counter to `q`, discharged via VCVio's
-- relational query-bound transport). `advantage_le_sum_hybridStep` is FCF `G1_G2_close` (v:334 — the
-- q-fold hybrid sum), feeding the two endpoints into `advantage_hybrid`; `advantage_le_nsmul_hybridStep`
-- is FCF `distance_le_prod_f` (the `q · k` uniform-per-hop form). All axiom-clean (the per-hop term is
-- the caller's atomic obligation, never an axiom). Written upstreamable; committed only to our tree.
#print axioms Demos.Crypto.OracleHybrid.run'_Oi_zero_eq_ofCounted_right
#print axioms Demos.Crypto.OracleHybrid.evalDist_run'_Oi_q_eq_ofCounted_left
#print axioms Demos.Crypto.OracleHybrid.advantage_le_sum_hybridStep
#print axioms Demos.Crypto.OracleHybrid.advantage_le_nsmul_hybridStep
-- Reuse glue (round 2): the generic per-hop term IS a `ProbComp.boolDistAdvantage` of the two
-- adjacent switching-handler runs (`hybridStep_eq_boolDistAdvantage`, by `rfl` since
-- `Stateful.advantage` is that `boolDistAdvantage`), so `advantage_le_sum_boolDistAdvantage_hybridStep`
-- re-states the q-fold sum with each summand in the exact `boolDistAdvantage` shape the cascade-PRF
-- floor (`HmacPrf.boolDistAdvantage_le_sum_chain`) consumes — closing the round-1 reuse gap (the floor
-- instantiates this rather than reconstructing the telescoping sum). `advantage_le_single_hop_of_oneQuery`
-- is the non-vacuous end-to-end instance at q=1: the bound collapses to the lone hop, a stated theorem
-- (not just the load-bearing `example`) witnessing the infrastructure discharges to a real conclusion.
-- All axiom-clean (the per-hop term stays the caller's atomic obligation).
#print axioms Demos.Crypto.OracleHybrid.hybridStep_eq_boolDistAdvantage
#print axioms Demos.Crypto.OracleHybrid.advantage_le_sum_boolDistAdvantage_hybridStep
#print axioms Demos.Crypto.OracleHybrid.advantage_le_single_hop_of_oneQuery

-- SPQR chain-step output split (structural / value adequacy — NO security game). The extracted
-- output-split loop carves the 64-byte HKDF block into new_next = genr8r[0..32] and out_key =
-- genr8r[32..64] (value spec, stronger than the audited totality); the resulting pure split is
-- definitionally the SAME byte-split as Demo 3's RatchetSecurity.splitPure, hence the length-
-- doubling bijection Blk64 ≃ Key × Key that the width-generic ratchet hybrid consumes (reusing
-- splitPure_bijective verbatim). Banks the split-shape fit; the full advantage bound is NOT reached
-- (SPQR's per-step generator is counter-indexed, so it does not instantiate the step-invariant
-- RatchetGeneric hybrid — see ChainSplit.lean scope note).
#print axioms Spqr.ChainSplit.spqr_chain_next_loop2_split_spec
#print axioms Spqr.ChainSplit.spqrSplit_eq_splitPure
#print axioms Spqr.ChainSplit.spqrSplit_bijective
-- The chain-step split FORMULA on the whole `spqr_chain_next` (functional, NO security): the call
-- advances the counter to ctr+1 and emits (new_next, out_key) = (genr8r[0..32], genr8r[32..64]),
-- where genr8r is PINNED to the actual HKDF-Expand block (the statement exhibits the computed
-- prk/info4 and asserts hkdf_expand_64 prk info4 35 = ok genr8r — so the split is of the real
-- cryptographic block, not an arbitrary array) — the layout the SCKA output_key production rests on.
#print axioms Spqr.ChainSplit.spqr_chain_next_split_spec

-- STEP-INDEXED generic ratchet hybrid (RatchetGenericIndexed): generalizes the RatchetGeneric
-- hybrid from a single step-invariant generator G : K → B to a step-indexed FAMILY G : ℕ → K → B,
-- threading an absolute base index t so the length-n keystream from base t uses G t, G (t+1), …,
-- G (t+n-1) and hop i reduces to the DISTINCT PRGScheme genBlockPRGI G (t+i). NO new game: every
-- advantage term is VCVio's existing PRGScheme.prgAdvantage; the per-step PRG-security assumption is
-- a hypothesis (a prgAdvantage bound premise), exactly as RatchetGeneric carries its single-G bound.
-- gen_advantage_le_sum: telescoping Σε advantage bound; gen_secure_asymptotic_idx: poly-length ⇒
-- pseudorandom keystream family (the single negligible ε uniformly bounds the per-hop advantage).
#print axioms RatchetGenericIndexed.gen_advantage_le_sum
#print axioms RatchetGenericIndexed.gen_secure_asymptotic_idx

-- SPQR symmetric-ratchet keystream pseudorandomness (Spqr.RatchetPrg): instantiates the step-indexed
-- hybrid above at the COUNTER-INDEXED SPQR block generator spqrGen ctr0 : ℕ → Key → Blk64 (hop i
-- evaluates SPQR's chain core at counter ctr0+i, the genuine 64-byte HKDF-Expand block driven by the
-- extracted spqr_chain_next), reusing Spqr.ChainSplit.spqrSplit / spqrSplit_bijective VERBATIM for the
-- length-doubling split. spqrGen_step_eq is the value-adequacy BRIDGE: the split of spqrGen's i-th
-- block is EXACTLY the (new_next, out_key) pair the extracted spqr_chain_next next (ctr0+i) returns,
-- so the hybrid is over the real chain step. spqr_ratchet_advantage_le_sum: the SPQR keystream Σε
-- bound; spqr_ratchet_secure_asymptotic: poly-length + per-hop PRG hypothesis ⇒ pseudorandom. The
-- per-step PRG security is an explicit HYPOTHESIS (a PRGScheme.prgAdvantage bound premise), NOT an
-- axiom and NO new game — same shape as RatchetSecurity.ratchet_secure_asymptotic. Scope (inherited
-- from Chain.lean): the hybrid treats each hop's chain key as uniform, whereas it is HKDF-Extracted
-- from the previous block; reducing the Extract step (PRK pseudorandomness) is out of scope.
#print axioms Spqr.RatchetPrg.spqrGen_step_eq
#print axioms Spqr.RatchetPrg.spqr_ratchet_advantage_le_sum
#print axioms Spqr.RatchetPrg.spqr_ratchet_secure_asymptotic

-- Triple Ratchet COMPONENT BRIDGE: the SPQR keystream as the antecedent of TR Thm 4.2's "KDF2 is a
-- secure PRG" hypothesis (Dodis, Jost, Katsumata, Prest, Schmidt; EUROCRYPT 2025 / ePrint 2025/078).
-- TR Thm 4.2 p.21 (assumption "KDF2 is a secure PRG"); KDF2 = Fig 9 p.20 lines 15/50 (KR ↦ (KR',K_aead));
-- "secure PRG" = Def 2.6 p.10 (matches VCVio's prgAdvantage shape exactly); consumed as the q·Adv^PRG
-- term of Lemma 4.7 p.23. spqr_chain_step_discharges_TR_KDF2_PRG WIRES our already-proven
-- spqr_ratchet_secure_asymptotic to that named hypothesis: under the per-hop PRG floor (an explicit
-- premise — exactly as TR ASSUMES KDF2-PRG rather than proving it; NOT an axiom, NO new game) the
-- extracted SPQR keystream is pseudorandom. spqr_keystream_advantage_le_kdf2_sum re-exports the
-- unconditional Σε bound. NOT claimed: the HKDF/SHA-256 PRG floor itself, TR's CKA/SM game, TR's
-- FS/PCS windows. The per-hop PRG-ness is a HYPOTHESIS, so the axiom set stays the standard three.
#print axioms Spqr.TripleRatchetComponent.spqr_chain_step_discharges_TR_KDF2_PRG
#print axioms Spqr.TripleRatchetComponent.spqr_keystream_advantage_le_kdf2_sum

-- SPQR Reed-Solomon codec field core: polynomial evaluation (encoder chunk generation),
-- pointwise add, and scalar multiply over GF(2^16) — all total.
#print axioms Spqr.Gf.poly_eval_total
#print axioms Spqr.Gf.poly_add_total
#print axioms Spqr.Gf.poly_scale_total

-- SPQR Reed-Solomon DECODER kernel: Lagrange interpolation (prepare ∘ mult_xdiff ∘ complete ∘
-- accumulate) + polynomial evaluation, over fixed [u16;37] coefficient arrays (the V1 bound
-- MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1 + 1). decode_value_at = the reconstruction kernel
-- (interpolate-then-evaluate); all proved TOTAL for n ≤ 36. NB: the algebraic decode∘encode=id
-- round-trip the SCKA correctness argument needs is separate future work, not proved here.
#print axioms Spqr.Gf.mult_xdiff_trailing_total
#print axioms Spqr.Gf.prepare_total
#print axioms Spqr.Gf.complete_total
#print axioms Spqr.Gf.lagrange_interpolate_total
#print axioms Spqr.Gf.compute_at_total
#print axioms Spqr.Gf.decode_value_at_total

-- SPQR Reed-Solomon codec — ALGEBRAIC value specs (the layer above totality: WHAT the loops
-- compute, as closed-form recurrences over the field ops, NO security game). The field multiply is
-- a deterministic pure function `gfMulV`; on top of it: `poly_eval_eq` — the encoder's evaluation
-- loop computes EXACTLY the Horner fold `hornerV coeffs x 0 deg` (= the polynomial value at x);
-- `poly_add_eq` — pointwise characteristic-2 sum `a[k] ⊕ b[k]`; `poly_scale_eq` — pointwise field
-- product `gfMulV a[k] m`; `mult_xdiff_trailing_eq` — one step of multiply-by-(x-c): over the window
-- `start-1 ≤ j < len-1`, coefficient j becomes `coeffs[j] ⊕ gfMulV coeffs[j+1] difference`, else
-- unchanged. NB: the full `decode∘encode=id` round-trip additionally needs the GF(2^16) FIELD LAWS
-- (assoc/distrib/inverse — what Signal proves against Spec.GF16 in F*); these value specs are the
-- field-law-free algebraic backbone it builds on, banked here. (Reduces decode∘encode=id to:
-- gfMulV/⊕ form a field + Lagrange-interpolation correctness over Mathlib's `Lagrange`.)
#print axioms Spqr.Gf.poly_eval_eq
#print axioms Spqr.Gf.poly_add_eq
#print axioms Spqr.Gf.poly_scale_eq
#print axioms Spqr.Gf.mult_xdiff_trailing_eq

-- SPQR Reed-Solomon codec — Layer B (PARTIAL): the ADDITIVE GROUP of the extracted GF(2^16) field.
-- These are about `gfAddV`, the value spec of the extracted `gf.gf_add` (banked as `gf_add_eq`):
-- the field add is commutative (gfAddV_comm), associative (gfAddV_assoc), has identity 0
-- (gfAddV_zero / gfAddV_zero_left) and is its own inverse (gfAddV_self) — the characteristic-2
-- abelian group, proved STRUCTURALLY from BitVec/Nat XOR (no field-law decide, no axiom). And the
-- XOR-as-polynomial-addition bridge `toPoly_gfAddV`: under the bit↔coefficient embedding
-- `toPoly : U16 → (ZMod 2)[X]`, `gfAddV` is EXACTLY polynomial addition — the additive half of the
-- ring-iso `U16 ≅ (ZMod 2)[X]/(POLY)`. NB: the MULTIPLICATIVE field instance (gfMulV = mult mod POLY,
-- and Irreducible POLY over ZMod 2) is the documented OPEN obligation — NOT closed here, NOT faked.
#print axioms Spqr.Gf16Field.gfAddV_comm
#print axioms Spqr.Gf16Field.gfAddV_assoc
#print axioms Spqr.Gf16Field.gfAddV_zero
#print axioms Spqr.Gf16Field.gfAddV_zero_left
#print axioms Spqr.Gf16Field.gfAddV_self
#print axioms Spqr.Gf16Field.toPoly_gfAddV

-- SPQR Reed-Solomon codec — Layer B-mul (PARTIAL), STAGE 1: the MULTIPLICATIVE side's first stage,
-- the carryless-multiply = polynomial-product half of the GF(2^16) ring bridge. About the extracted
-- carryless multiply `gf.poly_mul` (the `u32` half of `gf_mul = poly_reduce ∘ poly_mul`):
--   poly_mul_spec — VALUE SPEC of the extracted `gf.poly_mul`: it succeeds with the explicit
--     carryless XOR-fold `clmulPartial a.val b.val 16` = ⊕_{shift<16, b.testBit shift} (a << shift),
--     the same field-law-free "what value the loop computes" style as the banked value specs — a
--     result directly about `gf.poly_mul`;
--   toPoly32_polyMulV — STAGE 1 of B-mul: under the bit↔coefficient embeddings (toPoly : U16 → (ZMod 2)[X],
--     toPoly32 : U32 → (ZMod 2)[X]), the extracted carryless multiply (read as the value `polyMulV a b`
--     of `gf.poly_mul`) denotes EXACTLY the polynomial product: toPoly32 (polyMulV a b) = toPoly a * toPoly b.
--     Proved STRUCTURALLY from the carryless XOR-fold matched against Polynomial.coeff_mul (char-2
--     convolution) — no field laws, no value-space decide, no axiom. This is the multiplicative half's
--     first stage of the ring-iso U16 ≅ (ZMod 2)[X]/(POLY). NB: STAGE 2 (poly_reduce = remainder mod
--     POLY_poly, the table-fold residue-correctness) and Irreducible POLY_poly remain the documented
--     OPEN obligations — NOT closed here, NOT faked.
#print axioms Spqr.Gf16Mul.poly_mul_spec
#print axioms Spqr.Gf16Mul.toPoly32_polyMulV

-- SPQR Reed-Solomon codec — Layer B-mul, the CODE DECOMPOSITION of the extracted field multiply,
-- plus the PRECISE localization of the remaining multiplicative gap (Spqr.Gf16Reduce). All
-- field-law-FREE, about the extracted gf.gf_mul / gf.poly_reduce / gf.poly_mul:
--   poly_reduce_ok — VALUE SPEC of the extracted table reduction gf.poly_reduce: it succeeds with
--     the pure value poly_reduceV (from the banked totality poly_reduce_total) — the reduction-side
--     analog of the banked poly_mul value spec;
--   gfMulV_decomp — the extracted field multiply, read as the value gfMulV a b (the gf_mul_eq value
--     spec), is EXACTLY the table reduction of the carryless product: gfMulV a b =
--     poly_reduceV (polyMulV a b). This pins the gf_mul = poly_reduce ∘ poly_mul decomposition
--     (Extracted/Gf.lean) at the VALUE level — a result directly about gf.gf_mul/gf.poly_reduce/
--     gf.poly_mul, NO field laws, NO axiom.
-- NB: combined with the banked Stage 1 (toPoly32_polyMulV: clmul = poly product), gfMulV_decomp
-- localizes the field-assembly bridge `hmul` to the SINGLE polynomial statement Stage2
-- (poly_reduce realizes reduction mod POLY_poly on the embedding) — see Gf16Reduce.stage2_imp_hmul /
-- hmul_imp_stage2_on_products (building blocks). Stage 2 stays the documented OPEN gap (the 256-entry
-- table-double-fold = polynomial remainder is the heavier obligation) — NOT closed, NOT faked.
#print axioms Spqr.Gf16Reduce.poly_reduce_ok
#print axioms Spqr.Gf16Reduce.gfMulV_decomp

-- SPQR Reed-Solomon codec — Layer B, FIELD ASSEMBLY (CONDITIONAL): the GF(2^16) ring/field laws on
-- the extracted field arithmetic (gfAddV = gf_add value spec, gfMulV = gf_mul value spec), assembled
-- along the NON-CIRCULAR route — the field-ness comes from Mathlib's quotient `AdjoinRoot POLY_poly`,
-- reflected back through the embedding φ = AdjoinRoot.mk POLY_poly ∘ toPoly : U16 → AdjoinRoot POLY_poly.
-- φ is proved (UNCONDITIONALLY) ADDITIVE (phi_gfAddV, from the banked XOR=poly-add bridge), INJECTIVE
-- (φ a = φ b forces toPoly a − toPoly b, of degree <16 = natDegree POLY, to be a POLY-multiple hence 0),
-- and SURJECTIVE (every residue has a degree-<16 representative = toPoly of some U16). The MULTIPLICATIVE
-- compatibility of φ is exactly the full B-mul bridge (Stage 1 banked + Stage 2 open), carried as the
-- EXPLICIT, SATISFIABLE hypothesis `hmul : ∀ a b, phi (gfMulV a b) = phi a * phi b` — NEVER an axiom.
--   phi_gfAddV — UNCONDITIONAL: φ (gfAddV a b) = φ a + φ b (gfAddV = field add is the quotient add);
--   gfMulV_comm / gfMulV_assoc — CONDITIONAL on hmul: the extracted field-multiply is commutative /
--     associative, reflected through the injective φ from AdjoinRoot's ring laws (NO irreducibility);
--   gfMulV_one / gfMulV_one_left — CONDITIONAL on hmul: 1#u16 is a two-sided gfMulV identity;
--   gfMulV_gfAddV_distrib / _distrib_right — CONDITIONAL on hmul: gfMulV distributes over gfAddV;
--   gfMulV_exists_inv — CONDITIONAL on hmul AND [Fact (Irreducible POLY_poly)] (B-irr, OPEN): every
--     nonzero gfMulV-element has a gfMulV-inverse (the FIELD law), via inverting in the field
--     AdjoinRoot POLY_poly and pulling back through the (unconditional) surjective φ.
-- NB: both premises are SATISFIABLE (the field really IS GF(2^16) and POLY_poly really is irreducible),
-- so the conditional theorems are GENUINE and NON-VACUOUS. STAGE 2 of B-mul (poly_reduce = remainder mod
-- POLY) and Irreducible POLY_poly remain the documented OPEN obligations — NOT closed, NOT faked, NOT
-- axiomatized. Each headline mentions the extracted gfMulV/gfAddV (the gf_mul/gf_add value specs).
#print axioms Spqr.Gf16FieldAssembly.phi_gfAddV
#print axioms Spqr.Gf16FieldAssembly.gfMulV_comm
#print axioms Spqr.Gf16FieldAssembly.gfMulV_assoc
#print axioms Spqr.Gf16FieldAssembly.gfMulV_one
#print axioms Spqr.Gf16FieldAssembly.gfMulV_one_left
#print axioms Spqr.Gf16FieldAssembly.gfMulV_gfAddV_distrib
#print axioms Spqr.Gf16FieldAssembly.gfMulV_gfAddV_distrib_right
#print axioms Spqr.Gf16FieldAssembly.gfMulV_exists_inv

-- SPQR Reed-Solomon codec — Layer B-mul, STAGE 2 CLOSED (Spqr.Gf16ReduceTable): the extracted
-- table reduction gf.poly_reduce realizes reduction mod POLY_poly = x¹⁶+x¹²+x³+x+1, proved
-- STRUCTURALLY (loop value specs + AdjoinRoot.mk reasoning) with NO axiom / sorry / native_decide.
-- This DISCHARGES the hmul hypothesis and upgrades the six Gf16FieldAssembly ring laws from
-- CONDITIONAL to UNCONDITIONAL. All headlines below mention the extracted gf.reduce_from_byte /
-- gf.reduce_bytes / gf.poly_reduce / gf.gf_mul / gf.gf_add:
--   reduceFromByteV_spec — VALUE SPEC of gf.reduce_from_byte: the 8-step bit-fold result satisfies
--     mk(toPoly32 ·) = 0 (it is a POLY_poly-multiple), its high half >>16 recovers the input byte,
--     and it is < 2^24 — a result directly about the extracted gf.reduce_from_byte;
--   reduce_bytes_eq — VALUE SPEC of the 256-entry table gf.reduce_bytes: each entry table[k] =
--     reduce_from_byte(k) as u16 (the upstream hax loop_invariant), proved parametrically;
--   poly_reduce_form — closed-form VALUE SPEC of gf.poly_reduce: the two table-byte folds give
--     ((v ^^^ table[v>>24]<<8) ^^^ table[(v1>>16)&0xFF]) as u16;
--   stage2_proved — Spqr.Gf16Reduce.Stage2 PROVED: mk(toPoly(poly_reduceV v)) = mk(toPoly32 v),
--     i.e. gf.poly_reduce is reduction mod POLY_poly on the bit↔coefficient embedding;
--   hmul_proved — the multiplicative bridge phi(gfMulV a b) = phi a * phi b, UNCONDITIONAL, the
--     residue correctness of gf.gf_mul = poly_reduce ∘ poly_mul;
--   gfMulV_comm / _assoc / _one / _one_left / _gfAddV_distrib / _distrib_right — the extracted field
--     multiply gf.gf_mul (value gfMulV) is now a COMMUTATIVE-RING multiply over gfAddV, UNCONDITIONALLY
--     (the hmul premise is discharged by Stage 2 — NOT a hypothesis). NB: the FIELD inverse law
--     (gfMulV_exists_inv) still needs Irreducible POLY_poly (B-irr, the documented WALL).
#print axioms Spqr.Gf16ReduceTable.reduceFromByteV_spec
#print axioms Spqr.Gf16ReduceTable.reduce_bytes_eq
#print axioms Spqr.Gf16ReduceTable.poly_reduce_form
#print axioms Spqr.Gf16ReduceTable.stage2_proved
#print axioms Spqr.Gf16ReduceTable.hmul_proved
#print axioms Spqr.Gf16ReduceTable.gfMulV_comm
#print axioms Spqr.Gf16ReduceTable.gfMulV_assoc
#print axioms Spqr.Gf16ReduceTable.gfMulV_one
#print axioms Spqr.Gf16ReduceTable.gfMulV_one_left
#print axioms Spqr.Gf16ReduceTable.gfMulV_gfAddV_distrib
#print axioms Spqr.Gf16ReduceTable.gfMulV_gfAddV_distrib_right

-- SPQR Reed-Solomon codec — Layer C (PARTIAL): value specs of the DECODER's evaluation kernel
-- `gf.compute_at` (the `decode_value_at` re-evaluation step), extending the banked value-spec style
-- (poly_eval_eq / mult_xdiff_trailing_eq) to the remaining decoder loops. All field-law-FREE — they
-- pin EXACTLY which gfMulV/gfAddV combination the extracted loops form, in terms of the value specs
-- of gf_mul (gfMulV) / gf_add (gfAddV):
--   compute_at_loop1_eq / _eq0 — the coefficient dot product: started at (out,k), the loop folds
--     `out ↦ gfAddV out (gfMulV coeffs[k] powers[k])`, i.e. it computes `dotV coeffs powers len out k`
--     (= Σ_{k<len} coeffs[k] ⊗ powers[k]) — a recurrence about `gf.compute_at_loop1`;
--   compute_at_loop0_recurrence — the x-power table: from write index i≥2 to len≤37 the loop builds
--     `powers[j] = gfMulV powers[j/2] powers[j/2+j%2]` for 2≤j<len (and preserves slots <i), the
--     squaring recurrence — a value spec about `gf.compute_at_loop0`;
--   compute_at_eq — the assembled spec of `gf.compute_at`: it succeeds with the field dot product
--     `dotV coeffs powers len 0 0` of the coefficients against the x-power table (powers[0]=1,
--     powers[1]=x, squaring recurrence). The full in-boundary value characterization of the
--     extracted `gf.compute_at`. NB: connecting `dotV`/the power recurrence to `Polynomial.eval`
--     (hence the unconditional decode∘encode=id about gf.decode_value_at) additionally needs the
--     GF(2^16) FIELD instance — the documented Gf16Field gap (Irreducible POLY + clmul/reduce).
#print axioms Spqr.RsBridge.compute_at_loop1_eq
#print axioms Spqr.RsBridge.compute_at_loop1_eq0
#print axioms Spqr.RsBridge.compute_at_loop0_recurrence
#print axioms Spqr.RsBridge.compute_at_eq

-- SPQR Reed-Solomon codec — Layer C (PARTIAL), INTERPOLATION side: value specs of the extracted
-- Lagrange-reconstruction loops (gf.prepare / gf.complete / gf.lagrange_interpolate), the same
-- field-law-FREE "what value the loop computes" style as the banked poly_eval_eq /
-- mult_xdiff_trailing_eq / the compute_at specs, in terms of the value specs of the extracted field
-- ops (gfMulV = gf_mul, gfAddV = gf_add, gfDivV = gf_div):
--   gf_div_eq — the extracted Fermat-inverse division `gf.gf_div` is the deterministic pure
--     function `gfDivV` (the multiplicative-side analog of the banked gf_mul_eq, kept OPAQUE);
--   prepare_loop_eq / prepare_eq — gf.prepare builds PRODUCT_{i<n}(x − xs[i]) by iterating the banked
--     mult_xdiff_trailing_eq (xdiffStepFn): from the delta array [0,…,0,1,0,…] (1 at index n) it folds
--     n successive (x − xs[i]) multiplies (prepareFoldFn) — a value spec about gf.prepare / gf.prepare_loop;
--   complete_loop0_eq / _eq0 — gf.complete's denominator loop computes the running field product
--     ∏_{j<n, pix≠xs[j]} (pix ⊕ xs[j]) (denomV, a gfMulV-fold of gfAddV factors) — about gf.complete_loop0;
--   complete_loop1_eq — gf.complete's long-division sweep is the scale-and-carry recurrence divFold:
--     each step idx = len−j2 sets out[idx] = gfMulV out[idx] scale and out[idx−1] ⊕= gfMulV out[idx] pix
--     — a value spec about gf.complete_loop1;
--   complete_eq — assembles gf.complete: it runs divFold on the coefficients with the exact extracted
--     parameters pix = xs[i], scale = gfDivV ys[i] (denomV …) (the Lagrange coefficient
--     ys[i] / ∏(xs[i] ⊕ xs[j])), the division kept as the opaque gfDivV value — about gf.complete;
--   lagrange_interpolate_loop0_eq — the copy/divide-by-x loop shifts working down by one coefficient
--     (out[k] = working[k+1]) — about gf.lagrange_interpolate_loop0;
--   lagrange_interpolate_loop1_loop0_eq — the accumulate loop folds one basis term into the running sum
--     (out[j] ⊕= working[j+1], a gfAddV accumulation) — about gf.lagrange_interpolate_loop1_loop0.
-- NB: connecting these recurrences to Mathlib's `Lagrange.interpolate` (hence the unconditional
-- decode∘encode=id about gf.decode_value_at) additionally needs the GF(2^16) FIELD instance — the
-- documented Gf16Field gap (Irreducible POLY + clmul/reduce). These are the field-law-free backbone.
#print axioms Spqr.RsInterp.gf_div_eq
#print axioms Spqr.RsInterp.prepare_loop_eq
#print axioms Spqr.RsInterp.prepare_eq
#print axioms Spqr.RsInterp.complete_loop0_eq
#print axioms Spqr.RsInterp.complete_loop0_eq0
#print axioms Spqr.RsInterp.complete_loop1_eq
#print axioms Spqr.RsInterp.complete_eq
#print axioms Spqr.RsInterp.lagrange_interpolate_loop0_eq
#print axioms Spqr.RsInterp.lagrange_interpolate_loop1_loop0_eq

-- SPQR Reed-Solomon codec — Layer C, the CAPSTONE about the extracted `gf.decode_value_at`
-- (Spqr.RsCapstone): the `decode ∘ encode` identity over the genuine reconstruction kernel.
--   decode_value_at_eq — UNCONDITIONAL, field-law-FREE: `gf.decode_value_at xs ys n x` succeeds
--     and its value is EXACTLY the field dot product `dotV poly powers n 0 0 = Σ_{k<n} poly[k] ⊗
--     powers[k]` of the reconstructed coefficient array `poly` (= the value of the extracted
--     `gf.lagrange_interpolate xs ys n`) against the powers-of-x table (powers[0]=1, powers[1]=x,
--     squaring recurrence powers[j] = gfMulV powers[j/2] powers[j/2+j%2]). The structural
--     `decode = evaluate(interpolate)` identity, assembled from the banked RsBridge.compute_at_eq;
--     it mentions gf.decode_value_at, gf.lagrange_interpolate and (via dotV / the power recurrence)
--     gf.compute_at's gfMulV/gfAddV value specs. NO field laws, NO axiom, NO value-space decide.
--   decode_value_at_roundtrip — CONDITIONAL (explicit, satisfiable premises, NOT axioms): the
--     Reed–Solomon `decode ∘ encode = id` — for DISTINCT nodes (hvs : Set.InjOn node s) and a
--     codeword `ys` that is the encoder's evaluation of a degree-<n message polynomial f at those
--     nodes (henc), the extracted gf.decode_value_at xs ys n x — decoded into the field F via the
--     map `dec` — recovers `eval (dec x) f`. The honest open interpolation-correctness bridge
--     (`hbridge`: the decoder evaluates Mathlib's Lagrange.interpolate of the decoded samples; it
--     needs the field laws to identify the prepare/complete/divFold recurrences with the basis
--     polynomials) is carried as an EXPLICIT, SATISFIABLE hypothesis, never an axiom. The REAL
--     non-degeneracy hyps hvs (distinct nodes) and hdeg (f.degree < s.card) are kept and USED via
--     the banked field-generic RsAbstract.decode_eq_eval — dropping either makes recovery FALSE.
--     hbridge is NOT the conclusion (conclusion = recovers `eval (dec x) f` for the message f), so
--     the theorem does not secretly assume its own conclusion; all premises are jointly satisfiable
--     (so non-vacuous). NB: the UNCONDITIONAL round-trip stays open — it needs the field instance
--     (B-mul Stage 2 + Irreducible POLY_poly, the documented Gf16Field gaps) AND that the extracted
--     lagrange_interpolate loops compute Lagrange.interpolate; decode_value_at_eq is the
--     unconditional in-boundary fact this round banks.
#print axioms Spqr.RsCapstone.decode_value_at_eq
#print axioms Spqr.RsCapstone.decode_value_at_roundtrip

-- SPQR Reed-Solomon codec — Layer B, FIELD INSTANCE (Spqr.Gf16FieldInstance): with Stage 2 closed
-- (Gf16ReduceTable.hmul_proved), the embedding φ = mk ∘ toPoly : U16 → AdjoinRoot POLY_poly is now
-- an UNCONDITIONAL bijective ring hom. This packages the extracted field arithmetic as the genuine
-- GF(2¹⁶) quotient ring, the prerequisite for any Lagrange.interpolate statement over the carrier.
--   gfRingEquiv — the bundled ring ISOMORPHISM GF16 ≃+* AdjoinRoot POLY_poly (UNCONDITIONAL): the
--     extracted field arithmetic IS the quotient ring (ZMod 2)[X]/(POLY). (GF16 is a U16 synonym
--     carrying the CommRing transported through the bijection φ — the NON-CIRCULAR route.)
--   add_eq_gfAddV / mul_eq_gfMulV — the in-boundary identifications: GF16's + / * ARE the extracted
--     gfAddV / gfMulV (the value specs of gf.gf_add / gf.gf_mul). mul_eq_gfMulV is UNCONDITIONAL
--     because Stage 2 discharged hmul. zero_eq / one_eq — GF16's 0 / 1 are 0#u16 / 1#u16.
--   (also def fieldOfIrreducible : Field GF16 under [Fact (Irreducible POLY_poly)] — the genuine
--    GF(2¹⁶) field on the extracted arithmetic, conditional only on irreducibility, the WALL;
--    fieldOfIrreducible_toCommRing records it extends the same unconditional CommRing.)
#print axioms Spqr.Gf16FieldInstance.gfRingEquiv
#print axioms Spqr.Gf16FieldInstance.add_eq_gfAddV
#print axioms Spqr.Gf16FieldInstance.mul_eq_gfMulV
#print axioms Spqr.Gf16FieldInstance.zero_eq
#print axioms Spqr.Gf16FieldInstance.one_eq

-- SPQR Reed-Solomon codec — Layer C, the BRIDGE over the GENUINE GF(2¹⁶) carrier
-- (Spqr.RsFieldBridge): decode_value_at_roundtrip_gf16 instantiates the abstract round-trip at the
-- REAL field F = AdjoinRoot POLY_poly with dec = φ. The prior theorem's abstract [Field F] is
-- DISCHARGED to the genuine field (AdjoinRoot.instField under Fact (Irreducible POLY_poly)); the
-- only carried algebraic premise is now Irreducible POLY_poly (the WALL) — hmul/the field laws are
-- no longer assumed (Stage 2 discharged them). The interpolation-correctness bridge hbridge — now
-- phrased over the concrete genuine ring hom φ — remains an explicit, satisfiable premise (NOT an
-- axiom, NOT the conclusion); proving it (prepare/complete/divFold = Lagrange.interpolate, gfDivV =
-- field inverse) is the next refinement now that the field instance exists. About gf.decode_value_at.
#print axioms Spqr.RsFieldBridge.decode_value_at_roundtrip_gf16

-- decode_value_at_roundtrip_gf16_derived — CONDITIONAL on Irreducible POLY_poly + distinct nodes
-- (hdist) + nonzero Lagrange denominators (hdenom) + low message degree (hdeg) + the decode∘ENCODE
-- premise (henc: ys is a codeword of f) — the formerly-assumed hbridge premise is now DISCHARGED by
-- the proved RsLagrangeBridge.decode_value_at_eval_eq_interpolate (composition of the unconditional
-- evaluation half with the irreducibility-conditional interpolation half). So under irreducibility +
-- non-degeneracy, gf.decode_value_at xs ys n x, decoded through phi, recovers eval (phi x) f — the
-- Reed-Solomon decode∘encode=id over the genuine GF(2¹⁶) field, with the interpolation-correctness
-- bridge DERIVED rather than assumed (the only carried algebraic premise is Irreducible POLY_poly).
-- About gf.decode_value_at.
#print axioms Spqr.RsFieldBridge.decode_value_at_roundtrip_gf16_derived

-- decode_value_at_roundtrip_gf16_of_dist — REFINEMENT: the SAME decode∘encode=id over GF(2¹⁶) but
-- with the nonzero-Lagrange-denominator premise (hdenom) ALSO DROPPED. In the genuine GF(2¹⁶) field
-- the Lagrange denominators are products of differences of distinct nodes, hence nonzero in the
-- integral domain (RsLagrangeBridge.denomV_ne_zero) — so hdenom is DERIVED from hdist, not assumed.
-- CONDITIONAL on Irreducible POLY_poly + distinct nodes (hdist) + low message degree (hdeg) + the
-- decode∘ENCODE premise (henc) ONLY. Both the interpolation-correctness bridge and the
-- nonzero-denominator condition are now derived; the only carried algebraic premise is irreducibility.
-- About gf.decode_value_at.
#print axioms Spqr.RsFieldBridge.decode_value_at_roundtrip_gf16_of_dist

-- (Spqr.RsEvalBridge): the EVALUATION half of the interpolation bridge over the GENUINE GF(2¹⁶)
-- COMMUTATIVE RING (the `GF16` instance, +/* = the extracted gfAddV/gfMulV, transported from
-- AdjoinRoot POLY_poly through the bijection φ; UNCONDITIONAL since Stage 2 discharged hmul). These
-- connect the decoder's re-evaluation kernel to Mathlib's Polynomial.eval, NEEDING NO field inverse
-- and NO irreducibility — only the unconditional CommRing.
--   compute_at_eval — UNCONDITIONAL, in-boundary: gf.compute_at coeffs len x, read into GF16, equals
--     eval (ofU16 x) (gpoly coeffs len) — the decoder's evaluation kernel genuinely evaluates the
--     coefficient polynomial at x over GF(2¹⁶). Assembled from the banked RsBridge.compute_at_eq
--     (power-table + dot-product value spec), powerTable_eq_pow (the squaring recurrence builds
--     genuine field powers x^j, by induction using only the CommRing law x^(a+b)=x^a*x^b), and
--     dotV_eq_eval (dotV is Polynomial.eval of the coeff polynomial). About gf.compute_at.
--   decode_value_at_eval — UNCONDITIONAL, in-boundary: gf.decode_value_at xs ys n x, read into GF16,
--     equals eval (ofU16 x) (gpoly poly n) where poly is the value of gf.lagrange_interpolate xs ys n
--     — the decoder reconstructs the coeff polynomial and RE-EVALUATES it at x over GF(2¹⁶). This
--     upgrades the structural RsCapstone.decode_value_at_eq (raw dotV) to a genuine Polynomial.eval.
--     The remaining open obligation — identifying gpoly poly n with Lagrange.interpolate of the
--     samples (gfDivV = field inverse + basis matching) — is gated on Irreducible POLY_poly and is
--     NOT claimed here. About gf.decode_value_at / gf.lagrange_interpolate.
#print axioms Spqr.RsEvalBridge.compute_at_eval
#print axioms Spqr.RsEvalBridge.decode_value_at_eval

-- (Spqr.RsDivInverse): the DIVISION = FIELD-INVERSE bridge — reading the extracted Fermat-inverse
-- ladder gf.gf_div as the genuine GF(2¹⁶) field inverse. gf.gf_div numer denom (Extracted/Gf.lean)
-- runs 15 squaring iterations computing out = numer · denom^(2 + 4 + … + 2¹⁵) = numer · denom^(2¹⁶−2).
--   gfDivV_eq_fermat — UNCONDITIONAL, field-law-FREE: gf.gf_div numer denom (value gfDivV) is exactly
--     the pure squaring fold fermatFold denom numer 1 — a value spec of the extracted loop. About
--     gf.gf_div.
--   gf_div_eq_fermat — UNCONDITIONAL, field-law-FREE: read into the genuine GF(2¹⁶) CommRing GF16,
--     ofU16 (gfDivV numer denom) = ofU16 numer · (ofU16 denom)^(2¹⁶−2). Pins the value of gf.gf_div
--     over the ring WITHOUT the field inverse (only the unconditional CommRing + pow arithmetic).
--     About gf.gf_div.
--   gf_div_eq_inv — CONDITIONAL on Irreducible POLY_poly ALONE (strictly weaker than hmul+Irreducible
--     since hmul is discharged): reflected through gfRingEquiv : GF16 ≃+* AdjoinRoot POLY_poly, for
--     denom ≠ 0, the extracted gf.gf_div equals phi numer · (phi denom)⁻¹ — the genuine field inverse.
--     |AdjoinRoot POLY_poly| = 2¹⁶ (ZMod 2-finrank = natDegree POLY_poly = 16), so denom^(2¹⁶−1) = 1
--     (FiniteField.pow_card_sub_one_eq_one) ⇒ denom^(2¹⁶−2) = denom⁻¹. This is the field-inverse
--     ingredient the Lagrange-basis identification needs; irreducibility is a Fact premise, never an
--     axiom. About gf.gf_div.
#print axioms Spqr.RsDivInverse.gfDivV_eq_fermat
#print axioms Spqr.RsDivInverse.gf_div_eq_fermat
#print axioms Spqr.RsDivInverse.gf_div_eq_inv

-- (Spqr.RsPrepareBridge): the PREPARE = NODAL-PRODUCT bridge — the interpolation half's master
-- numerator polynomial, over the GENUINE GF(2¹⁶) COMMUTATIVE RING (UNCONDITIONAL, no irreducibility).
-- RsInterp.prepare_eq pinned gf.prepare xs n as the iterated window-fold prepareFoldFn (each iteration
-- one mult_xdiff_trailing = one (X − xs[i]) multiply, leading-coefficient-first layout); this closes
-- the polynomial-algebra reading of that fold.
--   prepare_eq_nodal — UNCONDITIONAL, in-boundary: for n ≤ 36, gf.prepare xs n succeeds with a
--     coefficient array p whose GF16 coefficient polynomial gpoly (p[·]) (n+1) equals the nodal product
--     ∏_{i<n}(X − C(ofU16 xs[i])). Proved by a window-invariant induction (WinInv_init / WinInv_step /
--     WinInv_fold): the loop's characteristic-two XOR carry c j ⊕ xs[i]·c(j+1) is exactly the
--     coefficient identity of multiply-by-(X − xs[i])-then-divide-by-X (coeff_X_sub_C_mul with − = + in
--     char 2) in the trailing-window layout, so after n steps the window holds ∏(X − xs[i]). Uses ONLY
--     the unconditional CommRing on GF16 (hmul discharged by Stage 2) — NO field inverse, NO
--     irreducibility. This nodal product is the master numerator each Lagrange basis polynomial
--     ℓ_i = ∏_{j≠i}(X − xs[j]) divides out one factor of; banking it over the extracted gf.prepare is
--     the foundational layer of the structural Lagrange-basis matching. About gf.prepare.
#print axioms Spqr.RsPrepareBridge.prepare_eq_nodal

-- (Spqr.RsCompleteBridge): the COMPLETE = SYNTHETIC-DIVISION bridge — the extracted gf.complete is the
-- synthetic division of the input coefficient polynomial by (X − C xs[i]), scaled by the Lagrange weight
-- and shifted up by one (× X), over the GENUINE GF(2¹⁶) COMMUTATIVE RING (UNCONDITIONAL, no irreducibility).
-- RsInterp.complete_eq pinned gf.complete as the long-division sweep divFold; this closes its polynomial
-- reading via a DivInv window-invariant induction (DivInv_init/_step/_fold: each step finalizes slot idx to
-- the scaled tail-Horner and carries slot idx−1 to the next un-scaled tail-Horner — the synthetic-division
-- recurrence) and the multiply-back identity (X − C p)·synQuot + C(remainder) = gpoly coeffs (n+1) (building
-- block synDiv_mul_back, abstract, NOT a headline). All three headlines mention gf.complete:
--   complete_eq_synDiv — UNCONDITIONAL, in-boundary: gf.complete coeffs xs ys n i succeeds with an array r
--     whose GF16 polynomial gpoly (r[·]) (n+1) = C(remainder) + C(scale)·X·synQuot, where remainder =
--     synTail(coeffs[·]) pix 0 (n+1) is the synthetic-division remainder, scale = ofU16(gfDivV ys[i] denomV)
--     the Lagrange weight, and synQuot the quotient of gpoly coeffs (n+1) by (X − C pix). The general
--     synthetic-division form of the extracted complete. NO field inverse, NO irreducibility, NO axiom.
--   complete_eq_synDiv_root — UNCONDITIONAL, in-boundary: when pix = xs[i] is a ROOT of the input
--     (eval (ofU16 xs[i]) (gpoly coeffs (n+1)) = 0, true for the prepare template), the remainder vanishes
--     and gpoly (r[·]) (n+1) = C(scale)·X·synQuot — the scaled quotient gpoly coeffs (n+1)/(X − C pix).
--   complete_prepare_eq_scaled_basis — UNCONDITIONAL, in-boundary: run on the gf.prepare template
--     (gpoly coeffs (n+1) = ∏_{k<n}(X − xs[k]), the banked RsPrepareBridge.prepare_eq_nodal), gf.complete
--     computes C(scale)·X·∏_{k≠i}(X − C(ofU16 xs[k])) — the scaled Lagrange basis numerator ℓ̃_i times X
--     (the upstream "working is x·<basis poly>" offset). So gf.complete divides the master nodal product by
--     (X − xs[i]) (removing the i-th factor) and scales by the Lagrange weight. Assembled from
--     complete_eq_synDiv_root + synQuot_nodal_eq (the synthetic quotient of nodal is the basis numerator,
--     by factoring out the i-th root and cancelling the monic X − C pix via mul_divByMonic_cancel_left —
--     a building block, NOT a headline). UNCONDITIONAL over the GF16 CommRing. NB: identifying scale with
--     the genuine Lagrange weight ys[i]·(∏(xs[i]−xs[j]))⁻¹ reads gfDivV as the field inverse (RsDivInverse.
--     gf_div_eq_inv, CONDITIONAL on Irreducible POLY_poly, the WALL); the loop0/loop1 basis-SUM assembly
--     into Lagrange.interpolate is the remaining piece. This banks the per-i numerator over the ring.
#print axioms Spqr.RsCompleteBridge.complete_eq_synDiv
#print axioms Spqr.RsCompleteBridge.complete_eq_synDiv_root
#print axioms Spqr.RsCompleteBridge.complete_prepare_eq_scaled_basis

-- (Spqr.RsLagrangeBridge): the LAGRANGE-ASSEMBLY bridge — the extracted gf.lagrange_interpolate
-- assembles the per-i scaled basis numerators (the banked gf.complete = scale·X·ℓ̃_i) into the
-- basis-weighted sum, and (conditional on irreducibility + distinct nodes) IS Mathlib's
-- Lagrange.interpolate. The loop0/loop1 shift reads working[k+1], dividing out the × X offset that
-- complete produced; the loop1 driver accumulates the per-i numerators (gfAddV = +). Two headlines,
-- both mention gf.lagrange_interpolate (via L1 and the banked complete/prepare value specs):
--   lagrange_interpolate_eq_basis_sum — UNCONDITIONAL, in-boundary: gf.lagrange_interpolate xs ys n
--     succeeds with an array out whose GF16 polynomial gpoly out n = Σ_{i<n} C(scaleᵢ)·∏_{k≠i}(X − xs[k])
--     — the Lagrange interpolant in numerator/weight form over the GENUINE GF(2¹⁶) commutative ring
--     (hmul discharged by Stage 2). NO field inverse, NO irreducibility, NO axiom. This is the
--     loop0/loop1 basis-SUM assembly the prior round flagged as the remaining item (1).
--   lagrange_interpolate_eq_interpolate — CONDITIONAL on [Fact (Irreducible POLY_poly)] + distinct
--     nodes (hdist) + nonzero Lagrange denominators (hdenom), in-boundary: gf.lagrange_interpolate xs
--     ys n succeeds with out whose gpoly out n, MAPPED through the ring iso gfRingEquiv into the genuine
--     field AdjoinRoot POLY_poly, equals Lagrange.interpolate (range n) (k↦phi xs[k]) (k↦phi ys[k]).
--     Reads gfDivV as the field inverse (RsDivInverse.gf_div_eq_inv) and the denominator as the erased
--     difference product (denomV_eq_erase_prod, char-2 XOR=− + distinct-node filter). This is the
--     interpolation-correctness identification the full decode∘encode=id bridge (RsCapstone.hbridge)
--     rests on; strictly WEAKER premise than the prior hmul+Irreducible pair (hmul discharged). The
--     only carried algebraic premise is irreducibility (the WALL), carried as [Fact …], never an axiom.
--   decode_value_at_eval_eq_interpolate — CONDITIONAL on [Fact (Irreducible POLY_poly)] + distinct
--     nodes (hdist) + nonzero Lagrange denominators (hdenom), in-boundary: the FULL hbridge premise,
--     DERIVED. gf.decode_value_at xs ys n x, decoded through phi, equals eval (phi x)
--     (Lagrange.interpolate (range n) (k↦phi xs[k]) (k↦phi ys[k])). Composes the UNCONDITIONAL
--     evaluation half (RsEvalBridge.decode_value_at_eval: decode = eval (ofU16 x) (gpoly poly n)) with
--     the interpolation half (lagrange_interpolate_eq_interpolate: map gfRingEquiv (gpoly poly n) =
--     Lagrange.interpolate) via the eval-commutes-with-ring-hom identity gfRingEquiv (eval r p) =
--     eval (gfRingEquiv r) (p.map gfRingEquiv) (Polynomial.eval_map / eval₂_at_apply). This is EXACTLY
--     the hbridge premise of RsCapstone.decode_value_at_roundtrip / RsFieldBridge.*_gf16 instantiated at
--     F = AdjoinRoot POLY_poly, dec = phi — so hbridge is now DERIVED, no longer assumed. About
--     gf.decode_value_at / gf.lagrange_interpolate. Only carried algebraic premise is irreducibility.
#print axioms Spqr.RsLagrangeBridge.lagrange_interpolate_eq_basis_sum
#print axioms Spqr.RsLagrangeBridge.lagrange_interpolate_eq_interpolate
#print axioms Spqr.RsLagrangeBridge.decode_value_at_eval_eq_interpolate

-- REFINEMENT: hdenom DERIVED from distinct nodes. denomV_ne_zero — the extracted denominator
-- denomV xs n xs[i] 1 0 (value of gf.complete_loop0's accumulator) is NONZERO, derived from
-- distinct nodes (hdist) in the genuine GF(2¹⁶) field: its image under the ring iso is the erased
-- difference product ∏_{k≠i}(phi xs[i] − phi xs[k]), a product of differences of distinct field
-- elements (phi injective), nonzero in the integral domain. CONDITIONAL on Irreducible POLY_poly +
-- distinct nodes. The two *_of_dist headlines re-state the L2/L3 bridge with hdenom DROPPED (derived
-- from hdist via denomV_ne_zero) — a strict reduction of the assumption surface, carrying only
-- irreducibility + distinct nodes. About gf.complete_loop0 (denomV) / gf.lagrange_interpolate /
-- gf.decode_value_at.
#print axioms Spqr.RsLagrangeBridge.denomV_ne_zero
#print axioms Spqr.RsLagrangeBridge.lagrange_interpolate_eq_interpolate_of_dist
#print axioms Spqr.RsLagrangeBridge.decode_value_at_eval_eq_interpolate_of_dist

-- SPQR typestate skeleton (the SCKA construction's transition structure): send/recv are total
-- pure dispatches over the 11-state machine (next state + emitted payload + output-key timing),
-- vulnerable_epoch is the total leakage predicate. This is what the SCKA security game binds to;
-- the crypto (codec/chain/MAC) is the verified primitive nodes, ML-KEM the assumed IND-CCA floor.
#print axioms Spqr.States.send_step_total
#print axioms Spqr.States.recv_step_total
#print axioms Spqr.States.vulnerable_epoch_total
#print axioms Spqr.States.init_a_total
#print axioms Spqr.States.init_b_total

-- SPQR typestate GRAPH lemmas (structural properties of the 11-state transition graph — what a
-- future SCKA game quantifies over; NO security game, value-level facts over the extracted dispatch).
-- (1) OUTPUT-KEY EMISSION TIMING. The transition functions return an output-key flag (the SCKA
-- "an output_key was produced this step" bit). send_step raises it for EXACTLY one state,
-- HeaderReceived (send_step_outputs_key_iff; the explicit emission send_step_headerReceived →
-- Ct1Sampled; and send_step_no_key_of_ne for the other ten). recv_step raises it for EXACTLY the
-- path EkSentCt1Received + in-window Ct2 + Done + accept (recv_step_outputs_key_iff; the explicit
-- emission recv_step_ekSentCt1Received_done → NoHeaderReceived; recv_step_no_key_of_ne elsewhere).
#print axioms Spqr.States.send_step_outputs_key_iff
#print axioms Spqr.States.send_step_headerReceived
#print axioms Spqr.States.send_step_no_key_of_ne
#print axioms Spqr.States.recv_step_outputs_key_iff
#print axioms Spqr.States.recv_step_ekSentCt1Received_done
#print axioms Spqr.States.recv_step_no_key_of_ne
-- (2) vulnerable_epoch TRACKS THE COMPROMISE SET. It is `none` for EXACTLY the three no-live-secret
-- states (KeysUnsampled / NoHeaderReceived / HeaderReceived — vulnerable_epoch_none_iff) and
-- `some s.epoch` for the other eight key-holding states (vulnerable_epoch_some_iff), always at the
-- state's OWN epoch, never a stale one (vulnerable_epoch_eq_epoch — no past-epoch leakage).
#print axioms Spqr.States.vulnerable_epoch_none_iff
#print axioms Spqr.States.vulnerable_epoch_some_iff
#print axioms Spqr.States.vulnerable_epoch_eq_epoch
-- (3) COUPLING (output flag × vulnerability). A key-emitting send lands in a vulnerable state at the
-- same epoch (send_step_output_target_vulnerable); the unique key-emitting recv is the round-CLOSING
-- key — it lands in the NoHeaderReceived reset (vulnerable_epoch = none), the dual structural fact
-- (recv_step_output_target_reset).
#print axioms Spqr.States.send_step_output_target_vulnerable
#print axioms Spqr.States.recv_step_output_target_reset

-- Demo 4 (message authentication): the extracted MAC `verify` is total and decides tag
-- equality (value adequacy), its Boolean view decides equality, and the canonical PRF-based
-- MAC (the libsignal HMAC shape) is perfectly complete — honest tags always verify.
#print axioms AuthMac.verify_spec_pointwise
#print axioms AuthMac.verifyB_eq_true_iff
#print axioms AuthMac.macAlg_perfectlyComplete

-- Demo 4 (UF-CMA reduction): the inductive real-world correspondence (the reduction simulated
-- through the real PRF equals the MAC game's internal oracle), the resulting equality of the
-- reduction's real-world acceptance with the MAC UF-CMA advantage, and the honest PRF-reduction
-- headline — the MAC's UF-CMA advantage is bounded by the reduction's PRF distinguishing
-- advantage plus its success against a random function.
#print axioms AuthMac.simulateQ_prfReal_fwdLog
#print axioms AuthMac.prfRealExp_reduction_eq
#print axioms AuthMac.macUF_le_prfAdvantage_add_RF

-- Demo 4 (random-function forgery bound): against a random function (the ideal world of the PRF
-- reduction), the reduction's forgery probability is bounded by `1/|Tag| = 2^-256` — a forgery on
-- an unqueried message can only succeed by guessing a uniformly random tag. Combined with the
-- reduction headline, this gives the closed UF-CMA bound `prfAdvantage + 1/|Tag|`.
#print axioms AuthMac.reduction_RF_le
#print axioms AuthMac.macUF_le
-- The `2^-256` reading of the `(Fintype.card Tag)⁻¹` term above is machine-checked, not informal:
#print axioms AuthMac.card_Tag

-- Demo 4 (SUF-CMA / strong unforgeability): for the canonical deterministic MAC, strong
-- unforgeability (pair-freshness) collapses to plain unforgeability — winning the pair-freshness
-- game on a queried message would force the forged tag to differ from the unique honest tag
-- `F_k(msg)`, which `verify` rejects. `sufAdv_le_ufAdv` is that pointwise gate implication (via the
-- honest-log invariant); `macSUF_le` composes it with the UF-CMA headline to give the same closed
-- bound `prfAdvantage + 1/|Tag|` for strong unforgeability.
#print axioms AuthMac.sufAdv_le_ufAdv
#print axioms AuthMac.macSUF_le

-- Demo 4 (SUF-CMA definitional cross-checks): the SUF-CMA game is defined here (not inherited from
-- VCVio), so it is a new trust boundary. These machine-checked lemmas pin the new game down: the
-- gate accepts exactly genuine fresh forgeries (`suf_gate_iff` — replay rejected, correct fresh tag
-- accepted), and strong unforgeability *equals* plain unforgeability for this canonical MAC
-- (`sufAdv_eq_ufAdv`, both directions — confirming the game is the genuinely stronger notion, not an
-- accidentally weaker or vacuous one).
#print axioms AuthMac.suf_gate_iff
#print axioms AuthMac.sufAdv_eq_ufAdv

-- Demo 4 (cost adequacy): the PRF reduction is efficient relative to the forger, in the
-- query-count measure (`IsTotalQueryBound`, native to the `OracleComp` model). The logging forward
-- oracle `fwdLogImpl` preserves query count (`isTotalQueryBound_run_simulateQ_fwdLogImpl_iff` — it
-- forwards every query 1:1, the log lives in the discarded `WriterT` layer), so the reduction makes
-- at most `qA + 1` queries when the forger makes `qA` (`reduction_queryBound` — only `O(1)`,
-- forger-independent overhead: one verification query). `reduction_polyQueryBound` packages this for
-- a poly-query forger family: it stays inside the poly-query efficiency class (`pA + 1`).
#print axioms AuthMac.isTotalQueryBound_run_simulateQ_fwdLogImpl_iff
#print axioms AuthMac.reduction_queryBound
#print axioms AuthMac.reduction_polyQueryBound

-- Demo 5 (KEM/DEM → PKE composition): a one-time symmetric DEM whose encryption is the
-- Aeneas-extracted 32-byte stream-cipher XOR (Demo 2's `combine` loop), keyed by a PRG seed, is
-- perfectly correct (`streamDEM_perfectlyCorrect` — decryption inverts encryption with probability
-- 1, via the extracted-loop involution). Composing it with an *abstract* IND-CPA KEM through
-- VCVio's `composeWithDEM` yields a public-key encryption scheme that is perfectly correct
-- (`composed_correct`, given KEM correctness) and whose one-time IND-CPA advantage is bounded by two
-- KEM IND-CPA advantages plus the DEM advantage (`composed_ind_cpa_le` — VCVio's composition bound,
-- with the four runtime-coherence side conditions discharged for `ProbCompRuntime.probComp`).
#print axioms Demo5KemDem.streamDEM_perfectlyCorrect
#print axioms Demo5KemDem.composed_correct
#print axioms Demo5KemDem.composed_ind_cpa_le

-- Demo 5 (DEM term ⇒ PRG, the substantive reduction): the extracted-stream-cipher DEM's one-time
-- IND-CPA advantage is bounded by twice the PRG distinguishing advantage of an explicit reduction
-- (`streamDEM_ind_cpa_le_prg`). When the PRG challenge block is the real keystream the simulation is
-- the DEM game; when it is uniform, `m_b ⊕ R` is a uniform block independent of `b` (XOR is a
-- permutation, `encEquiv`), so the guess is a fair coin — hence the DEM bias ≤ 2·PRG advantage. This
-- discharges the DEM term in `composed_ind_cpa_le` to the PRG assumption (the same one as Demo 2).
#print axioms Demo5KemDem.streamDEM_ind_cpa_le_prg

-- Demo 5 (end-to-end headline): chaining the two results above — the composed PKE's one-time
-- IND-CPA advantage bottoms out on just KEM-IND-CPA + PRG (no DEM term remains).
#print axioms Demo5KemDem.composed_ind_cpa_le_prg

-- Demo 5 (asymptotic, reusing VCVio's `Negligible`): if the KEM family is IND-CPA-secure and the
-- PRG family is secure, the composed KEM+DEM PKE family's one-time IND-CPA advantage is negligible.
#print axioms Demo5KemDem.composed_secure_asymptotic

-- ── B-irr: `Irreducible POLY_poly` closed UNCONDITIONALLY (THE WALL) ──────────────────────────
-- The last algebraic premise gating an unconditional Reed–Solomon decode∘encode=id over the real
-- extracted GF(2¹⁶) is `Irreducible (POLY_poly : (ZMod 2)[X])`, POLY_poly = X¹⁶+X¹²+X³+X+1. It is
-- closed here as a REAL theorem (no `Fact`-hypothesis, no axiom) via a Mathlib-free computable
-- `List Bool` mirror of F2[x] (`Gf16IrreducibleMirror`): a kernel `decide` checks no monic divisor
-- of degree 1..8 divides the bit pattern POLY (a reducible degree-16 poly over a field would have
-- an irreducible factor of degree ≤ 8). The mirror headline depends on NO axioms — it is a pure
-- kernel Bool reduction (`decide`, NOT `native_decide`).
#print axioms Spqr.Gf16IrreducibleMirror.noSmallFactor_POLY

-- The transport assembles the mirror result into `(ZMod 2)[X]`: `no_factor_le_8` discharges the
-- half-degree non-divisibility hypothesis of `Monic.irreducible_iff_lt_natDegree_lt` (natDegree
-- POLY_poly / 2 = 8, matching the mirror's k = 8), giving `POLY_poly_irreducible` unconditionally.
-- Only the three standard Mathlib axioms — NO sorryAx, NO ofReduceBool, NO custom axiom.
#print axioms Spqr.Gf16IrreducibleBridge.no_factor_le_8
#print axioms Spqr.Gf16IrreducibleBridge.POLY_poly_irreducible

-- The newly-UNCONDITIONAL downstream headlines: with `fact_POLY_poly_irreducible` now a real
-- (axiom-clean) instance, the seven downstream field/RS files' `[Fact (Irreducible POLY_poly)]`
-- binders are discharged. These wrappers restate the load-bearing capstones with that binder
-- DROPPED — the Reed–Solomon decode∘encode=id over the genuine GF(2¹⁶), the GF(2¹⁶) field inverse
-- via `gf.gf_div`, the nonzero-element inverse, and the Fermat inverse in `AdjoinRoot POLY_poly`.
#print axioms Spqr.Gf16IrreducibleBridge.decode_value_at_roundtrip_gf16_unconditional
#print axioms Spqr.Gf16IrreducibleBridge.gf_div_eq_inv_unconditional
#print axioms Spqr.Gf16IrreducibleBridge.gfMulV_exists_inv_unconditional

-- ── Wire phase: HmacPrf's abstract compression `f` wired to the GENUINE EXTRACTED sha256_compress ──
-- `compress_eq_ok`: THE TRUSTED LINK — the totalized pure `compressPure` provably equals the
-- `Result`-monadic extracted `sha256.sha256_compress` on ALL inputs (derived from
-- `Sha256.sha256_compress_total`, NOT a hand-rewrite of the extracted def; `compressPure` reduces by
-- `rfl` through `sha256.sha256_compress`). `sha256_loop2_eq_cascade`: the prose "sha256 is
-- `cascade sha256_compress H0`" is now a THEOREM — the extracted multi-block driver returns exactly
-- `HmacPrf.cascade compressPure H0 (extractBlocks buf nblocks)` (a `Std.loop.spec_decr_nat` fold
-- identity over the extracted offset/extract/compress steps). `cascade_sha256CompressionPRF_eval`:
-- `compressionPRF`'s abstract `f` instantiated at the extracted `compressPure`.
-- `sha256_cascade_prfAdvantage_le_qmul`: the SPQR-path floor headline — under the compression-PRF
-- assumption (the named atomic floor, a HYPOTHESIS via the per-hop bound, NEVER an axiom), the
-- fixed-length cascade of the EXTRACTED compression has advantage ≤ q·ε (wiring HmacPrf's cascade
-- hybrid `cascadeFixedLen_prfAdvantage_le_qmul_simCorrect` at the real code). Axiom set is clean
-- ([propext, Classical.choice, Quot.sound]); the compression-PRF assumption + the cascade hybrid's
-- per-hop/endpoint pins + HKDF-Extract/ratchet-PRG bridges remain the honest open obligations.
#print axioms Sha256Wire.compress_eq_ok
#print axioms Sha256Wire.sha256_loop2_eq_cascade
#print axioms Sha256Wire.cascade_sha256CompressionPRF_eval
#print axioms Sha256Wire.sha256_cascade_prfAdvantage_le_qmul
-- The fold-identity building blocks (extracted-code value lemmas feeding `sha256_loop2_eq_cascade`):
-- `extract_block_eq_ok` projects the extracted 64-byte block-extraction to its pure `Result`-free
-- value; `mul_offset_eq` pins the loop's `i * 64` byte offset arithmetic; `sha256_loop2_eq_cascade_suffix`
-- is the strengthened induction hypothesis (the loop from block `i` returns the cascade over the
-- remaining `extractBlocks` suffix). All over the EXTRACTED `sha256_compress` (via `compressPure` /
-- `compress_eq_ok`), all axiom-clean.
#print axioms Sha256Wire.extract_block_eq_ok
#print axioms Sha256Wire.mul_offset_eq
#print axioms Sha256Wire.sha256_loop2_eq_cascade_suffix

-- ── Per-hop reduction DISCHARGED at the single-block slice (Bellare CRYPTO 2006 cascade lemma /
--    FCF GNMAC_PRF.v + hF.v, the per-hop swap) ─────────────────────────────────────────────────
-- The cascade `q·ε` headline `sha256_cascade_prfAdvantage_le_qmul` / `cascadeFixedLen_..._qmul_simCorrect`
-- carries the two per-hop simulation-correctness pins as HYPOTHESES:
--   hreal i : H (i+1) = f.prfRealExp (red i)   (the i-th hop's real side IS the reduction's real exp)
--   hideal i : H i    = prfIdealExp (red i)    (and its ideal side IS the reduction's ideal exp).
-- This block DISCHARGES both pins, genuinely and hypothesis-free, at the single-block (q=1, n=1)
-- slice — the FCF hF.v `hF_oracle`/`PRF_h_A` routing specialized to the one swapped compression
-- call, on the slice where the lazy-RO interpolation (the lossy step, FCF hF.v `G1_G2_equiv`) is
-- EXACT because `[b] ↦ b` is a bijection. The compression-PRF advantage (`ε`/`hbound`) stays the
-- atomic floor — a hypothesis, never proved, never an axiom (exactly as Bellare assumes).
--   `singleBlockRed_prfRealExp` — pin `hreal` DISCHARGED: the concretely-built reduction's real
--     compression-PRF experiment IS the head-block cascade real experiment (simulateQ_compose; the
--     single challenge call computes the whole single-block cascade, no interpolation).
--   `singleBlockRed_prfIdealExp` — pin `hideal` DISCHARGED: the reduction's ideal experiment IS the
--     head-block ideal handler (a lazy RO keyed on the head block) — an equality, not an ≤-with-WCR,
--     because on length-1 queries head-block-keyed and whole-list-keyed random oracles coincide.
--   `projCache_cacheQuery` — the `[b] ↦ b` cache bijection commutes with caching (the structural
--     core making head-block-keyed = whole-list-keyed on the single-block slice).
--   `wrapSingleton_prfIdealExp` — the TRUE-IDEAL coupling: on the single-block image the head-block
--     ideal experiment IS the whole-list ideal experiment `prfIdealExp (wrapSingleton advB)` (the
--     two lazy random oracles coincide along `projCache`, via the invariant-gated state projection).
--   `singleBlockRed_wrapSingleton` — round-trip: reducing the wrapped adversary recovers it exactly.
--   `singleBlockRed_wrapSingleton_prfAdvantage` — hence the reduction is advantage-PRESERVING (the
--     witness that the q=1 reduction is non-vacuous, not a degenerate map).
--   `headBlockPRF_wrapSingleton_prfRealExp` — real-endpoint: on the wrapped slice the head-block
--     real experiment IS the genuine `cascadeFixedLenPRF f 1` real experiment.
--   `singleBlockHop_eq_prfAdvantage` / `singleBlockCascadeHop_eq_prfAdvantage` /
--     `..._trueIdeal` — the single hop EQUALS the reduction's compression-PRF advantage `f.prfAdvantage advB`
--     (the `_trueIdeal` form lands its ideal endpoint on the actual whole-list `prfIdealExp` on the nose).
--   `cascadeFixedLen_prfAdvantage_le_one_smul_of_compressionPRF` — THE HYPOTHESIS-FREE CASCADE BOUND:
--     instantiates `cascadeFixedLen_prfAdvantage_le_qmul_simCorrect` at q=1 with the concretely-built
--     `singleBlockRed (wrapSingleton advB)` and BOTH pins PROVED (not assumed) — the single-block
--     cascade PRF advantage ≤ 1·ε carrying ONLY the compression-PRF bound `hbound`, no simCorrect hyps.
-- All axiom-clean ([propext, Classical.choice, Quot.sound]); `hbound` is the only carried hypothesis.
#print axioms HmacPrf.singleBlockRed_prfRealExp
#print axioms HmacPrf.singleBlockRed_prfIdealExp
#print axioms HmacPrf.projCache_cacheQuery
#print axioms HmacPrf.wrapSingleton_prfIdealExp
#print axioms HmacPrf.singleBlockRed_wrapSingleton
#print axioms HmacPrf.singleBlockRed_wrapSingleton_prfAdvantage
#print axioms HmacPrf.headBlockPRF_wrapSingleton_prfRealExp
#print axioms HmacPrf.singleBlockHop_eq_prfAdvantage
#print axioms HmacPrf.singleBlockCascadeHop_eq_prfAdvantage
#print axioms HmacPrf.singleBlockCascadeHop_eq_prfAdvantage_trueIdeal
#print axioms HmacPrf.cascadeFixedLen_prfAdvantage_le_one_smul_of_compressionPRF
-- Wired at the EXTRACTED sha256_compress (via `compressPure`): the single-block cascade of the real
-- extracted SHA-256 compression is a PRF up to 1·ε, carrying ONLY `hbound` — no `hreal`/`hideal`.
#print axioms Sha256Wire.sha256_singleBlockCascade_prfAdvantage_le_one_smul_of_compressionPRF

#print axioms Spqr.Gf16IrreducibleBridge.adjoinRoot_pow_eq_inv_unconditional
