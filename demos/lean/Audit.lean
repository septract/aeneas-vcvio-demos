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
import Demos.Spqr.Gf
import Demos.Spqr.Authenticator
import Demos.AuthChannel.Mac
import Demos.AuthChannel.SufCma
import Demos.AuthChannel.MacCost
import Demos.KemDem.Composition
import Demos.Spqr.States
import Demos.Crypto.Sha256

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

-- Demo 3 (meaty node): the ratchet's block generator is the real, extracted ChaCha20 block
-- function. Value adequacy = totality of the ARX code; security = the generic hybrid bound,
-- now over genuine arithmetic Rust.
#print axioms RatchetChacha.chacha20_block_total
#print axioms RatchetChacha.chacha_ratchet_advantage_le_sum
#print axioms RatchetChacha.chacha_ratchet_secure_asymptotic

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
-- KDF-input premise the AKE proof rests on (the segment ordering is the BJKS-attack-relevant part).
#print axioms Pqxdh.pqxdh_secret_input_spec
#print axioms Pqxdh.pqxdh_secret_input_with_opk_spec
-- The associated data AD = EncodeEC(IK_A) ‖ EncodeEC(IK_B) (two 0x05-tagged 33-byte keys) — the
-- transcript-MACed identity binding, the exact construction the BJKS re-encapsulation attack hit.
#print axioms Pqxdh.associated_data_spec

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

-- SPQR typestate skeleton (the SCKA construction's transition structure): send/recv are total
-- pure dispatches over the 11-state machine (next state + emitted payload + output-key timing),
-- vulnerable_epoch is the total leakage predicate. This is what the SCKA security game binds to;
-- the crypto (codec/chain/MAC) is the verified primitive nodes, ML-KEM the assumed IND-CCA floor.
#print axioms Spqr.States.send_step_total
#print axioms Spqr.States.recv_step_total
#print axioms Spqr.States.vulnerable_epoch_total
#print axioms Spqr.States.init_a_total
#print axioms Spqr.States.init_b_total

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
