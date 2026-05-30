# Feasibility: an end-to-end Rust -> Lean -> game-based-security demo

Can Aeneas (Rust -> Lean) + VCVio (game-based crypto in Lean) be glued into a
small, complete, end-to-end proof? This note researches both tools and proposes
a concrete minimal demo.

Created 2026-05-29.

## TL;DR verdict

YES, feasible, and the pieces line up unusually well:

- Both are **native Lean 4 + Mathlib** libraries -> one proof assistant, no
  cross-prover seam. This kills the "two PAs, glue by hand" problem from the
  theory note (rough_theory.md sec. 5/7).
- VCVio is exactly the "probabilistic-relational layer in Lean" that the theory
  note said you'd otherwise have to build. It already exists, with a relational
  program logic (the ~[eps] framework realized).
- VCVio ships a **OneTimePad / perfect-secrecy** result. That is the smallest
  possible complete instance of the whole stack: information-theoretic, eps = 0,
  NO hardness assumption, NO reduction, NO random oracle. Ideal first demo.

Main risk is mundane but real: **toolchain skew.** VCVio pins Lean v4.28.0;
Aeneas's Lean backend pins v4.30.0-rc2. Both ride Mathlib, so the demo's real
cost is aligning them on one toolchain/Mathlib commit, not the math.

================================================================================

## The two tools

### Aeneas  (= "T" of rough_theory.md sec. 6)
- Toolchain: `Rust --Charon--> LLBC --Aeneas--> Lean` (also F*/Rocq/HOL4).
  Lean + HOL4 are the most mature backends (partial functions, extrinsic
  termination proofs, monadic tactics).
- LIFTS safe Rust into a PURE functional model; borrows/region types erased.
  Output lives in a `Result` monad (`.ok` / `.fail` / `.div`) to model
  panics/partiality.
- Real use: Microsoft's SymCrypt C->Rust verification effort; recent jxl-rs
  case study (Protzenko, May 2026). So it handles nontrivial real Rust.
- Lean backend pins `v4.30.0-rc2` (main); tutorial historically tracked
  v4.11 .. v4.15-rc1, i.e. it follows recent Lean closely.

### VCVio  (= the Lean realization of rough_theory.md sec. 5)
- "Verified Cryptography in Lean via Oracle Effects and Handlers"
  (Tuma et al., Verified-zkEVM org; eprint 2026/899; forking-lemma /
  Fiat-Shamir paper eprint 2024/1819). The Lean analogue of Coq's FCF.
- Core API:
    OracleComp spec a    free monad: "return a" | "query oracle; continue"
    evalDist             denotational semantics -> SPMF (sub-PMF) distribution
    simulateQ            operational semantics: substitute oracle impls
                         (logging / caching / ROM pre-sampling)
- Program logic = the graded-relation framework, concretely:
    relational mode  RelTriple   coupling-based game-equivalence  (the ~[eps])
    unary mode       Hoare triples bounding event probability     (Pr[bad])
    tactics          rvcstep / vcstep   step through hops
- Case studies: OneTimePad, ElGamal (IND-CPA / DDH), Schnorr (EUF-CMA),
  RO commitment, Bellare-Neven forking lemma; downstream LatticeCrypto
  (ML-KEM, ML-DSA, Falcon).
- Pins Lean `v4.28.0` (master).

================================================================================

## How they compose (the glue)

The bottom link from rough_theory.md sec. 7 splits into:
  (a) functional   f_rust = f_spec        -- Aeneas proves, in Lean, eps = 0
  (b) idealization game built from f_spec   -- modeling step
VCVio supplies the game world for (b); Aeneas supplies f_rust for (a).

GLUE POINT: VCVio's `encrypt : k -> msg -> OracleComp spec C`. A pure Aeneas
function embeds via the `pure` constructor (no oracle queries):

    encrypt k m  :=  pure (bridge (f_rust (unbridge k) (unbridge m)))

Two small obligations make this rigorous -- and these ARE the theory note's
"value adequacy" obligation, made concrete:

  1. Result-discharge:  prove  f_rust k m = .ok (...)  always (no panic/overflow),
     so it collapses to a total pure function.
  2. Type bridge:       Aeneas emits its own `U8` / `Array U8 n#usize`; VCVio
     reasons over Mathlib types (`BitVec n`, `Fin`, `ZMod`, `PMF`). Define a
     coercion `bridge`/`unbridge` and prove the Aeneas op corresponds to the
     math op (e.g. Aeneas byte-array XOR  =  `BitVec` xor). THIS lemma IS
     `f_rust = f_spec`.

Mapping to rough_theory.md boundaries:
  sec. 6 obligation (1) value adequacy   -> obligations 1 + 2 above (the demo).
  sec. 6 obligation (2) cost adequacy     -> VACUOUS for OTP (info-theoretic;
                                             eps = 0 regardless of A's runtime).
  sec. 6 obligation (3) observation adeq. -> OUT OF SCOPE (timing side channels);
                                             flag as trusted assumption.

That OTP makes (2) vacuous and (b) trivial is precisely why it is the right
FIRST demo: it exercises the value-adequacy link fully and end-to-end while
zeroing out everything that would otherwise need a reduction or a cost model.

================================================================================

## Concrete demo: end-to-end one-time pad

GOAL: real Rust XOR cipher  ->(Charon+Aeneas)->  Lean function  ->(VCVio)->
machine-checked perfect secrecy. All in one Lean project. eps = 0 throughout.

### Step 0 -- Rust source (illustrative)
```rust
// otp.rs   -- fixed 32-byte block; no unsafe, no FFI: in Aeneas's subset
pub fn xor(k: [u8; 32], m: [u8; 32]) -> [u8; 32] {
    let mut c = [0u8; 32];
    let mut i = 0;
    while i < 32 { c[i] = k[i] ^ m[i]; i += 1; }
    c
}
```

### Step 1 -- lift with Charon + Aeneas
```
charon --input otp.rs            # -> otp.llbc
aeneas -backend lean otp.llbc    # -> Otp.lean
```
Yields (shape, illustrative):
```lean
def xor (k m : Array U8 32#usize) : Result (Array U8 32#usize) := ...
```

### Step 2 -- discharge Result + bridge to a math type (value adequacy)
```lean
-- no panic / always succeeds
theorem xor_ok (k m) : ∃ c, Otp.xor k m = .ok c := ...
-- pure total version
def enc (k m : BitVec 256) : BitVec 256 := ...           -- via bridge
-- THE adequacy lemma: Aeneas op = spec op
theorem enc_spec (k m : BitVec 256) : enc k m = k ^^^ m := ...
-- correctness (decrypt ∘ encrypt = id), free from xor self-inverse
theorem dec_enc (k m) : enc k (enc k m) = m := by simp [enc_spec, BitVec.xor_assoc]
```

### Step 3 -- instantiate VCVio SymmEncAlg with the Aeneas function
```lean
def otpScheme : SymmEncAlg spec (K := fun _ => BitVec 256)
                               (M := fun _ => BitVec 256)
                               (C := fun _ => BitVec 256) where
  keygen _ := uniformOfFintype (BitVec 256)        -- uniform key
  encrypt k m := pure (enc k m)                    -- <-- the Aeneas fn, via `pure`
  decrypt k c := pure (enc k c)
```

### Step 4 -- prove perfect secrecy via VCVio's Shannon theorem
VCVio gives `perfectSecrecyAt` and the constructive direction:
  keygen uniform  AND  each (m,c) realized by a UNIQUE key  =>  perfectSecrecyAt.
Discharge both for OTP:
  - keygen uniform: by construction (Step 3).
  - unique key: k = m ^^^ c is the unique key sending m to c (from enc_spec).
```lean
theorem otp_perfectly_secret : otpScheme.perfectSecrecyAt ... := by
  apply SymmEncAlg.perfectSecrecy_of_uniform_unique
  · exact keygen_uniform
  · intro m c; exact ⟨m ^^^ c, by simp [enc_spec], by ...⟩   -- existence+uniqueness
```

RESULT: a closed Lean proof that the cipher COMPILED FROM REAL RUST is perfectly
secret -- the complete `P_concrete ~[0] G_0 ~[0] IDEAL` path, mechanized.

================================================================================

## Risks / costs (honest)

1. **Toolchain alignment (the real work).** VCVio @ v4.28.0 vs Aeneas Lean @
   v4.30.0-rc2, both on Mathlib. Options:
     (a) pin Aeneas Lean backend to a commit built on v4.28.0 to match VCVio; or
     (b) bump VCVio to v4.30 (more churn: Mathlib API drift).
   Likely a day or two of dependency yak-shaving; the math is easy, this isn't.
2. **Result-monad discharge.** Trivial for fixed-size byte XOR; grows with code
   complexity (overflow/index reasoning).
3. **Type bridge.** Aeneas `U8`/`Array` <-> Mathlib `BitVec`. Small, reusable;
   this lemma IS the value-adequacy obligation -- worth building cleanly once.
4. **What it does NOT exercise.** OTP is info-theoretic, so cost adequacy
   (sec.-6 obligation 2) is vacuous and there is no reduction term. The demo
   proves the PLUMBING end-to-end but not the parts that bite at protocol scale.
5. **Side channels** (sec.-6 obligation 3) remain a trusted assumption, outside
   the proof, as always.

================================================================================

## Stretch: demo 2 (exercises a real reduction)

To exercise cost adequacy and a genuine eps > 0 reduction, lift a PRG/PRF-based
or ElGamal-style construction:
  - Rust: a stream cipher = PRG ^ message, or ElGamal over a group.
  - VCVio already has PRG.lean, PRF.lean, ElGamal (IND-CPA from DDH).
  - Now the chain is  P_concrete ~[0] G_0 ~[eps_DDH] ... ~[0] IDEAL, with a real
    reduction edge, and the PPT/cost quantifiers stop being vacuous -- forcing
    the cost-adequacy question (sec. 8 of rough_theory.md, the open hinge) into
    the open. Bigger lift; do OTP first.

Natural progression toward the libsignal goal: OTP -> PRG stream cipher ->
AEAD -> a single ratchet step. Each step adds exactly one of the obligations the
theory note enumerates.

================================================================================

## Sources

- Aeneas: https://github.com/AeneasVerif/aeneas , https://aeneasverif.github.io/ ,
  tutorial https://reservoir.lean-lang.org/@AeneasVerif/tutorial ,
  jxl-rs case study https://jonathan.protzenko.fr/2026/05/05/jxl-rs.html ,
  Lean-lang feature https://lean-lang.org/use-cases/aeneas/
- VCVio: https://github.com/dtumad/VCV-io ,
  reservoir https://reservoir.lean-lang.org/@dtumad/VCVio ,
  paper (eprint 2026/899) https://eprint.iacr.org/2026/899 ,
  forking/Fiat-Shamir (eprint 2024/1819) https://eprint.iacr.org/2024/1819
- Toolchains observed: VCVio lean-toolchain = leanprover/lean4:v4.28.0 ;
  Aeneas backends/lean/lean-toolchain = v4.30.0-rc2 (checked 2026-05-29).
