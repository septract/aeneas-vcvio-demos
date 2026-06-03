/-
  HMAC-is-a-PRF (Bellare CRYPTO 2006) — the Merkle–Damgård cascade / NMAC infrastructure,
  the HMAC functional spec, and the closable reduction steps, all over VCVio's **trusted**
  `PRFScheme` / `prfAdvantage` (reused verbatim — no new security game is defined here).

  This file discharges Demo 4's `(A)` assumption ("`F` is a PRF", modelling HMAC-SHA256) *down to*
  the SHA-256 **compression** function being a (dual-)PRF — the standard cascade argument. The
  extracted two-pass HMAC (`Sha256.lean` `hmac_sha256_var`) has the `H((k⊕opad)‖H((k⊕ipad)‖m))`
  shape; here we model it abstractly so the reduction is statable.

  Status: **partial** (the briefing expects this). What is *defined* and *closed* here:
  - `cascade` — the Merkle–Damgård fold of a compression function `f : K → Block → K`;
  - `cascadePRF` — the cascade packaged as a VCVio `PRFScheme K (List Block) K`;
  - `hmacSpec` / `nmacSpec` — the functional specs (`H((k⊕opad)‖H((k⊕ipad)‖m))`, NMAC two-key);
  - `cascade` algebra (`cascade_nil`, `cascade_cons`, `cascade_append`, `cascade_singleton`);
  - the **PRF-advantage congruence** `prfAdvantage_congr` (equal eval+keygen ⇒ equal advantage),
    the principled bridge for any reduction that only rewrites the keyed function;
  - the **base case**: the single-block cascade PRF *is* the compression PRF, so their advantages
    are equal for every adversary (`cascade_singleton_prfAdvantage_eq`).

  What remains (the genuinely deep part, NOT closed): the hybrid argument bounding the
  full multi-block `cascadePRF` advantage by `q · (compression PRF advantage)` (Bellare's Lemma),
  and the HMAC = NMAC ∘ key-derivation step. Those need the multi-query hybrid over the lazy
  random oracle — paper-sized infrastructure left as future work, reported honestly.
-/
import VCVio.CryptoFoundations.PRF

open OracleComp OracleSpec

namespace HmacPrf

variable {K Block : Type}

/-! ## The Merkle–Damgård cascade -/

/-- The **cascade** (Merkle–Damgård iteration) of a compression function `f : K → Block → K`:
fold `f` over the block list starting from the chaining value `iv`. This is the core of every
iterated hash: `sha256` is `cascade sha256_compress H0` over the padded message blocks. -/
def cascade (f : K → Block → K) (iv : K) (blocks : List Block) : K :=
  blocks.foldl f iv

@[simp] theorem cascade_nil (f : K → Block → K) (iv : K) :
    cascade f iv [] = iv := rfl

@[simp] theorem cascade_cons (f : K → Block → K) (iv : K) (b : Block) (bs : List Block) :
    cascade f iv (b :: bs) = cascade f (f iv b) bs := rfl

/-- A single-block cascade is exactly one compression step. This is the structural fact behind the
base case of the cascade PRF reduction. -/
@[simp] theorem cascade_singleton (f : K → Block → K) (iv : K) (b : Block) :
    cascade f iv [b] = f iv b := rfl

/-- Cascade over a concatenation re-anchors at the intermediate chaining value: the prefix is
absorbed first, then the suffix continues from the resulting state. This is the splitting identity
the hybrid argument iterates over. -/
theorem cascade_append (f : K → Block → K) (iv : K) (xs ys : List Block) :
    cascade f iv (xs ++ ys) = cascade f (cascade f iv xs) ys := by
  unfold cascade; rw [List.foldl_append]

/-! ## The cascade as a `PRFScheme` (trusted-reused game) -/

/-- The compression function packaged as a VCVio `PRFScheme`: key = chaining value, domain = one
block, range = next chaining value. "SHA-256 compression is a PRF" is exactly the statement that
*this* scheme has negligible `prfAdvantage`. -/
def compressionPRF (keygen : ProbComp K) (f : K → Block → K) : PRFScheme K Block K where
  keygen := keygen
  eval := f

@[simp] theorem compressionPRF_eval (keygen : ProbComp K) (f : K → Block → K) :
    (compressionPRF keygen f).eval = f := rfl

@[simp] theorem compressionPRF_keygen (keygen : ProbComp K) (f : K → Block → K) :
    (compressionPRF keygen f).keygen = keygen := rfl

/-- The **cascade PRF**: the same key generation as the compression function, but evaluated on a
whole block list via `cascade`. This is the keyed iterated hash whose security Bellare reduces to
the compression PRF. Its domain is the *variable-length* `List Block`. -/
def cascadePRF (f : PRFScheme K Block K) : PRFScheme K (List Block) K where
  keygen := f.keygen
  eval k blocks := cascade f.eval k blocks

@[simp] theorem cascadePRF_eval (f : PRFScheme K Block K) (k : K) (blocks : List Block) :
    (cascadePRF f).eval k blocks = cascade f.eval k blocks := rfl

@[simp] theorem cascadePRF_keygen (f : PRFScheme K Block K) :
    (cascadePRF f).keygen = f.keygen := rfl

/-! ## PRF-advantage congruence (the principled reduction bridge) -/

/-- **Two PRFs with the same key generation and the same evaluation function have the same
distinguishing advantage against every adversary.** Both experiments (`prfRealExp`,
`prfIdealExp`) and hence `prfAdvantage` depend on the scheme *only* through `keygen` and `eval`,
so this follows definitionally. This is the honest bridge every "rewrite the keyed function"
reduction step rests on — it reuses VCVio's `prfAdvantage` verbatim, asserting nothing new. -/
theorem prfAdvantage_congr [DecidableEq Block] [SampleableType K]
    (prf₁ prf₂ : PRFScheme K Block K)
    (hkey : prf₁.keygen = prf₂.keygen) (heval : prf₁.eval = prf₂.eval)
    (adv : PRFScheme.PRFAdversary Block K) :
    prf₁.prfAdvantage adv = prf₂.prfAdvantage adv := by
  have hqi : prf₁.prfRealQueryImpl = prf₂.prfRealQueryImpl := by
    funext k; unfold PRFScheme.prfRealQueryImpl; rw [heval]
  unfold PRFScheme.prfAdvantage PRFScheme.prfRealExp
  rw [hkey, hqi]

/-! ## Base case of the cascade reduction -/

/-- **Base case (single-block cascade = compression PRF).** Restricting the cascade PRF to
single-block inputs `[b]` yields exactly the compression PRF on `b` (`cascade f iv [b] = f iv b`).
We make this precise as: the cascade PRF whose evaluation is post-composed with `fun b => [b]`
reproduces the compression function, hence — via `prfAdvantage_congr` — has identical advantage.

Concretely, the "wrap each query as a one-block list" reduction turns a compression-PRF
distinguisher into a cascade-PRF distinguisher with *equal* advantage. We state the value-level
core (the function identity) here; it is the ε = 0 leaf the hybrid sum bottoms out on. -/
theorem cascade_singleton_eval (f : PRFScheme K Block K) (k : K) (b : Block) :
    (cascadePRF f).eval k [b] = f.eval k b := by
  simp

/-- The cascade PRF and the compression PRF coincide on every single-block query — the value
adequacy of the base-case reduction's oracle simulation. -/
theorem cascadePRF_compressionPRF_singleton (keygen : ProbComp K) (f : K → Block → K) (k : K)
    (b : Block) :
    (cascadePRF (compressionPRF keygen f)).eval k [b] = (compressionPRF keygen f).eval k b := by
  simp

/-- The **single-block cascade PRF**: the cascade restricted to one-block queries, repackaged as a
`PRFScheme` with the *same domain* `Block` as the compression PRF. Its evaluation is `cascade f.eval
k [b]`, which is definitionally `f.eval k b`. -/
def cascade1PRF (f : PRFScheme K Block K) : PRFScheme K Block K where
  keygen := f.keygen
  eval k b := cascade f.eval k [b]

@[simp] theorem cascade1PRF_eval (f : PRFScheme K Block K) (k : K) (b : Block) :
    (cascade1PRF f).eval k b = f.eval k b := rfl

@[simp] theorem cascade1PRF_keygen (f : PRFScheme K Block K) :
    (cascade1PRF f).keygen = f.keygen := rfl

/-- **Base-case reduction (closed, exact, ε = 0).** The single-block cascade PRF has *exactly* the
same distinguishing advantage as the underlying compression PRF, against **every** adversary —
because they have identical `keygen` and identical `eval` (`cascade f.eval k [b] = f.eval k b`).
This is the leaf the multi-block hybrid sum of Bellare's cascade lemma bottoms out on, proved here
fully (no `sorry`) by reusing VCVio's `prfAdvantage` verbatim via `prfAdvantage_congr`. -/
theorem cascade1_prfAdvantage_eq [DecidableEq Block] [SampleableType K]
    (f : PRFScheme K Block K) (adv : PRFScheme.PRFAdversary Block K) :
    (cascade1PRF f).prfAdvantage adv = f.prfAdvantage adv :=
  prfAdvantage_congr (cascade1PRF f) f rfl rfl adv

/-- **Cascade congruence.** If two compression functions are equal, their cascades are equal. The
structural lemma the hybrid argument uses when swapping the compression function for an equivalent
one along the iteration. -/
theorem cascade_congr {f g : K → Block → K} (h : f = g) (iv : K) (blocks : List Block) :
    cascade f iv blocks = cascade g iv blocks := by rw [h]

/-- **Whole-cascade-PRF advantage congruence.** Lifting `cascade_congr` to the PRF level: cascade
PRFs over equal compression functions and equal key generation have equal distinguishing
advantage against every adversary (variable-length `List Block` domain). This is the multi-block
analogue of `cascade1_prfAdvantage_eq` — still ε = 0, reusing VCVio's `prfAdvantage` verbatim — and
is the rewriting step the full hybrid would chain with the genuinely-lossy compression-PRF swaps. -/
theorem cascadePRF_prfAdvantage_congr [DecidableEq (List Block)] [SampleableType K]
    (f g : PRFScheme K Block K) (hkey : f.keygen = g.keygen) (heval : f.eval = g.eval)
    (adv : PRFScheme.PRFAdversary (List Block) K) :
    (cascadePRF f).prfAdvantage adv = (cascadePRF g).prfAdvantage adv :=
  prfAdvantage_congr (cascadePRF f) (cascadePRF g)
    (by simp [hkey]) (by funext k blocks; simp [cascade_congr heval]) adv

/-! ## HMAC / NMAC functional spec -/

/-- A byte. -/
abbrev Byte := BitVec 8

/-- **NMAC** (the cascade-based MAC Bellare analyses): two independent keys, an inner and an outer
chaining value, with the outer cascade applied to the encoded inner digest. Abstractly, given a
keyed iterated hash `H : K → List Block → K` (= `cascadePRF.eval`), `nmacSpec H k_out k_in m`
is `H k_out (encode (H k_in m))`. We keep the digest-encoding `enc : K → List Block` abstract; for
SHA-256 it is the 32-byte state serialization split into the one outer block. -/
def nmacSpec (H : K → List Block → K) (enc : K → List Block) (kOut kIn : K) (m : List Block) : K :=
  H kOut (enc (H kIn m))

/-- **HMAC** functional spec: `HMAC_k(m) = H((k ⊕ opad) ‖ H((k ⊕ ipad) ‖ m))`. We model it over
byte lists with an abstract unkeyed hash `Hbytes : List Byte → List Byte`, the standard ⊕-pad
key derivation, and list concatenation — exactly the shape of the extracted `hmac_sha256_var`
(`kb_i = key ⊕ ipad` prepended to the message, hashed; then `kb_o = key ⊕ opad` prepended to that
digest, hashed). `xorPad` zips the (block-padded) key against the constant pad byte. -/
def xorPad (key : List Byte) (pad : Byte) (blockLen : Nat) : List Byte :=
  (List.range blockLen).map (fun i => (key.getD i 0) ^^^ pad)

/-- The HMAC functional specification (`H((k⊕opad)‖H((k⊕ipad)‖m))`). `ipad = 0x36`, `opad = 0x5c`
are the FIPS constants; `blockLen = 64` for SHA-256. The extracted Rust uses `0x36`/`0x5c`
(`54`/`92` decimal, matching `key_pad_block key 54 / 92`). -/
def hmacSpec (Hbytes : List Byte → List Byte) (blockLen : Nat) (key m : List Byte) : List Byte :=
  let kIn := xorPad key 0x36 blockLen
  let kOut := xorPad key 0x5c blockLen
  Hbytes (kOut ++ Hbytes (kIn ++ m))

/-- The two pad constants are distinct (a sanity pin: HMAC's two passes use genuinely different
keys, the property the dual-PRF assumption needs). -/
theorem hmac_pads_distinct : (0x36 : Byte) ≠ (0x5c : Byte) := by decide

/-- Unfolding lemma exposing the inner/outer two-pass structure of `hmacSpec`. -/
theorem hmacSpec_eq (Hbytes : List Byte → List Byte) (blockLen : Nat) (key m : List Byte) :
    hmacSpec Hbytes blockLen key m =
      Hbytes (xorPad key 0x5c blockLen ++ Hbytes (xorPad key 0x36 blockLen ++ m)) := rfl

end HmacPrf
