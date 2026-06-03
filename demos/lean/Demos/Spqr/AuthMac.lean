/-
  SPQR Ratcheted-Authenticator MAC — UF-CMA over the extracted constant-time comparator.

  SPQR's authenticator (`src/authenticator.rs`) authenticates each epoch's header/ciphertext
  with an HMAC-SHA256 tag and verifies it with a *constant-time* comparator `compare` (the
  byte-OR-fold then `inz` bit-twiddle, both extracted Rust). This is the libsignal "deterministic
  canonical MAC" shape `tag(k,m) = F_k(m)`, `verify(k,m,t) = (F_k(m) == t)`, with `F` the keyed
  HMAC modelled abstractly as a VCVio `PRFScheme`, EXACTLY as Demo 4 (`Demos/AuthChannel/Mac.lean`)
  — the only difference is the *verify* primitive: here it is SPQR's `authenticator::compare`
  (0 = accept, nonzero = reject — the inverse polarity of `mac.verify`'s Bool), not `mac.verify`.

  We REUSE VCVio's TRUSTED `MacAlg` / `MacAlg.UF_CMA` game verbatim (no new game is defined). The
  contribution here is the construction + the verify-adequacy glue that lets the SPQR comparator
  drive the trusted game:
    * `compare_accept`  — equal tags ⇒ `compare = 0` (the accept direction; pairs with the
                          already-landed `compare_reject`, the reject direction).
    * `compareB_eq_true_iff` — the Boolean view of `compare` decides tag equality (value adequacy).
    * `spqrMacAlg`      — the canonical PRF-MAC packaged as `MacAlg ProbComp M K Tag` over the
                          extracted comparator.
    * `spqrMacAlg_perfectlyComplete` — honest tags always verify (perfect completeness).

  The full UF-CMA *bound* (`advantage ≤ prfAdvantage + 1/|Tag|`) is Demo 4's chain
  (`Demos/AuthChannel/SufCma.lean`) over the *same* `MacAlg` shape; banking the instance +
  completeness/adequacy here is the SPQR-side glue (per the task's "bank the MacAlg instance +
  perfect-completeness/verify-adequacy glue even if the full UF-CMA bound isn't reached").
-/
import Demos.Spqr.Authenticator
import Demos.AuthChannel.Mac
import VCVio.CryptoFoundations.MacAlg
import VCVio.CryptoFoundations.PRF
import VCVio.OracleComp.Constructions.SampleableType

open Aeneas Std Result

namespace Spqr.AuthMac

/-- The SPQR authenticator tag space: the 32-byte MAC (`authenticator::MACSIZE = 32`), which is
*definitionally* Demo 4's `AuthMac.Tag` (`Std.Array Std.U8 32#usize`), so we inherit its
`Fintype`/`SampleableType`/`DecidableEq` instances and reuse `AuthMac.tag_eq_iff`. -/
abbrev Tag := Std.Array Std.U8 32#usize

/-! ### Accept direction: equal tags ⇒ `compare` returns 0 -/

/-- **The MAC comparator accepts genuine tags.** On equal inputs `compare` returns `0` (accept):
the OR-accumulator never changes (`compare_loop_refl`, starting from `0`), and `inz 0 = 0`
(`inz_spec`). This is the accept counterpart of the already-landed `Spqr.Auth.compare_reject`. -/
theorem compare_accept (a : Tag) :
    authenticator.compare a a ⦃ res => res = 0#u8 ⦄ := by
  unfold authenticator.compare
  apply Aeneas.Std.WP.spec_bind
    (Spqr.Auth.compare_loop_refl a 0#u8 0#usize (by scalar_tac))
  intro r hr
  -- `r = 0`, so `inz r = inz 0 = 0`.
  apply Aeneas.Std.WP.spec_mono (Spqr.Auth.inz_spec r)
  intro res hres
  have hr0 : r.bv = 0#8 := by rw [hr]; rfl
  rw [if_pos hr0] at hres
  apply Aeneas.Std.UScalar.eq_of_val_eq
  show res.bv.toNat = (0#u8).bv.toNat; rw [hres]; rfl

/-! ### Boolean view of the comparator decides tag equality -/

/-- Total Boolean view of the SPQR comparator: `true` (accept) iff `compare a t` returns `0`.
The `compare` computation is always `ok` (its loop + `inz` are total), so the non-`ok` branch is
unreachable. -/
def compareB (a t : Tag) : Bool :=
  match authenticator.compare a t with
  | .ok r => r = 0#u8
  | _ => false

/-- **The Boolean comparator decides tag equality.** `compareB a t = true ↔ a = t`:
- (`←`) equal tags accept, by `compare_accept`;
- (`→`) if `a ≠ t` they differ at some byte `k < 32` (`AuthMac.tag_eq_iff`), so `compare` returns
  nonzero (`Spqr.Auth.compare_reject`) — a forged/altered tag is rejected.
This is the value-adequacy bridge the trusted MAC game's verify rests on. -/
@[simp] theorem compareB_eq_true_iff (a t : Tag) : compareB a t = true ↔ a = t := by
  constructor
  · -- accept ⇒ equal: contrapositive via compare_reject
    intro hacc
    by_contra hne
    -- a ≠ t ⇒ ∃ k < 32, a[k]! ≠ t[k]!
    rw [AuthMac.tag_eq_iff] at hne
    simp only [not_forall] at hne
    obtain ⟨k, hk, hdiff⟩ := hne
    obtain ⟨r, hr, hrne⟩ := WP.spec_imp_exists (Spqr.Auth.compare_reject a t k hk hdiff)
    simp only [compareB, hr] at hacc
    exact hrne (by simpa using hacc)
  · rintro rfl
    obtain ⟨r, hr, hr0⟩ := WP.spec_imp_exists (compare_accept a)
    simp only [compareB, hr, hr0, decide_eq_true_eq]

/-! ### The canonical PRF-based SPQR MAC, instantiated against VCVio's `MacAlg` -/

variable {K M : Type}

/-- The **canonical deterministic SPQR MAC** built from a PRF `F`: `tag k m = F_k(m)`, and
`verify` runs the extracted constant-time `compare` on the recomputed tag (accept iff it returns
`0`). Computations live in `ProbComp = OracleComp unifSpec` (so `keygen` is the PRF's key
generation directly). Identical shape to Demo 4's `AuthMac.macAlg`; the verify primitive is the
SPQR comparator. -/
def spqrMacAlg (prf : PRFScheme K M Tag) : MacAlg ProbComp M K Tag where
  keygen := prf.keygen
  tag k m := pure (prf.eval k m)
  verify k m t := pure (compareB (prf.eval k m) t)

@[simp] theorem spqrMacAlg_keygen (prf : PRFScheme K M Tag) :
    (spqrMacAlg prf).keygen = prf.keygen := rfl

@[simp] theorem spqrMacAlg_tag (prf : PRFScheme K M Tag) (k : K) (m : M) :
    (spqrMacAlg prf).tag k m = pure (prf.eval k m) := rfl

@[simp] theorem spqrMacAlg_verify (prf : PRFScheme K M Tag) (k : K) (m : M) (t : Tag) :
    (spqrMacAlg prf).verify k m t = pure (compareB (prf.eval k m) t) := rfl

/-- **Perfect completeness.** Honestly generated tags always verify — because the extracted SPQR
comparator accepts equal inputs (`compareB_eq_true_iff`) and `F_k(m) = F_k(m)`. Stated for
uniform-key PRFs (the standard case; makes `keygen` total), exactly as Demo 4. -/
theorem spqrMacAlg_perfectlyComplete [SampleableType K] (prf : PRFScheme K M Tag)
    (hkey : prf.UniformKey) :
    (spqrMacAlg prf).PerfectlyComplete ProbCompRuntime.probComp := by
  intro msg
  have hv : ∀ k : K, compareB (prf.eval k msg) (prf.eval k msg) = true :=
    fun k => (compareB_eq_true_iff _ _).mpr rfl
  rw [PRFScheme.UniformKey] at hkey
  have hbridge : ∀ X : ProbComp Bool,
      Pr[= true | ProbCompRuntime.probComp.evalDist X] = Pr[= true | X] := fun _ => rfl
  simp only [hbridge, spqrMacAlg, pure_bind, hv, hkey]
  rw [probOutput_bind_const, probFailure_uniformSample]
  simp

end Spqr.AuthMac
