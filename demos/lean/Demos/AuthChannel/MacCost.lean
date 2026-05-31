/-
  Demo 4 (cost adequacy) — the SUF-CMA / UF-CMA PRF reduction is *efficient* relative to the
  forger, in the **query-count** cost measure (`IsTotalQueryBound`, the cost notion native to the
  pure `OracleComp` model — *not* a wall-clock/circuit-time bound).

  The reduction `reduction prf A` runs the forger `A.main` through the logging forward oracle
  `fwdLogImpl` (which forwards every source query 1:1 to the underlying oracle, only additionally
  *writing* a log), then makes exactly one more oracle query (the verification query) before
  returning a Boolean. So if `A.main` makes at most `qA` queries, the reduction makes at most
  `qA + 1` — it adds only `O(1)` oracle overhead, independent of `A`.

  This mirrors Demo 3's `Demos/Ratchet/Cost.lean` (efficiency preservation for the hybrid
  reduction) and the VCVio template `loggingOracle.isTotalQueryBound_run_simulateQ_loggingOracle_iff`:
  Step 1 shows the logging forward oracle preserves query count (the log is discarded under `fst`,
  queries forwarded 1:1, so it is the identity simulation), and Step 2 reads off the `+1` overhead.
-/
import Demos.AuthChannel.SufCma
import VCVio.OracleComp.QueryTracking.QueryBound

open Aeneas Std OracleComp OracleSpec MacAlg PRFScheme

namespace AuthMac

variable {K M : Type} [DecidableEq M]

omit [DecidableEq M] in
/-- **Step 1, inductive core — `fwdLogImpl` forwards queries 1:1.** Discarding the written log
(`Prod.fst`) from the simulation of `oa` through the reduction's logging forward oracle recovers
`oa` itself: every source query is forwarded to the *same* underlying oracle and the only extra
effect is a `WriterT` `tell`, which `fst` drops. This is the identity-simulation fact underlying
the query-count preservation, and is the `fwdLogImpl` analogue of
`loggingOracle.fst_map_run_simulateQ`. Proved by induction on `oa` (template:
`simulateQ_prfReal_fwdLog` in `SufCma.lean`); the `query_bind` head reduces by the `map`-lemmas
and `rfl`, the tail by the IH. -/
theorem fst_map_run_simulateQ_fwdLogImpl {γ : Type}
    (oa : OracleComp (unifSpec + (M →ₒ Tag)) γ) :
    Prod.fst <$> (simulateQ fwdLogImpl oa).run = oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t f ih =>
    cases t with
    | inl q =>
      simp only [simulateQ_bind, WriterT.run_bind', simulateQ_spec_query]
      change Prod.fst <$>
          ((fwdLogImpl (Sum.inl q)).run >>= fun x =>
            (Prod.map id fun x_1 => x.2 ++ x_1) <$> (simulateQ fwdLogImpl (f x.1)).run) = _
      have hhead : (fwdLogImpl (Sum.inl q)).run =
          ((liftM ((unifSpec + (M →ₒ Tag)).query (Sum.inl q)) :
              OracleComp (unifSpec + (M →ₒ Tag)) _) >>= fun u =>
            pure (u, (∅ : QueryLog (M →ₒ Tag)))) := rfl
      rw [hhead]
      simp only [map_bind, bind_pure_comp, Functor.map_map]
      refine (bind_map_left _ _ _).trans ?_
      refine bind_congr fun u => ?_
      simpa using ih u
    | inr msg =>
      simp only [simulateQ_bind, WriterT.run_bind', simulateQ_spec_query]
      change Prod.fst <$>
          ((fwdLogImpl (Sum.inr msg)).run >>= fun x =>
            (Prod.map id fun x_1 => x.2 ++ x_1) <$> (simulateQ fwdLogImpl (f x.1)).run) = _
      have hhead : (fwdLogImpl (Sum.inr msg)).run =
          ((liftM ((unifSpec + (M →ₒ Tag)).query (Sum.inr msg)) :
              OracleComp (unifSpec + (M →ₒ Tag)) Tag) >>= fun t =>
            pure (t, ([⟨msg, t⟩] : QueryLog (M →ₒ Tag)))) := rfl
      rw [hhead]
      simp only [map_bind, bind_pure_comp, Functor.map_map]
      refine (bind_map_left _ _ _).trans ?_
      refine bind_congr fun t => ?_
      simpa using ih t

omit [DecidableEq M] in
/-- **Step 1 — `fwdLogImpl` preserves query count.** Simulating `oa` through the reduction's
logging forward oracle has the *same* total query bound as `oa`: the forwarding is 1:1 and the
log is invisible to the query counter (it lives in the discarded `WriterT` layer). This is the
`fwdLogImpl` analogue of `loggingOracle.isTotalQueryBound_run_simulateQ_loggingOracle_iff`. -/
theorem isTotalQueryBound_run_simulateQ_fwdLogImpl_iff {γ : Type}
    (oa : OracleComp (unifSpec + (M →ₒ Tag)) γ) (n : ℕ) :
    IsTotalQueryBound ((simulateQ fwdLogImpl oa).run) n ↔ IsTotalQueryBound oa n :=
  isQueryBound_iff_of_map_eq (fst_map_run_simulateQ_fwdLogImpl oa) _ _

/-- **Step 2 — the reduction adds exactly one oracle query.** If the UF-CMA/SUF-CMA forger `A`
makes at most `qA` oracle queries (`IsTotalQueryBound A.main qA`), then the PRF distinguisher
`reduction prf A` makes at most `qA + 1`: it runs `A.main` through `fwdLogImpl` (cost `qA`, by
Step 1) and then makes a single verification query (`query (Sum.inr msg)`) before returning a
pure Boolean (cost `1`). So the reduction is efficient — it adds only `O(1)`, `A`-independent
oracle overhead. This is the `AuthMac` analogue of `RatchetCost.reduction_queryBound`. -/
theorem reduction_queryBound (prf : PRFScheme K M Tag)
    (A : (macAlg prf).UF_CMA_Adversary) (qA : ℕ)
    (hA : IsTotalQueryBound A.main qA) :
    IsTotalQueryBound (reduction prf A) (qA + 1) := by
  -- Expose `reduction` as `(simulateQ fwdLogImpl A.main).run >>= tail`.
  have hred : reduction prf A =
      (simulateQ fwdLogImpl A.main).run >>= fun w =>
        (liftM ((unifSpec + (M →ₒ Tag)).query (Sum.inr w.1.1)) :
            OracleComp (unifSpec + (M →ₒ Tag)) Tag) >>= fun t =>
          pure (!w.2.wasQueried w.1.1 && verifyB t w.1.2) := rfl
  rw [hred]
  -- The simulated forger has bound `qA` (Step 1).
  have hpre : IsTotalQueryBound ((simulateQ fwdLogImpl A.main).run) qA :=
    (isTotalQueryBound_run_simulateQ_fwdLogImpl_iff A.main qA).mpr hA
  -- Each verification tail makes exactly one query.
  have htail : ∀ w : (M × Tag) × QueryLog (M →ₒ Tag),
      IsTotalQueryBound
        ((liftM ((unifSpec + (M →ₒ Tag)).query (Sum.inr w.1.1)) :
            OracleComp (unifSpec + (M →ₒ Tag)) Tag) >>= fun t =>
          pure (!w.2.wasQueried w.1.1 && verifyB t w.1.2)) 1 := by
    intro w
    exact isTotalQueryBound_query_bind_iff.mpr ⟨Nat.one_pos, fun t => trivial⟩
  exact isTotalQueryBound_bind hpre htail

/-! ## Step 3 — efficiency preservation for a poly-query forger family.

Packaging Step 2 across a security parameter: a forger *family* whose query count is bounded by a
polynomial `pA` is mapped by `reduction` to a PRF-distinguisher family whose query count is bounded
by the polynomial `pA + 1`. So the reduction stays inside the poly-query efficiency class — the
overhead it adds is a single oracle query, constant in the security parameter. This is the
`AuthMac` analogue of the efficiency-preservation step in `RatchetCost.reduction_queryBound` /
`ratchet_secure_against_polyQuery`, but for the canonical MAC the security bound (`macSUF_le`) is
already concrete, so no asymptotic wrapper is needed — the polynomial statement is the natural
"efficient for a family" packaging. -/
theorem reduction_polyQueryBound (prf : PRFScheme K M Tag)
    (A : ℕ → (macAlg prf).UF_CMA_Adversary) (pA : Polynomial ℕ)
    (hA : ∀ sp, IsTotalQueryBound (A sp).main (pA.eval sp)) :
    ∀ sp, IsTotalQueryBound (reduction prf (A sp)) ((pA + 1).eval sp) := by
  intro sp
  simpa only [Polynomial.eval_add, Polynomial.eval_one] using
    reduction_queryBound prf (A sp) (pA.eval sp) (hA sp)

end AuthMac
