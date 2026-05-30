/-
  Demo 4 (message authentication) — part 2: UF-CMA security of the canonical PRF-based MAC,
  by a reduction to PRF security.

  We build, from any UF-CMA forger against the MAC, a PRF distinguisher: it runs the forger,
  answering tag queries with the PRF oracle (logging them), then checks the forged tag by one
  more oracle query. Under the *real* PRF the distinguisher reproduces the UF-CMA game exactly;
  under a *random function* a forgery on a fresh message only succeeds by guessing a uniformly
  random tag. Hence `UF_CMA_Advantage ≤ prfAdvantage(reduction) + (forgery-vs-random-function)`.
-/
import Demos.AuthChannel.Mac

open Aeneas Std Result OracleComp OracleSpec ENNReal MacAlg PRFScheme

namespace AuthMac

variable {K M : Type} [DecidableEq M]

/- The reduction's oracle handlers forward `unifSpec` queries to the ambient PRF-game oracle,
and forward `M →ₒ Tag` (tag) queries while logging the queried message — exactly the shape of
`MacAlg.UF_CMA_Exp`'s simulation, but with the tag oracle forwarded to the ambient function
oracle (which is `F_k` in the real world, a random function in the ideal world). -/

/-- The reduction's simulation oracle, written inline: forward `unifSpec` queries to the ambient
PRF-game oracle (no log), and forward tag queries to the ambient function oracle while logging the
queried message — exactly the `MacAlg.UF_CMA_Exp` simulation, with the tag oracle forwarded. -/
noncomputable def fwdLogImpl :
    QueryImpl (unifSpec + (M →ₒ Tag))
      (WriterT (QueryLog (M →ₒ Tag)) (OracleComp (unifSpec + (M →ₒ Tag)))) :=
  fun x => match x with
    | Sum.inl q => liftM ((unifSpec + (M →ₒ Tag)).query (Sum.inl q))
    | Sum.inr msg => do
        let t ← liftM ((unifSpec + (M →ₒ Tag)).query (Sum.inr msg))
        tell [⟨msg, t⟩]
        pure t

/-- The PRF distinguisher derived from a MAC UF-CMA forger: run the forger with the logging
forward oracle, then query the function oracle at the forged message and accept iff the message
was unqueried and the recomputed tag matches the forged tag. -/
noncomputable def reduction (prf : PRFScheme K M Tag)
    (A : (macAlg prf).UF_CMA_Adversary) : PRFScheme.PRFAdversary M Tag :=
  (do
    let ((msg, τ), log) ← (simulateQ fwdLogImpl A.main).run
    let t ← ((unifSpec + (M →ₒ Tag)).query (Sum.inr msg) :
      OracleComp (unifSpec + (M →ₒ Tag)) Tag)
    return !log.wasQueried msg && verifyB t τ :
      OracleComp (unifSpec + (M →ₒ Tag)) Bool)

/-- The simulation oracle `MacAlg.UF_CMA_Exp` uses for the MAC game (with `spec = unifSpec`):
forward `unifSpec` to the ambient `ProbComp`, and tag queries through the MAC's tagging oracle
(which logs and runs `tag k = F_k`). -/
noncomputable def ufImpl (prf : PRFScheme K M Tag) (k : K) :
    QueryImpl (unifSpec + (M →ₒ Tag)) (WriterT (QueryLog (M →ₒ Tag)) ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (WriterT (QueryLog (M →ₒ Tag)) ProbComp) +
    (macAlg prf).taggingOracle k

/-- **Real-world correspondence, inductive core.** Simulating the forger through the reduction's
forwarding oracle and then through the real PRF is the same, value-and-log-by-value-and-log, as
simulating it directly through the MAC game's oracle with the tag oracle set to `F_k`. -/
theorem simulateQ_prfReal_fwdLog (prf : PRFScheme K M Tag) (k : K)
    {α : Type} (oa : OracleComp (unifSpec + (M →ₒ Tag)) α) :
    simulateQ (prf.prfRealQueryImpl k) ((simulateQ fwdLogImpl oa).run) =
      (simulateQ (ufImpl prf k) oa).run := by
  induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t f ih =>
    -- Open both sides; the RHS `simulateQ (ufImpl …) (query_bind)` distributes by the `@[simp]`
    -- `simulateQ_bind`, but the LHS outer `simulateQ` over the `WriterT.run`-derived bind does
    -- not match the pretty-printed `do`. A `change` re-exposes the explicit `_ >>= _`, after which
    -- `simulateQ_bind`/`simulateQ_map` fire, the per-oracle head equality is definitional (`rfl`),
    -- and the tail closes by `ih`.
    cases t with
    | inl q =>
      simp only [simulateQ_bind, WriterT.run_bind', simulateQ_spec_query]
      change simulateQ (prf.prfRealQueryImpl k)
          ((fwdLogImpl (Sum.inl q)).run >>= fun x =>
            (Prod.map id fun x_1 => x.2 ++ x_1) <$> (simulateQ fwdLogImpl (f x.1)).run) = _
      simp only [simulateQ_bind, simulateQ_map]
      have head : simulateQ (prf.prfRealQueryImpl k) (fwdLogImpl (Sum.inl q)).run
          = (ufImpl prf k (Sum.inl q)).run := rfl
      rw [head]; refine bind_congr fun x => ?_; rw [ih x.1]
    | inr msg =>
      simp only [simulateQ_bind, WriterT.run_bind', simulateQ_spec_query]
      change simulateQ (prf.prfRealQueryImpl k)
          ((fwdLogImpl (Sum.inr msg)).run >>= fun x =>
            (Prod.map id fun x_1 => x.2 ++ x_1) <$> (simulateQ fwdLogImpl (f x.1)).run) = _
      simp only [simulateQ_bind, simulateQ_map]
      have head : simulateQ (prf.prfRealQueryImpl k) (fwdLogImpl (Sum.inr msg)).run
          = (ufImpl prf k (Sum.inr msg)).run := rfl
      rw [head]; refine bind_congr fun x => ?_; rw [ih x.1]

/-- **Step A — real-world correspondence.** Under the real PRF, the distinguisher built by
`reduction` reproduces the UF-CMA game exactly: its acceptance probability equals the MAC's
UF-CMA advantage. -/
theorem prfRealExp_reduction_eq (prf : PRFScheme K M Tag)
    (A : (macAlg prf).UF_CMA_Adversary) :
    Pr[= true | prf.prfRealExp (reduction prf A)] =
      (macAlg prf).UF_CMA_Advantage ProbCompRuntime.probComp A := by
  have hbridge : ∀ X : ProbComp Bool,
      Pr[= true | ProbCompRuntime.probComp.evalDist X] = Pr[= true | X] := fun _ => rfl
  unfold UF_CMA_Advantage
  rw [MacAlg.UF_CMA_Exp, hbridge]
  congr 1
  unfold PRFScheme.prfRealExp reduction
  refine bind_congr (m := ProbComp) fun k => ?_
  dsimp only
  change simulateQ (prf.prfRealQueryImpl k)
      ((simulateQ fwdLogImpl A.main).run >>= fun __discr =>
        ((liftM ((unifSpec + (M →ₒ Tag)).query (Sum.inr __discr.1.1)) :
            OracleComp (unifSpec + (M →ₒ Tag)) Tag) >>= fun t =>
          pure (!__discr.2.wasQueried __discr.1.1 && verifyB t __discr.1.2))) = _
  rw [simulateQ_bind, simulateQ_prfReal_fwdLog]
  refine bind_congr fun x => ?_
  have hq : simulateQ (prf.prfRealQueryImpl k)
      (liftM ((unifSpec + (M →ₒ Tag)).query (Sum.inr x.1.1)) :
        OracleComp (unifSpec + (M →ₒ Tag)) Tag) = (pure (prf.eval k x.1.1) : ProbComp Tag) := rfl
  change simulateQ (prf.prfRealQueryImpl k)
      ((liftM ((unifSpec + (M →ₒ Tag)).query (Sum.inr x.1.1)) :
          OracleComp (unifSpec + (M →ₒ Tag)) Tag) >>= fun t =>
        pure (!x.2.wasQueried x.1.1 && verifyB t x.1.2)) = _
  rw [simulateQ_bind, hq, pure_bind, macAlg_verify, pure_bind, simulateQ_pure]

/-- **Step B — combination bound.** The MAC's UF-CMA advantage is bounded by the PRF
distinguishing advantage of the reduction plus the success probability of the same reduction
against a random function. This is the honest PRF-reduction headline (the analogue of
`authExp_le_prfAdvantage_add_authRF`). -/
theorem macUF_le_prfAdvantage_add_RF (prf : PRFScheme K M Tag)
    (A : (macAlg prf).UF_CMA_Adversary) :
    ((macAlg prf).UF_CMA_Advantage ProbCompRuntime.probComp A).toReal ≤
      prf.prfAdvantage (reduction prf A) +
      (Pr[= true | PRFScheme.prfIdealExp (reduction prf A)]).toReal := by
  rw [← prfRealExp_reduction_eq]
  unfold PRFScheme.prfAdvantage
  set a := (Pr[= true | prf.prfRealExp (reduction prf A)]).toReal
  set b := (Pr[= true | PRFScheme.prfIdealExp (reduction prf A)]).toReal
  have : a - b ≤ |a - b| := le_abs_self _
  linarith

/-! ## Step C — the random-function forgery bound `1/|Tag|` -/

section RF

open scoped Classical

/-- Abbreviation for the ideal-world simulation handler of the reduction. -/
noncomputable abbrev idealImpl : QueryImpl (unifSpec + (M →ₒ Tag))
    (StateT ((M →ₒ Tag).QueryCache) ProbComp) :=
  PRFScheme.prfIdealQueryImpl (D := M) (R := Tag)

/-- **Cache–log invariant.** Running `A.main` through the reduction's logging forward oracle,
then through the ideal-world random oracle starting from cache `c₀`, only ever caches messages
that were either already cached or have been logged. In particular (with `c₀ = ∅`, empty log),
an unlogged message stays uncached. -/
theorem fwdLog_cache_log_inv {γ : Type}
    (oa : OracleComp (unifSpec + (M →ₒ Tag)) γ) :
    ∀ (c₀ : (M →ₒ Tag).QueryCache) (log₀ : QueryLog (M →ₒ Tag)),
    (∀ m : M, c₀ m ≠ none → (log₀.wasQueried m = true)) →
    ∀ z ∈ support
      ((simulateQ idealImpl
        ((fun p => (p.1, log₀ ++ p.2)) <$> (simulateQ fwdLogImpl oa).run)).run c₀),
    ∀ m : M, z.2 m ≠ none → z.1.2.wasQueried m = true := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro c₀ log₀ hinit z hz m hm
    simp only [simulateQ_pure, WriterT.run_pure', map_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    simpa using hinit m hm
  | query_bind t f ih =>
    intro c₀ log₀ hinit z hz m hm
    simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind', map_bind, Functor.map_map,
      simulateQ_map, StateT.run_bind, StateT.run_map] at hz
    rw [mem_support_bind_iff] at hz
    obtain ⟨x, hx, hz⟩ := hz
    -- Head step invariant: the head query caches at most the message it also logs.
    have hhead : ∀ mm : M, x.2 mm ≠ none → (log₀ ++ x.1.2).wasQueried mm = true := by
      cases t with
      | inl q =>
        have key : (simulateQ idealImpl (fwdLogImpl (Sum.inl q)).run).run c₀ =
            ((unifSpec.query q : ProbComp _) >>= fun u =>
              pure ((u, (∅ : QueryLog (M →ₒ Tag))), c₀)) := by
          show (simulateQ idealImpl ((·, (∅ : QueryLog (M →ₒ Tag))) <$>
              (liftM ((unifSpec + (M →ₒ Tag)).query (Sum.inl q)) :
                OracleComp (unifSpec + (M →ₒ Tag)) _))).run c₀ = _
          rw [simulateQ_map, simulateQ_spec_query]
          show ((·, (∅ : QueryLog (M →ₒ Tag))) <$>
            (liftM (unifSpec.query q : ProbComp _) :
              StateT ((M →ₒ Tag).QueryCache) ProbComp _)).run c₀ = _
          simp [StateT.run_monadLift, map_eq_bind_pure_comp]
        rw [key] at hx
        obtain ⟨u, _, hu⟩ := (mem_support_bind_iff _ _ _).1 hx
        have hxeq : x = ((u, ∅), c₀) := by simpa using hu
        subst hxeq
        intro mm hmm
        simpa using hinit mm hmm
      | inr msg =>
        have hq : simulateQ idealImpl
            (liftM ((unifSpec + (M →ₒ Tag)).query (Sum.inr msg)) :
              OracleComp (unifSpec + (M →ₒ Tag)) Tag) =
            OracleSpec.randomOracle (spec := (M →ₒ Tag)) msg :=
          simulateQ_spec_query _ (Sum.inr msg)
        have key : (simulateQ idealImpl (fwdLogImpl (Sum.inr msg)).run).run c₀ =
            ((OracleSpec.randomOracle (spec := (M →ₒ Tag)) msg).run c₀ >>= fun p =>
              pure ((p.1, ([⟨msg, p.1⟩] : QueryLog (M →ₒ Tag))), p.2)) := by
          show (simulateQ idealImpl ((liftM ((unifSpec + (M →ₒ Tag)).query (Sum.inr msg)) :
              OracleComp (unifSpec + (M →ₒ Tag)) Tag) >>= fun t =>
                pure (t, ([⟨msg, t⟩] : QueryLog (M →ₒ Tag))))).run c₀ = _
          rw [simulateQ_bind, hq]
          simp only [simulateQ_pure, StateT.run_bind]
          rfl
        have hcache : ∀ p ∈ support ((OracleSpec.randomOracle (spec := (M →ₒ Tag)) msg).run c₀),
            ∀ mm : M, mm ≠ msg → p.2 mm = c₀ mm := by
          intro p hp mm hmm
          cases hc : c₀ msg with
          | some u =>
            rw [QueryImpl.withCaching_run_some _ hc] at hp
            simp only [support_pure, Set.mem_singleton_iff] at hp
            rw [hp]
          | none =>
            rw [QueryImpl.withCaching_run_none _ hc] at hp
            simp only [support_map, Set.mem_image] at hp
            obtain ⟨v, _, rfl⟩ := hp
            exact QueryCache.cacheQuery_of_ne _ _ hmm
        rw [key] at hx
        obtain ⟨p, hp, hxeq⟩ := (mem_support_bind_iff _ _ _).1 hx
        have hxeq' : x = ((p.1, ([⟨msg, p.1⟩] : QueryLog (M →ₒ Tag))), p.2) := by
          simpa using hxeq
        subst hxeq'
        intro mm hmm
        by_cases hmsg : mm = msg
        · subst hmsg
          simp [QueryLog.wasQueried_eq_decide_mem_map_fst]
        · have hcc : (p.2) mm = c₀ mm := hcache p hp mm hmsg
          have hc₀ : c₀ mm ≠ none := by rwa [hcc] at hmm
          have hlog : log₀.wasQueried mm = true := hinit mm hc₀
          simp only [QueryLog.wasQueried_eq_decide_mem_map_fst, List.map_append,
            List.mem_append, decide_eq_true_eq]
          left
          simpa [QueryLog.wasQueried_eq_decide_mem_map_fst] using hlog
    -- The tail outcome `z` matches the IH form with accumulated log `log₀ ++ x.1.2`.
    rw [support_map, Set.mem_image] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    have hih := ih x.1.1 x.2 (log₀ ++ x.1.2) hhead
      ((p.1.1, (log₀ ++ x.1.2) ++ p.1.2), p.2) ?_ m hm
    · simpa [List.append_assoc] using hih
    · -- `p` lies in the IH's support set after rewriting the accumulated map.
      simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image]
      exact ⟨p, hp, by simp [List.append_assoc]⟩

/-- **Fresh-point guessing bound.** The final verification query of the reduction, run against the
ideal random oracle at a message that is uncached whenever the gate `b` is on, accepts with
probability at most `1/|Tag|`: an uncached query samples the tag uniformly, independently of the
forged tag `τ`, so the chance it matches is exactly `1/|Tag|`. -/
theorem fresh_query_bound (msg : M) (τ : Tag) (b : Bool)
    (cache' : (M →ₒ Tag).QueryCache) (hfresh : b = true → cache' msg = none) :
    Pr[= true |
      (simulateQ idealImpl
        ((liftM ((unifSpec + (M →ₒ Tag)).query (Sum.inr msg)) :
            OracleComp (unifSpec + (M →ₒ Tag)) Tag) >>= fun t =>
          pure (b && verifyB t τ))).run' cache'] ≤ (Fintype.card Tag : ℝ≥0∞)⁻¹ := by
  have hq : simulateQ idealImpl
      (liftM ((unifSpec + (M →ₒ Tag)).query (Sum.inr msg)) :
        OracleComp (unifSpec + (M →ₒ Tag)) Tag) =
      OracleSpec.randomOracle (spec := (M →ₒ Tag)) msg :=
    simulateQ_spec_query _ (Sum.inr msg)
  have hred : (simulateQ idealImpl
      ((liftM ((unifSpec + (M →ₒ Tag)).query (Sum.inr msg)) :
          OracleComp (unifSpec + (M →ₒ Tag)) Tag) >>= fun t =>
        pure (b && verifyB t τ))).run' cache' =
      (OracleSpec.randomOracle (spec := (M →ₒ Tag)) msg).run' cache' >>= fun t =>
        pure (b && verifyB t τ) := by
    rw [simulateQ_bind, hq]
    simp only [simulateQ_pure]
    rw [StateT.run'_eq, StateT.run'_eq, StateT.run_bind, map_bind]
    simp [StateT.run_pure]
  rw [hred]
  cases b with
  | false =>
    simp only [Bool.false_and]
    rw [show (fun _ : Tag => pure (false : Bool) : Tag → ProbComp Bool) =
      pure ∘ fun _ : Tag => (false : Bool) from rfl, ← probEvent_eq_eq_probOutput,
      probEvent_bind_pure_comp]
    rw [probEvent_eq_zero (fun x _ h => absurd h (by simp))]
    exact zero_le _
  | true =>
    have hfree : cache' msg = none := hfresh rfl
    -- Reduce to the random-oracle output distribution and bound by `Pr[t = τ]`.
    have hbound : Pr[= true |
        (OracleSpec.randomOracle (spec := (M →ₒ Tag)) msg).run' cache' >>= fun t =>
          pure (true && verifyB t τ)] ≤
        Pr[= τ | (OracleSpec.randomOracle (spec := (M →ₒ Tag)) msg).run' cache'] := by
      rw [← probEvent_eq_eq_probOutput,
        show (fun t => pure (true && verifyB t τ) :
            Tag → ProbComp Bool) = pure ∘ fun t => true && verifyB t τ from rfl,
        probEvent_bind_pure_comp, ← probEvent_eq_eq_probOutput]
      refine probEvent_mono ?_
      intro t _ ht
      simp only [Function.comp_apply] at ht
      rw [Bool.true_and, verifyB_eq_true_iff] at ht
      exact ht
    refine hbound.trans ?_
    -- A fresh random-oracle query is uniform, so `Pr[= τ] = 1/|Tag|`.
    rw [StateT.run'_eq, QueryImpl.withCaching_run_none _ hfree, Functor.map_map,
      show (fun a => (a, cache'.cacheQuery msg a).1 : Tag → Tag) = (id : Tag → Tag) from rfl,
      id_map, show uniformSampleImpl msg = ($ᵗ Tag : ProbComp Tag) from rfl,
      probOutput_uniformSample]

set_option maxRecDepth 8000 in
/-- **Step C — random-function forgery bound.** Against a *random function* (the ideal world of
the PRF reduction), the distinguisher built by `reduction` accepts with probability at most
`1/|Tag|`: a forgery on an unqueried message can only succeed by guessing a uniformly random tag.
This is the analogue of `authIdealExp_eq_zero`, but with the nonzero `1/|Tag|` guessing term that
the lazy random oracle genuinely contributes. -/
theorem reduction_RF_le (prf : PRFScheme K M Tag)
    (A : (macAlg prf).UF_CMA_Adversary) :
    (Pr[= true | PRFScheme.prfIdealExp (reduction prf A)]).toReal ≤ (Fintype.card Tag : ℝ)⁻¹ := by
  -- It suffices to prove the `ℝ≥0∞` bound and then transport along `toReal`.
  suffices h : Pr[= true | PRFScheme.prfIdealExp (reduction prf A)] ≤
      (Fintype.card Tag : ℝ≥0∞)⁻¹ by
    haveI : Nonempty Tag := inferInstanceAs (Nonempty (List.Vector Std.U8 32))
    rw [show ((Fintype.card Tag : ℝ)⁻¹) = ((Fintype.card Tag : ℝ≥0∞)⁻¹).toReal from by
      rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]]
    exact ENNReal.toReal_mono (ENNReal.inv_ne_top.mpr (by exact_mod_cast Fintype.card_ne_zero)) h
  -- Decompose the ideal experiment: run `A.main` (logging + RO), then the final verify query.
  rw [PRFScheme.prfIdealExp]
  show Pr[= true |
      (simulateQ idealImpl (reduction prf A)).run' ∅] ≤ _
  unfold reduction
  rw [show (do
        let ((msg, τ), log) ← (simulateQ fwdLogImpl A.main).run
        let t ← ((unifSpec + (M →ₒ Tag)).query (Sum.inr msg) :
          OracleComp (unifSpec + (M →ₒ Tag)) Tag)
        (pure (!log.wasQueried msg && verifyB t τ) :
          OracleComp (unifSpec + (M →ₒ Tag)) Bool)) =
      ((simulateQ fwdLogImpl A.main).run >>= fun w =>
        (liftM ((unifSpec + (M →ₒ Tag)).query (Sum.inr w.1.1)) :
            OracleComp (unifSpec + (M →ₒ Tag)) Tag) >>= fun t =>
          pure (!w.2.wasQueried w.1.1 && verifyB t w.1.2)) from rfl]
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind, probOutput_bind_eq_tsum]
  -- Each first-part outcome contributes at most `1/|Tag|`; sum is bounded by `1/|Tag|`.
  have hterm : ∀ w : ((M × Tag) × QueryLog (M →ₒ Tag)) × (M →ₒ Tag).QueryCache,
      w ∈ support ((simulateQ idealImpl (simulateQ fwdLogImpl A.main).run).run ∅) →
        Pr[= true | Prod.fst <$> ((simulateQ idealImpl
            ((liftM ((unifSpec + (M →ₒ Tag)).query (Sum.inr w.1.1.1)) :
                OracleComp (unifSpec + (M →ₒ Tag)) Tag) >>= fun t =>
              pure (!w.1.2.wasQueried w.1.1.1 && verifyB t w.1.1.2))).run w.2)] ≤
          (Fintype.card Tag : ℝ≥0∞)⁻¹ := by
    intro w hw
    -- The cache–log invariant from running `A.main`.
    have hinv := fwdLog_cache_log_inv (M := M) A.main ∅ ∅
      (by intro m hm; simp at hm) w (by simpa using hw)
    have hfresh : (!w.1.2.wasQueried w.1.1.1) = true → w.2 w.1.1.1 = none := by
      intro hb
      by_contra hc
      have := hinv w.1.1.1 hc
      simp [this] at hb
    have hb := fresh_query_bound (M := M) w.1.1.1 w.1.1.2 (!w.1.2.wasQueried w.1.1.1) w.2 hfresh
    simpa [StateT.run'_eq] using hb
  calc ∑' w, Pr[= w | (simulateQ idealImpl (simulateQ fwdLogImpl A.main).run).run ∅] *
        Pr[= true | Prod.fst <$> ((simulateQ idealImpl
            ((liftM ((unifSpec + (M →ₒ Tag)).query (Sum.inr w.1.1.1)) :
                OracleComp (unifSpec + (M →ₒ Tag)) Tag) >>= fun t =>
              pure (!w.1.2.wasQueried w.1.1.1 && verifyB t w.1.1.2))).run w.2)]
      ≤ ∑' w, Pr[= w | (simulateQ idealImpl (simulateQ fwdLogImpl A.main).run).run ∅] *
          (Fintype.card Tag : ℝ≥0∞)⁻¹ := by
        refine ENNReal.tsum_le_tsum fun w => ?_
        by_cases hw : w ∈ support ((simulateQ idealImpl (simulateQ fwdLogImpl A.main).run).run ∅)
        · exact mul_le_mul' le_rfl (hterm w hw)
        · rw [probOutput_eq_zero_of_not_mem_support hw]; simp
    _ = (∑' w, Pr[= w | (simulateQ idealImpl (simulateQ fwdLogImpl A.main).run).run ∅]) *
          (Fintype.card Tag : ℝ≥0∞)⁻¹ := by rw [ENNReal.tsum_mul_right]
    _ ≤ 1 * (Fintype.card Tag : ℝ≥0∞)⁻¹ := by gcongr; exact tsum_probOutput_le_one
    _ = (Fintype.card Tag : ℝ≥0∞)⁻¹ := one_mul _

/-- **Headline UF-CMA bound.** The MAC's UF-CMA advantage is bounded by the PRF distinguishing
advantage of the reduction plus the random-function guessing term `1/|Tag| = 2^-256`. This is the
honest PRF-based MAC reduction, with the ideal-world forgery probability discharged by
`reduction_RF_le`. -/
theorem macUF_le (prf : PRFScheme K M Tag) (A : (macAlg prf).UF_CMA_Adversary) :
    ((macAlg prf).UF_CMA_Advantage ProbCompRuntime.probComp A).toReal ≤
      prf.prfAdvantage (reduction prf A) + (Fintype.card Tag : ℝ)⁻¹ := by
  have h1 := macUF_le_prfAdvantage_add_RF prf A
  have h2 := reduction_RF_le prf A
  linarith

end RF

end AuthMac
