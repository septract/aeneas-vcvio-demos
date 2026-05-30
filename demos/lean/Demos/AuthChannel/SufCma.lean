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

end AuthMac
