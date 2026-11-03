import TransparencyLean.Information.FeasiblePayoffs
import TransparencyLean.Information.FiniteSignals

namespace TransparencyLean

open scoped BigOperators
open Set

noncomputable section

variable {Ω Agent : Type*} [Fintype Ω] [Fintype Agent] [DecidableEq Agent]

/-- A uniform, conservative support bound from ambient Carathéodory dimension.
No sharp support-cardinality claim is needed for the paper's footnote. -/
abbrev supportBound (Ω : Type*) [Fintype Ω] := Module.finrank ℝ (PosteriorPayoff Ω) + 1

omit [Fintype Agent] [DecidableEq Agent] in
theorem supportBound_eq : supportBound Ω = Fintype.card Ω + 2 := by
  simp [supportBound, PosteriorPayoff, Module.finrank_prod,
    Module.finrank_fintype_fun_eq_card, Nat.add_assoc]

theorem ContractScheme.mean_mem_convexHull {Signal : Type*} [Fintype Signal]
    {prior : FiniteDist Ω} {f : Ω → Finset Agent → ℝ} {c : Agent → ℝ}
    (scheme : ContractScheme prior f c Signal) :
    (prior.prob, scheme.utility) ∈ convexHull ℝ (feasiblePayoffs f c) := by
  let z : Signal → PosteriorPayoff Ω := fun s =>
    ((scheme.information.posterior s).prob,
      principalUtility (posteriorReward (scheme.information.posterior s) f)
        (scheme.contract s) (scheme.team s))
  apply mem_convexHull_of_exists_fintype scheme.information.weights.prob z
    scheme.information.weights.nonneg scheme.information.weights.sum_eq_one
  · intro s
    apply (mem_feasiblePayoffs_iff f c (z s)).mpr
    exact ⟨scheme.information.posterior s, scheme.contract s, scheme.team s,
      scheme.feasible s, scheme.equilibrium s, rfl, rfl⟩
  · apply Prod.ext
    · ext ω
      simpa [z, FiniteDist.expect, Prod.fst_sum, Finset.sum_apply] using scheme.information.plausible ω
    · simp [z, ContractScheme.utility, FiniteDist.expect, Prod.snd_sum]

/-- Every posterior-payoff point in the convex hull is implemented by one
finite public contract scheme, with a uniform finite signal type. -/
theorem finite_scheme_of_mem_convexHull (prior : FiniteDist Ω)
    {f : Ω → Finset Agent → ℝ} {c : Agent → ℝ} {u : ℝ}
    (hu : (prior.prob, u) ∈ convexHull ℝ (feasiblePayoffs f c)) :
    ∃ scheme : ContractScheme prior f c (Fin (supportBound Ω)), scheme.utility = u := by
  classical
  obtain ⟨w, z, hw, hsum, hz, hmean⟩ := convexHull_fixed_mixture hu
  choose q α S hα hS hq hv using fun i => (mem_feasiblePayoffs_iff f c (z i)).mp (hz i)
  let weights : FiniteDist (Fin (supportBound Ω)) := ⟨w, hw, hsum⟩
  have hplausible : ∀ ω, weights.expect (fun i => (q i).prob ω) = prior.prob ω := by
    intro ω
    have hh := congrArg (fun x : PosteriorPayoff Ω => x.1 ω) hmean
    simpa [FiniteDist.expect, weights, hq, Prod.fst_sum, Finset.sum_apply] using hh
  let scheme : ContractScheme prior f c (Fin (supportBound Ω)) := {
    information := ⟨weights, q, hplausible⟩
    contract := α
    team := S
    feasible := hα
    equilibrium := hS
  }
  refine ⟨scheme, ?_⟩
  have hh := congrArg Prod.snd hmean
  simpa [ContractScheme.utility, scheme, FiniteDist.expect, weights, hv, Prod.snd_sum] using hh

/-- The principal's objective has a maximizing posterior-payoff point at the
given prior. Compactness is proved from the original incentive constraints. -/
theorem optimal_payoff_exists (prior : FiniteDist Ω) (f : Ω → Finset Agent → ℝ)
    (c : Agent → ℝ) (hc : ∀ i, 0 ≤ c i) :
    ∃ u : ℝ, (prior.prob, u) ∈ convexHull ℝ (feasiblePayoffs f c) ∧
      ∀ v, (prior.prob, v) ∈ convexHull ℝ (feasiblePayoffs f c) → v ≤ u := by
  let C := convexHull ℝ (feasiblePayoffs f c) ∩ {x | x.1 = prior.prob}
  have hC : IsCompact C := (feasiblePayoffs_convexHull_compact f c).inter_right
    (isClosed_eq continuous_fst continuous_const)
  have hbase : (prior.prob, posteriorReward prior f ∅) ∈ feasiblePayoffs f c := by
    apply (mem_feasiblePayoffs_iff f c _).mpr
    exact ⟨prior, fun _ => 0, ∅, zero_feasible,
      empty_zero_equilibrium _ c hc, rfl, principalUtility_zero _ _⟩
  have hne : C.Nonempty :=
    ⟨(prior.prob, posteriorReward prior f ∅), subset_convexHull ℝ _ hbase, rfl⟩
  obtain ⟨x, hx, hmax⟩ := hC.exists_isMaxOn hne continuous_snd.continuousOn
  refine ⟨x.2, ?_, ?_⟩
  · have he : (prior.prob, x.2) = x := Prod.ext hx.2.symm rfl
    rw [he]
    exact hx.1
  · intro v hv
    exact hmax ⟨hv, rfl⟩

/-- An optimal joint scheme exists among all finite public schemes, even
though there was no a priori bound on their finite signal cardinalities. -/
theorem finite_optimal_scheme (prior : FiniteDist Ω) (f : Ω → Finset Agent → ℝ)
    (c : Agent → ℝ) (hc : ∀ i, 0 ≤ c i) :
    ∃ optimal : ContractScheme prior f c (Fin (supportBound Ω)),
      ∀ (Signal : Type*) [Fintype Signal] (scheme : ContractScheme prior f c Signal),
        scheme.utility ≤ optimal.utility := by
  obtain ⟨u, hu, hmax⟩ := optimal_payoff_exists prior f c hc
  obtain ⟨optimal, hopt⟩ := finite_scheme_of_mem_convexHull prior hu
  refine ⟨optimal, ?_⟩
  intro Signal _ scheme
  rw [hopt]
  exact hmax _ scheme.mean_mem_convexHull

end

end TransparencyLean
