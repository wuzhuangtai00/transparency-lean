import TransparencyLean.Information.FiniteSupport
import TransparencyLean.Submodular.Transparency
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Arbitrary measurable signal spaces, represented by a Bayes-plausible
posterior process and selected contract/equilibrium. Feasibility is required
only almost everywhere. Outcome measurability suffices; integrability follows
from the compact feasible graph and is not an extra payoff assumption. -/

namespace TransparencyLean

open scoped BigOperators
open Set MeasureTheory

noncomputable section

variable {Ω Agent : Type*} [Fintype Ω] [Fintype Agent] [DecidableEq Agent]

structure MeasurableContractScheme (prior : FiniteDist Ω)
    (f : Ω → Finset Agent → ℝ) (c : Agent → ℝ)
    (Signal : Type*) [MeasurableSpace Signal] where
  weights : Measure Signal
  probability : IsProbabilityMeasure weights
  posterior : Signal → FiniteDist Ω
  contract : Signal → Agent → ℝ
  team : Signal → Finset Agent
  feasible : ∀ᵐ s ∂weights, FeasibleContract (contract s)
  equilibrium : ∀ᵐ s ∂weights, IsEquilibrium (posteriorReward (posterior s) f)
    c (contract s) (team s)
  measurable_outcome : AEStronglyMeasurable (fun s => ((posterior s).prob,
    principalUtility (posteriorReward (posterior s) f) (contract s) (team s))) weights
  plausible : ∀ ω, (∫ s, (posterior s).prob ω ∂weights) = prior.prob ω

namespace MeasurableContractScheme

variable {Signal : Type*} [MeasurableSpace Signal]
variable {prior : FiniteDist Ω} {f : Ω → Finset Agent → ℝ} {c : Agent → ℝ}

def outcome (scheme : MeasurableContractScheme prior f c Signal) (s : Signal) : PosteriorPayoff Ω :=
  ((scheme.posterior s).prob,
    principalUtility (posteriorReward (scheme.posterior s) f) (scheme.contract s) (scheme.team s))

def utility (scheme : MeasurableContractScheme prior f c Signal) : ℝ :=
  ∫ s, (scheme.outcome s).2 ∂scheme.weights

theorem ae_outcome_mem (scheme : MeasurableContractScheme prior f c Signal) :
    ∀ᵐ s ∂scheme.weights, scheme.outcome s ∈ feasiblePayoffs f c := by
  filter_upwards [scheme.feasible, scheme.equilibrium] with s hs heq
  exact (mem_feasiblePayoffs_iff f c _).mpr
    ⟨scheme.posterior s, scheme.contract s, scheme.team s, hs, heq, rfl, rfl⟩

theorem outcome_integrable (scheme : MeasurableContractScheme prior f c Signal) :
    Integrable scheme.outcome scheme.weights := by
  letI := scheme.probability
  obtain ⟨M, hM⟩ := (feasiblePayoffs_compact f c).isBounded.exists_norm_le
  exact (integrable_const M).mono' scheme.measurable_outcome
    (scheme.ae_outcome_mem.mono (fun _ h => hM _ h))

theorem integral_outcome (scheme : MeasurableContractScheme prior f c Signal) :
    (∫ s, scheme.outcome s ∂scheme.weights) = (prior.prob, scheme.utility) := by
  apply Prod.ext
  · ext ω
    rw [fst_integral scheme.outcome_integrable]
    have heval := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Ω => ℝ) ω).integral_comp_comm
      scheme.outcome_integrable.fst
    exact heval.symm.trans (scheme.plausible ω)
  · exact snd_integral scheme.outcome_integrable

theorem mean_mem_convexHull (scheme : MeasurableContractScheme prior f c Signal) :
    (prior.prob, scheme.utility) ∈ convexHull ℝ (feasiblePayoffs f c) := by
  letI := scheme.probability
  have h := (convex_convexHull ℝ (feasiblePayoffs f c)).integral_mem
    (feasiblePayoffs_convexHull_compact f c).isClosed
    (scheme.ae_outcome_mem.mono (fun _ h => subset_convexHull ℝ _ h))
    scheme.outcome_integrable
  rwa [scheme.integral_outcome] at h

/-- Exact finite-support reduction: preserves the prior and expected utility.
The output includes contracts and selected equilibria, not only posterior
points, and can be implemented as a randomized kernel by `toKernel`. -/
theorem finite_equivalent (scheme : MeasurableContractScheme prior f c Signal) :
    ∃ finite : ContractScheme prior f c (Fin (supportBound Ω)), finite.utility = scheme.utility :=
  finite_scheme_of_mem_convexHull prior scheme.mean_mem_convexHull

theorem all_or_nothing (scheme : MeasurableContractScheme prior f c Signal)
    (hf : ∀ ω, ValidReward (f ω)) (β : ℝ)
    (hbound : ∀ μ, noDisclosureValue μ f c ≤ β * fullDisclosureValue μ f c) :
    scheme.utility ≤ β * fullDisclosureValue prior f c := by
  obtain ⟨finite, hfinite⟩ := scheme.finite_equivalent
  rw [← hfinite]
  exact finite.all_or_nothing hf β hbound

/-- The 4/3 guarantee for arbitrary measurable public signal spaces in
posterior representation, with no positivity assumption on optimal utility. -/
theorem submodular_four_thirds (scheme : MeasurableContractScheme prior f c Signal)
    (hf : ∀ ω, ValidReward (f ω)) (hmono : ∀ ω, Monotone (f ω))
    (hsub : ∀ ω, Submodular (f ω)) (hc : ∀ i, 0 ≤ c i) :
    scheme.utility ≤ (4 / 3) * fullDisclosureValue prior f c := by
  obtain ⟨finite, hfinite⟩ := scheme.finite_equivalent
  rw [← hfinite]
  exact finite.submodular_four_thirds hf hmono hsub hc

end MeasurableContractScheme

/-- The finite-attainment claim in posterior representation: a single finite
scheme weakly dominates every admissible scheme on every measurable signal
space. No compactness assumption on the signal space is necessary. -/
theorem optimal_finite_for_measurable (prior : FiniteDist Ω) (f : Ω → Finset Agent → ℝ)
    (c : Agent → ℝ) (hc : ∀ i, 0 ≤ c i) :
    ∃ optimal : ContractScheme prior f c (Fin (supportBound Ω)),
      ∀ (Signal : Type*) [MeasurableSpace Signal]
        (scheme : MeasurableContractScheme prior f c Signal), scheme.utility ≤ optimal.utility := by
  obtain ⟨u, hu, hmax⟩ := optimal_payoff_exists prior f c hc
  obtain ⟨optimal, hopt⟩ := finite_scheme_of_mem_convexHull prior hu
  refine ⟨optimal, ?_⟩
  intro Signal _ scheme
  rw [hopt]
  exact hmax _ scheme.mean_mem_convexHull

end

end TransparencyLean
