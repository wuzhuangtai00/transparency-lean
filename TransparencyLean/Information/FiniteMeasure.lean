import TransparencyLean.Information.MeasurableSignals

namespace TransparencyLean

open scoped BigOperators ENNReal
open MeasureTheory Set

noncomputable section

namespace FiniteDist

variable {Signal : Type*} [Fintype Signal] [MeasurableSpace Signal]

def toMeasure (p : FiniteDist Signal) : Measure Signal :=
  ∑ s, ENNReal.ofReal (p.prob s) • Measure.dirac s

instance toMeasure_probability (p : FiniteDist Signal) : IsProbabilityMeasure p.toMeasure where
  measure_univ := by
    simp only [toMeasure, Measure.finset_sum_apply, Measure.smul_apply, measure_univ,
      smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => p.nonneg s), p.sum_eq_one]
    simp

theorem toMeasure_singleton [MeasurableSingletonClass Signal] (p : FiniteDist Signal) (s : Signal) :
    p.toMeasure {s} = ENNReal.ofReal (p.prob s) := by
  classical
  simp [toMeasure, Measure.finset_sum_apply, Measure.smul_apply, Measure.dirac_apply,
    Set.indicator_apply, eq_comm]

theorem integral_toMeasure [MeasurableSingletonClass Signal] (p : FiniteDist Signal) (g : Signal → ℝ) :
    (∫ s, g s ∂p.toMeasure) = p.expect g := by
  rw [integral_fintype g Integrable.of_finite]
  simp only [measureReal_def, toMeasure_singleton, ENNReal.toReal_ofReal (p.nonneg _),
    smul_eq_mul, FiniteDist.expect]

end FiniteDist

variable {Ω Agent : Type*} [Fintype Ω] [Fintype Agent] [DecidableEq Agent]
variable {Signal : Type*} [Fintype Signal] [MeasurableSpace Signal] [MeasurableSingletonClass Signal]
variable {prior : FiniteDist Ω} {f : Ω → Finset Agent → ℝ} {c : Agent → ℝ}

def ContractScheme.toMeasurable (scheme : ContractScheme prior f c Signal) :
    MeasurableContractScheme prior f c Signal where
  weights := scheme.information.weights.toMeasure
  probability := inferInstance
  posterior := scheme.information.posterior
  contract := scheme.contract
  team := scheme.team
  feasible := Filter.Eventually.of_forall scheme.feasible
  equilibrium := Filter.Eventually.of_forall scheme.equilibrium
  measurable_outcome := (measurable_of_finite _).aestronglyMeasurable
  plausible ω := by
    rw [FiniteDist.integral_toMeasure]
    exact scheme.information.plausible ω

@[simp] theorem ContractScheme.toMeasurable_utility (scheme : ContractScheme prior f c Signal) :
    scheme.toMeasurable.utility = scheme.utility :=
  scheme.information.weights.integral_toMeasure _

/-- An attained optimum within the measurable model itself, on a finite
signal space. This includes the inclusion of finite schemes into that model. -/
theorem measurable_optimum_attained (prior : FiniteDist Ω) (f : Ω → Finset Agent → ℝ)
    (c : Agent → ℝ) (hc : ∀ i, 0 ≤ c i) :
    ∃ optimal : MeasurableContractScheme prior f c (Fin (supportBound Ω)),
      ∀ (Signal : Type*) [MeasurableSpace Signal]
        (scheme : MeasurableContractScheme prior f c Signal), scheme.utility ≤ optimal.utility := by
  obtain ⟨optimal, hopt⟩ := optimal_finite_for_measurable prior f c hc
  exact ⟨optimal.toMeasurable, fun Signal _ scheme => by
    rw [ContractScheme.toMeasurable_utility]
    exact hopt Signal scheme⟩

end

end TransparencyLean
