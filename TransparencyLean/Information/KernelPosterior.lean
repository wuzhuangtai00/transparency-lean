import TransparencyLean.Information.MeasurableSignals
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! Bayesian posteriors for arbitrary measurable signal kernels with a finite
state space. Radon-Nikodym derivatives construct the posterior; normalization
is proved almost everywhere, and the prior is used on the exceptional null set. -/

namespace TransparencyLean

open scoped BigOperators ENNReal
open MeasureTheory Set

noncomputable section

variable {Ω Signal : Type*} [Fintype Ω] [MeasurableSpace Signal]

structure SignalKernel (Ω Signal : Type*) [MeasurableSpace Signal] where
  law : Ω → Measure Signal
  probability : ∀ ω, IsProbabilityMeasure (law ω)

namespace SignalKernel

instance law_probability (κ : SignalKernel Ω Signal) (ω : Ω) : IsProbabilityMeasure (κ.law ω) :=
  κ.probability ω

def jointComponent (prior : FiniteDist Ω) (κ : SignalKernel Ω Signal) (ω : Ω) : Measure Signal :=
  ENNReal.ofReal (prior.prob ω) • κ.law ω

instance component_finite (prior : FiniteDist Ω) (κ : SignalKernel Ω Signal) (ω : Ω) :
    IsFiniteMeasure (jointComponent prior κ ω) :=
  (κ.law ω).smul_finite ENNReal.ofReal_ne_top

def signalLaw (prior : FiniteDist Ω) (κ : SignalKernel Ω Signal) : Measure Signal :=
  ∑ ω, jointComponent prior κ ω

instance signalLaw_probability (prior : FiniteDist Ω) (κ : SignalKernel Ω Signal) :
    IsProbabilityMeasure (signalLaw prior κ) where
  measure_univ := by
    simp only [signalLaw, Measure.finset_sum_apply, jointComponent,
      Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => prior.nonneg ω), prior.sum_eq_one]
    simp

theorem component_le (prior : FiniteDist Ω) (κ : SignalKernel Ω Signal) (ω : Ω) :
    jointComponent prior κ ω ≤ signalLaw prior κ := by
  apply Measure.le_iff.mpr
  intro A _
  rw [signalLaw, Measure.finset_sum_apply]
  exact Finset.single_le_sum (f := fun η => jointComponent prior κ η A)
    (fun _ _ => zero_le _) (Finset.mem_univ ω)

theorem component_ac (prior : FiniteDist Ω) (κ : SignalKernel Ω Signal) (ω : Ω) :
    jointComponent prior κ ω ≪ signalLaw prior κ :=
  Measure.absolutelyContinuous_of_le (component_le prior κ ω)

omit [Fintype Ω] in
theorem rnDeriv_finset_sum (ν : Ω → Measure Signal) [∀ ω, IsFiniteMeasure (ν ω)]
    (μ : Measure Signal) [IsFiniteMeasure μ] (T : Finset Ω) :
    (∑ ω ∈ T, ν ω).rnDeriv μ =ᵐ[μ] fun s => ∑ ω ∈ T, (ν ω).rnDeriv μ s := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using Measure.rnDeriv_zero μ
  | @insert ω T hω ih =>
    rw [Finset.sum_insert hω]
    filter_upwards [Measure.rnDeriv_add (ν ω) (∑ η ∈ T, ν η) μ, ih] with s hs ht
    simpa only [Pi.add_apply, Finset.sum_insert hω, ht] using hs

def density (prior : FiniteDist Ω) (κ : SignalKernel Ω Signal) (ω : Ω) (s : Signal) : ℝ :=
  ((jointComponent prior κ ω).rnDeriv (signalLaw prior κ) s).toReal

theorem density_nonneg (prior : FiniteDist Ω) (κ : SignalKernel Ω Signal) (ω : Ω) (s : Signal) :
    0 ≤ density prior κ ω s := ENNReal.toReal_nonneg

theorem density_measurable (prior : FiniteDist Ω) (κ : SignalKernel Ω Signal) (ω : Ω) :
    Measurable (density prior κ ω) := (Measure.measurable_rnDeriv _ _).ennreal_toReal

theorem density_sum (prior : FiniteDist Ω) (κ : SignalKernel Ω Signal) :
    ∀ᵐ s ∂signalLaw prior κ, ∑ ω, density prior κ ω s = 1 := by
  have hsum := rnDeriv_finset_sum (jointComponent prior κ) (signalLaw prior κ) Finset.univ
  have hfin : ∀ᵐ s ∂signalLaw prior κ,
      ∀ ω, (jointComponent prior κ ω).rnDeriv (signalLaw prior κ) s < ∞ :=
    ae_all_iff.mpr (fun ω => Measure.rnDeriv_lt_top _ _)
  filter_upwards [hsum, (signalLaw prior κ).rnDeriv_self, hfin] with s hs hself hfinite
  change ∑ ω, ((jointComponent prior κ ω).rnDeriv (signalLaw prior κ) s).toReal = 1
  rw [← ENNReal.toReal_sum (fun ω _ => ne_of_lt (hfinite ω)), ← hs]
  change ((signalLaw prior κ).rnDeriv (signalLaw prior κ) s).toReal = 1
  rw [hself]
  simp

def posterior (prior : FiniteDist Ω) (κ : SignalKernel Ω Signal) (s : Signal) : FiniteDist Ω :=
  if h : ∑ ω, density prior κ ω s = 1 then
    ⟨fun ω => density prior κ ω s, fun ω => density_nonneg prior κ ω s, h⟩
  else prior

theorem posterior_ae (prior : FiniteDist Ω) (κ : SignalKernel Ω Signal) :
    ∀ᵐ s ∂signalLaw prior κ, ∀ ω, (posterior prior κ s).prob ω = density prior κ ω s := by
  filter_upwards [density_sum prior κ] with s hs
  simp [posterior, hs]

theorem posterior_measurable (prior : FiniteDist Ω) (κ : SignalKernel Ω Signal) :
    Measurable (fun s => (posterior prior κ s).prob) := by
  classical
  have hsum : Measurable (fun s => ∑ ω, density prior κ ω s) :=
    Finset.measurable_sum _ (fun ω _ => density_measurable prior κ ω)
  apply measurable_pi_lambda
  intro ω
  have hh : Measurable (fun s => if ∑ η, density prior κ η s = 1 then
      density prior κ ω s else prior.prob ω) :=
    Measurable.ite (measurableSet_eq_fun hsum (measurable_const (a := (1 : ℝ))))
      (density_measurable prior κ ω) (measurable_const (a := prior.prob ω))
  have heq : (fun s => (posterior prior κ s).prob ω) =
      (fun s => if ∑ η, density prior κ η s = 1 then density prior κ ω s else prior.prob ω) := by
    funext s
    by_cases hs : ∑ η, density prior κ η s = 1 <;> simp [posterior, hs]
  rw [heq]
  exact hh

/-- The posterior satisfies Bayes' rule on every signal event, including
zero-prior states; no division by the probability of an individual signal. -/
theorem posterior_joint (prior : FiniteDist Ω) (κ : SignalKernel Ω Signal)
    (ω : Ω) (A : Set Signal) :
    (∫ s in A, (posterior prior κ s).prob ω ∂signalLaw prior κ) =
      (jointComponent prior κ ω).real A := by
  calc
    _ = ∫ s in A, density prior κ ω s ∂signalLaw prior κ :=
      integral_congr_ae (ae_restrict_of_ae ((posterior_ae prior κ).mono (fun _ h => h ω)))
    _ = _ := Measure.setIntegral_toReal_rnDeriv (component_ac prior κ ω) A

theorem posterior_plausible (prior : FiniteDist Ω) (κ : SignalKernel Ω Signal) (ω : Ω) :
    (∫ s, (posterior prior κ s).prob ω ∂signalLaw prior κ) = prior.prob ω := by
  have h := posterior_joint prior κ ω Set.univ
  simpa [jointComponent, measureReal_def, Measure.smul_apply, prior.nonneg ω] using h

end SignalKernel

end

end TransparencyLean
