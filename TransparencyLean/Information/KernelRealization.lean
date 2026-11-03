import TransparencyLean.Information.KernelContracts
import TransparencyLean.Information.FiniteMeasure

namespace TransparencyLean

open scoped BigOperators ENNReal
open MeasureTheory Set

noncomputable section

variable {Ω Signal : Type*} [Fintype Ω] [Fintype Signal]
  [MeasurableSpace Signal] [MeasurableSingletonClass Signal]

namespace PosteriorScheme

variable {prior : FiniteDist Ω} (scheme : PosteriorScheme prior Signal)

def toSignalKernel : SignalKernel Ω Signal where
  law ω := (scheme.toKernel ω).toMeasure
  probability _ := inferInstance

theorem signalLaw_toSignalKernel : scheme.toSignalKernel.signalLaw prior = scheme.weights.toMeasure := by
  apply Measure.ext_of_singleton
  intro s
  simp only [SignalKernel.signalLaw, Measure.finset_sum_apply, SignalKernel.jointComponent,
    Measure.smul_apply, toSignalKernel, FiniteDist.toMeasure_singleton, smul_eq_mul]
  simp_rw [← ENNReal.ofReal_mul (prior.nonneg _)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ =>
    mul_nonneg (prior.nonneg ω) ((scheme.toKernel ω).nonneg s))]
  congr 1
  exact scheme.kernel_signalMass s

theorem posterior_toSignalKernel :
    ∀ᵐ s ∂scheme.toSignalKernel.signalLaw prior,
      scheme.toSignalKernel.posterior prior s = scheme.posterior s := by
  apply ae_iff_of_countable.mpr
  intro s hs
  have hmass : (scheme.toSignalKernel.signalLaw prior).real {s} = scheme.weights.prob s := by
    rw [scheme.signalLaw_toSignalKernel]
    simp [measureReal_def, FiniteDist.toMeasure_singleton, scheme.weights.nonneg s]
  have hw : scheme.weights.prob s ≠ 0 := by
    intro hw
    rw [scheme.signalLaw_toSignalKernel, FiniteDist.toMeasure_singleton, hw] at hs
    simp at hs
  apply FiniteDist.ext
  intro ω
  have h := scheme.toSignalKernel.posterior_joint prior ω {s}
  have hjoint : (SignalKernel.jointComponent prior scheme.toSignalKernel ω).real {s} =
      prior.prob ω * (scheme.toKernel ω).prob s := by
    simp [SignalKernel.jointComponent, toSignalKernel, measureReal_def, Measure.smul_apply,
      FiniteDist.toMeasure_singleton, ENNReal.toReal_mul, prior.nonneg ω,
      (scheme.toKernel ω).nonneg s]
  rw [integral_singleton, hmass, hjoint, scheme.kernel_joint_eq] at h
  exact mul_left_cancel₀ hw h

end PosteriorScheme

variable {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
variable {prior : FiniteDist Ω} {f : Ω → Finset Agent → ℝ} {c : Agent → ℝ}

def ContractScheme.toKernelContract (scheme : ContractScheme prior f c Signal) :
    KernelContractScheme prior f c Signal where
  kernel := scheme.information.toSignalKernel
  contract := scheme.contract
  team := scheme.team
  feasible := Filter.Eventually.of_forall scheme.feasible
  equilibrium := by
    filter_upwards [scheme.information.posterior_toSignalKernel] with s hs
    rw [hs]
    exact scheme.equilibrium s
  measurable_payoff := (measurable_of_finite _).aestronglyMeasurable

@[simp] theorem ContractScheme.toKernelContract_utility (scheme : ContractScheme prior f c Signal) :
    scheme.toKernelContract.utility = scheme.utility := by
  have hpost := scheme.information.posterior_toSignalKernel
  rw [scheme.information.signalLaw_toSignalKernel] at hpost
  change (∫ s, principalUtility
    (posteriorReward (scheme.information.toSignalKernel.posterior prior s) f)
    (scheme.contract s) (scheme.team s) ∂scheme.information.toSignalKernel.signalLaw prior) = _
  rw [scheme.information.signalLaw_toSignalKernel]
  calc
    _ = ∫ s, principalUtility (posteriorReward (scheme.information.posterior s) f)
        (scheme.contract s) (scheme.team s) ∂scheme.information.weights.toMeasure :=
      integral_congr_ae (hpost.mono (fun _ hs => by rw [hs]))
    _ = _ := scheme.information.weights.integral_toMeasure _

/-- The paper's finite-attainment footnote, entirely in the kernel model:
an optimal joint signaling/contract scheme exists on a finite signal space
and dominates every admissible scheme on every measurable signal space. -/
theorem kernel_optimum_attained (prior : FiniteDist Ω) (f : Ω → Finset Agent → ℝ)
    (c : Agent → ℝ) (hc : ∀ i, 0 ≤ c i) :
    ∃ optimal : KernelContractScheme prior f c (Fin (supportBound Ω)),
      ∀ (Signal : Type*) [MeasurableSpace Signal]
        (scheme : KernelContractScheme prior f c Signal), scheme.utility ≤ optimal.utility := by
  obtain ⟨optimal, hopt⟩ := optimal_finite_for_kernels prior f c hc
  exact ⟨optimal.toKernelContract, fun Signal _ scheme => by
    rw [ContractScheme.toKernelContract_utility]
    exact hopt Signal scheme⟩

/-- Paper Theorem 4.1, upper-bound direction, stated with an actual full
revelation kernel and quantified over all measurable public signal kernels. -/
theorem submodular_full_transparency [DecidableEq Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (prior : FiniteDist Ω)
    (f : Ω → Finset Agent → ℝ) (c : Agent → ℝ)
    (hf : ∀ ω, ValidReward (f ω)) (hmono : ∀ ω, Monotone (f ω))
    (hsub : ∀ ω, Submodular (f ω)) (hc : ∀ i, 0 ≤ c i) :
    ∃ full : KernelContractScheme prior f c Ω,
      full.kernel = (PosteriorScheme.full prior).toSignalKernel ∧
      full.utility = fullDisclosureValue prior f c ∧
      ∀ (Signal : Type*) [MeasurableSpace Signal]
        (scheme : KernelContractScheme prior f c Signal), 3 * scheme.utility ≤ 4 * full.utility := by
  obtain ⟨finite, hinfo, hvalue⟩ := fullDisclosure_attained prior f c hf hmono hc
  refine ⟨finite.toKernelContract, ?_, ?_, ?_⟩
  · change finite.information.toSignalKernel = _
    rw [hinfo]
  · rw [ContractScheme.toKernelContract_utility, hvalue]
  · intro Signal _ scheme
    rw [ContractScheme.toKernelContract_utility, hvalue]
    linarith [scheme.submodular_four_thirds hf hmono hsub hc]

end

end TransparencyLean
