import TransparencyLean.Mixed.Transparency
import TransparencyLean.Information.KernelRealization

/-! The mixed guarantee for arbitrary measurable public signal kernels. -/

namespace TransparencyLean.Mixed

open scoped BigOperators
open MeasureTheory

noncomputable section

variable {Ω Agent : Type*} [Fintype Ω] [Fintype Agent] [DecidableEq Agent]

structure KernelContractScheme (prior : FiniteDist Ω) (f : Ω → Finset Agent → ℝ)
    (c : Agent → ℝ) (Signal : Type*) [MeasurableSpace Signal] where
  kernel : SignalKernel Ω Signal
  contract : Signal → Agent → ℝ
  profile : Signal → Agent → ℝ
  feasible : ∀ᵐ s ∂kernel.signalLaw prior, FeasibleContract (contract s)
  valid : ∀ᵐ s ∂kernel.signalLaw prior, ValidProfile (profile s)
  equilibrium : ∀ᵐ s ∂kernel.signalLaw prior,
    IsMixedEquilibrium (posteriorReward (kernel.posterior prior s) f) c (contract s) (profile s)
  measurable_payoff : AEStronglyMeasurable (fun s => utility
    (posteriorReward (kernel.posterior prior s) f) (contract s) (profile s)) (kernel.signalLaw prior)

theorem utility_abs_bound {f : Finset Agent → ℝ} (hf : ValidReward f)
    {α x : Agent → ℝ} (hα : FeasibleContract α) (hx : ValidProfile x) :
    |utility f α x| ≤ (Fintype.card Agent : ℝ) + 1 := by
  have hs0 : 0 ≤ ∑ i, α i := Finset.sum_nonneg (fun i _ => (hα i).1)
  have hs1 : ∑ i, α i ≤ (Fintype.card Agent : ℝ) := by
    simpa using Finset.sum_le_sum (s := (Finset.univ : Finset Agent)) (fun i _ => (hα i).2)
  have hn : (0 : ℝ) ≤ Fintype.card Agent := Nat.cast_nonneg _
  have hF := sample_bounds hx Finset.univ hf
  change 0 ≤ extension f x ∧ extension f x ≤ 1 at hF
  have hp := mul_le_mul_of_nonneg_left hF.2 hs0
  have hu := utility_le_one hf hα hx
  apply abs_le.mpr
  unfold utility at *
  constructor <;> nlinarith

variable {Signal : Type*} [MeasurableSpace Signal]

theorem posterior_prob_integrable (prior : FiniteDist Ω) (κ : SignalKernel Ω Signal) (ω : Ω) :
    Integrable (fun s => (κ.posterior prior s).prob ω) (κ.signalLaw prior) := by
  have hm := (measurable_pi_apply ω).comp (κ.posterior_measurable prior)
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro s
  change ‖(κ.posterior prior s).prob ω‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg ((κ.posterior prior s).nonneg ω)]
  exact (Finset.single_le_sum (fun η _ => (κ.posterior prior s).nonneg η)
    (Finset.mem_univ ω)).trans_eq (κ.posterior prior s).sum_eq_one

theorem posterior_expect_integrable (prior : FiniteDist Ω) (κ : SignalKernel Ω Signal) (v : Ω → ℝ) :
    Integrable (fun s => (κ.posterior prior s).expect v) (κ.signalLaw prior) := by
  exact integrable_finset_sum _ (fun ω _ => (posterior_prob_integrable prior κ ω).mul_const (v ω))

theorem integral_posterior_expect (prior : FiniteDist Ω) (κ : SignalKernel Ω Signal) (v : Ω → ℝ) :
    (∫ s, (κ.posterior prior s).expect v ∂κ.signalLaw prior) = prior.expect v := by
  unfold FiniteDist.expect
  rw [integral_finset_sum _ (fun ω _ => (posterior_prob_integrable prior κ ω).mul_const (v ω))]
  simp_rw [integral_mul_const, κ.posterior_plausible prior]

namespace KernelContractScheme

variable {prior : FiniteDist Ω} {f : Ω → Finset Agent → ℝ} {c : Agent → ℝ}

def utility (scheme : KernelContractScheme prior f c Signal) : ℝ :=
  ∫ s, Mixed.utility (posteriorReward (scheme.kernel.posterior prior s) f)
    (scheme.contract s) (scheme.profile s) ∂scheme.kernel.signalLaw prior

theorem payoff_integrable (scheme : KernelContractScheme prior f c Signal)
    (hf : ∀ ω, ValidReward (f ω)) :
    Integrable (fun s => Mixed.utility (posteriorReward (scheme.kernel.posterior prior s) f)
      (scheme.contract s) (scheme.profile s)) (scheme.kernel.signalLaw prior) := by
  apply (integrable_const ((Fintype.card Agent : ℝ) + 1)).mono' scheme.measurable_payoff
  filter_upwards [scheme.feasible, scheme.valid] with s hα hx
  simpa only [Real.norm_eq_abs] using utility_abs_bound (posteriorReward_valid _ hf) hα hx

theorem all_or_nothing (scheme : KernelContractScheme prior f c Signal)
    (hf : ∀ ω, ValidReward (f ω)) (β : ℝ)
    (hbound : ∀ μ, noDisclosureValue μ f c ≤ β * fullDisclosureValue μ f c) :
    scheme.utility ≤ β * fullDisclosureValue prior f c := by
  have h := integral_mono_ae (scheme.payoff_integrable hf)
    ((posterior_expect_integrable prior scheme.kernel (fun ω => statelessValue (f ω) c)).const_mul β)
    (show ∀ᵐ s ∂scheme.kernel.signalLaw prior,
      Mixed.utility (posteriorReward (scheme.kernel.posterior prior s) f)
        (scheme.contract s) (scheme.profile s) ≤
          β * (scheme.kernel.posterior prior s).expect (fun ω => statelessValue (f ω) c) from by
      filter_upwards [scheme.feasible, scheme.valid, scheme.equilibrium] with s hα hx heq
      exact (utility_le_statelessValue (posteriorReward_valid _ hf) hα hx heq).trans (hbound _))
  rw [integral_const_mul, integral_posterior_expect] at h
  exact h

theorem submodular_four_thirds (scheme : KernelContractScheme prior f c Signal)
    (hf : ∀ ω, ValidReward (f ω)) (hmono : ∀ ω, Monotone (f ω))
    (hsub : ∀ ω, Submodular (f ω)) (hc : ∀ i, 0 ≤ c i) :
    scheme.utility ≤ (4 / 3) * fullDisclosureValue prior f c :=
  scheme.all_or_nothing hf (4 / 3) (fun μ => noDisclosure_le_four_thirds μ hf hmono hsub hc)

def ofPure (scheme : TransparencyLean.KernelContractScheme prior f c Signal) :
    KernelContractScheme prior f c Signal where
  kernel := scheme.kernel
  contract := scheme.contract
  profile s := pureProfile (scheme.team s)
  feasible := scheme.feasible
  valid := Filter.Eventually.of_forall (fun _ => pureProfile_valid _)
  equilibrium := scheme.equilibrium.mono (fun s hs => (pure_equilibrium_iff _ _ _ _).mpr hs)
  measurable_payoff := by simpa only [utility_pure] using scheme.measurable_payoff

@[simp] theorem ofPure_utility (scheme : TransparencyLean.KernelContractScheme prior f c Signal) :
    (ofPure scheme).utility = scheme.utility := by
  simp only [utility, ofPure, utility_pure]
  rfl

end KernelContractScheme

variable [Fintype Signal] [MeasurableSingletonClass Signal]
variable {prior : FiniteDist Ω} {f : Ω → Finset Agent → ℝ} {c : Agent → ℝ}

def ContractScheme.toKernelContract (scheme : ContractScheme prior f c Signal) :
    KernelContractScheme prior f c Signal where
  kernel := scheme.information.toSignalKernel
  contract := scheme.contract
  profile := scheme.profile
  feasible := Filter.Eventually.of_forall scheme.feasible
  valid := Filter.Eventually.of_forall scheme.valid
  equilibrium := by
    filter_upwards [scheme.information.posterior_toSignalKernel] with s hs
    rw [hs]
    exact scheme.equilibrium s
  measurable_payoff := (measurable_of_finite _).aestronglyMeasurable

@[simp] theorem ContractScheme.toKernelContract_utility (scheme : ContractScheme prior f c Signal) :
    scheme.toKernelContract.utility = scheme.utility := by
  have hpost := scheme.information.posterior_toSignalKernel
  rw [scheme.information.signalLaw_toSignalKernel] at hpost
  change (∫ s, Mixed.utility (posteriorReward (scheme.information.toSignalKernel.posterior prior s) f)
    (scheme.contract s) (scheme.profile s) ∂scheme.information.toSignalKernel.signalLaw prior) = _
  rw [scheme.information.signalLaw_toSignalKernel]
  calc
    _ = ∫ s, Mixed.utility (posteriorReward (scheme.information.posterior s) f)
        (scheme.contract s) (scheme.profile s) ∂scheme.information.weights.toMeasure :=
      integral_congr_ae (hpost.mono (fun _ h => by rw [h]))
    _ = _ := scheme.information.weights.integral_toMeasure _

/-- Theorem A.2's upper bound with an attained mixed full-disclosure kernel,
uniformly against every admissible scheme on every measurable signal space. -/
theorem submodular_full_transparency [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (prior : FiniteDist Ω) (f : Ω → Finset Agent → ℝ) (c : Agent → ℝ)
    (hf : ∀ ω, ValidReward (f ω)) (hmono : ∀ ω, Monotone (f ω))
    (hsub : ∀ ω, Submodular (f ω)) (hc : ∀ i, 0 ≤ c i) :
    ∃ full : KernelContractScheme prior f c Ω,
      full.kernel = (PosteriorScheme.full prior).toSignalKernel ∧
      full.utility = fullDisclosureValue prior f c ∧
      ∀ (Signal : Type*) [MeasurableSpace Signal]
        (scheme : KernelContractScheme prior f c Signal), 3 * scheme.utility ≤ 4 * full.utility := by
  obtain ⟨finite, hinfo, hvalue⟩ := fullDisclosure_attained prior f c hf hc
  refine ⟨finite.toKernelContract, ?_, ?_, ?_⟩
  · change finite.information.toSignalKernel = _
    rw [hinfo]
  · rw [ContractScheme.toKernelContract_utility, hvalue]
  · intro Signal _ scheme
    rw [ContractScheme.toKernelContract_utility, hvalue]
    linarith [scheme.submodular_four_thirds hf hmono hsub hc]

end

end TransparencyLean.Mixed
