import TransparencyLean.MultiAction.Welfare
import TransparencyLean.Mixed.KernelSignals

/-! Theorem C.1's upper bound for finite posterior schemes and arbitrary
measurable public signal kernels. Selected responses may be mixed; pure
responses are represented by point masses. -/

namespace TransparencyLean.MultiAction

open scoped BigOperators
open MeasureTheory
noncomputable section

variable {Ω A : Type*} [Fintype Ω] [Fintype A] [Nonempty A] [DecidableEq A]

def meanReward (μ : FiniteDist Ω) (r : Ω → A → ℝ) (i : A) : ℝ :=
  μ.expect (fun ω => r ω i)

def fullDisclosureValue (μ : FiniteDist Ω) (r : Ω → A → ℝ) (c : A → ℝ) : ℝ :=
  μ.expect (fun ω => value (r ω) c)

omit [Fintype A] [Nonempty A] [DecidableEq A] in
theorem meanReward_nonneg (μ : FiniteDist Ω) {r : Ω → A → ℝ}
    (hr : ∀ ω i, 0 ≤ r ω i) (i : A) : 0 ≤ meanReward μ r i :=
  μ.expect_nonneg (fun ω => hr ω i)

omit [Fintype A] [Nonempty A] [DecidableEq A] in
@[simp] theorem meanReward_pointMass [DecidableEq Ω] (ω : Ω) (r : Ω → A → ℝ) :
    meanReward (FiniteDist.pointMass ω) r = r ω := by
  ext i
  exact FiniteDist.expect_pointMass _ _

omit [Nonempty A] in
theorem pointMass_bestResponse {r c : A → ℝ} {α : ℝ} {i : A}
    (hi : BestResponse r c α i) : MixedBestResponse r c α (FiniteDist.pointMass i) := by
  intro j hj
  by_cases hji : j = i
  · simpa [hji] using hi
  · simp [FiniteDist.pointMass, hji] at hj

theorem posterior_payoff_le (μ : FiniteDist Ω) {r : Ω → A → ℝ} {c : A → ℝ}
    (hr : ∀ ω i, 0 ≤ r ω i) (hc : ∀ i, 0 ≤ c i) (hz : ∃ z, c z = 0)
    {α : ℝ} {i : A} (hα : FeasibleShare α) (hi : BestResponse (meanReward μ r) c α i) :
    payoff (meanReward μ r) α i ≤ Fintype.card A * fullDisclosureValue μ r c := by
  obtain ⟨z, hz⟩ := hz
  have hIR := hi z
  rw [hz, sub_zero] at hIR
  have hzero := mul_nonneg hα.1 (meanReward_nonneg μ hr z)
  have hprofit : payoff (meanReward μ r) α i ≤ meanReward μ r i - c i := by
    dsimp [payoff]
    linarith
  calc
    _ ≤ meanReward μ r i - c i := hprofit
    _ = μ.expect (fun ω => r ω i - c i) := by rw [μ.expect_sub, μ.expect_const]; rfl
    _ ≤ μ.expect (fun ω => (Fintype.card A : ℝ) * value (r ω) c) :=
      μ.expect_mono (fun ω => welfare_le_card_value (hr ω) hc i)
    _ = _ := μ.expect_mul _ _

theorem mixed_posterior_payoff_le (μ : FiniteDist Ω) {r : Ω → A → ℝ} {c : A → ℝ}
    (hr : ∀ ω i, 0 ≤ r ω i) (hc : ∀ i, 0 ≤ c i) (hz : ∃ z, c z = 0)
    {α : ℝ} (p : FiniteDist A) (hα : FeasibleShare α)
    (hp : MixedBestResponse (meanReward μ r) c α p) :
    p.expect (payoff (meanReward μ r) α) ≤ Fintype.card A * fullDisclosureValue μ r c := by
  obtain ⟨i, hi, hdom⟩ := mixed_dominated p hp
  exact hdom.trans (posterior_payoff_le μ hr hc hz hα hi)

structure ContractScheme (prior : FiniteDist Ω) (r : Ω → A → ℝ) (c : A → ℝ)
    (Signal : Type*) [Fintype Signal] where
  information : PosteriorScheme prior Signal
  share : Signal → ℝ
  response : Signal → FiniteDist A
  feasible : ∀ s, FeasibleShare (share s)
  equilibrium : ∀ s, MixedBestResponse (meanReward (information.posterior s) r) c (share s) (response s)

def ContractScheme.utility {Signal : Type*} [Fintype Signal] {prior : FiniteDist Ω}
    {r : Ω → A → ℝ} {c : A → ℝ} (scheme : ContractScheme prior r c Signal) : ℝ :=
  scheme.information.weights.expect (fun s =>
    (scheme.response s).expect (payoff (meanReward (scheme.information.posterior s) r) (scheme.share s)))

theorem finite_card_bound {Signal : Type*} [Fintype Signal] {prior : FiniteDist Ω}
    {r : Ω → A → ℝ} {c : A → ℝ} (scheme : ContractScheme prior r c Signal)
    (hr : ∀ ω i, 0 ≤ r ω i) (hc : ∀ i, 0 ≤ c i) (hz : ∃ z, c z = 0) :
    scheme.utility ≤ Fintype.card A * fullDisclosureValue prior r c := by
  exact scheme.information.payoff_le_of_all_or_nothing (fun ω => value (r ω) c)
    (fun μ => Fintype.card A * fullDisclosureValue μ r c) _ (Fintype.card A)
    (fun s => mixed_posterior_payoff_le _ hr hc hz _ (scheme.feasible s) (scheme.equilibrium s))
    (fun _ => le_rfl)

theorem fullDisclosure_attained [DecidableEq Ω] (prior : FiniteDist Ω)
    (r : Ω → A → ℝ) (c : A → ℝ) :
    ∃ full : ContractScheme prior r c Ω,
      full.information = PosteriorScheme.full prior ∧ full.utility = fullDisclosureValue prior r c := by
  choose α i hα hi hu using fun ω => value_attained (r ω) c
  let full : ContractScheme prior r c Ω := {
    information := PosteriorScheme.full prior
    share := α
    response := fun ω => FiniteDist.pointMass (i ω)
    feasible := hα
    equilibrium := fun ω => by
      change MixedBestResponse (meanReward (FiniteDist.pointMass ω) r) c _ _
      rw [meanReward_pointMass]
      exact pointMass_bestResponse (hi ω) }
  refine ⟨full, rfl, ?_⟩
  change prior.expect (fun ω => (FiniteDist.pointMass (i ω)).expect
    (payoff (meanReward (FiniteDist.pointMass ω) r) (α ω))) = _
  simp only [meanReward_pointMass, FiniteDist.expect_pointMass, hu]
  rfl

structure KernelContractScheme (prior : FiniteDist Ω) (r : Ω → A → ℝ) (c : A → ℝ)
    (Signal : Type*) [MeasurableSpace Signal] where
  kernel : SignalKernel Ω Signal
  share : Signal → ℝ
  response : Signal → FiniteDist A
  feasible : ∀ᵐ s ∂kernel.signalLaw prior, FeasibleShare (share s)
  equilibrium : ∀ᵐ s ∂kernel.signalLaw prior,
    MixedBestResponse (meanReward (kernel.posterior prior s) r) c (share s) (response s)
  measurable_payoff : AEStronglyMeasurable (fun s =>
    (response s).expect (payoff (meanReward (kernel.posterior prior s) r) (share s))) (kernel.signalLaw prior)

namespace KernelContractScheme

variable {Signal : Type*} [MeasurableSpace Signal] {prior : FiniteDist Ω}
variable {r : Ω → A → ℝ} {c : A → ℝ}

def utility (scheme : KernelContractScheme prior r c Signal) : ℝ :=
  ∫ s, (scheme.response s).expect
    (payoff (meanReward (scheme.kernel.posterior prior s) r) (scheme.share s)) ∂scheme.kernel.signalLaw prior

omit [Nonempty A] [DecidableEq A] in
theorem payoff_integrable (scheme : KernelContractScheme prior r c Signal)
    (hr : ∀ ω i, 0 ≤ r ω i) :
    Integrable (fun s => (scheme.response s).expect
      (payoff (meanReward (scheme.kernel.posterior prior s) r) (scheme.share s))) (scheme.kernel.signalLaw prior) := by
  apply (Mixed.posterior_expect_integrable prior scheme.kernel (fun ω => ∑ i, r ω i)).mono'
    scheme.measurable_payoff
  filter_upwards [scheme.feasible] with s hα
  rw [Real.norm_eq_abs, abs_of_nonneg ((scheme.response s).expect_nonneg
    (payoff_nonneg (meanReward_nonneg _ hr) hα))]
  let μ := scheme.kernel.posterior prior s
  have h (i : A) : payoff (meanReward μ r) (scheme.share s) i ≤ μ.expect (fun ω => ∑ j, r ω j) :=
    (payoff_le_reward (meanReward_nonneg μ hr) hα i).trans
      (μ.expect_mono (fun ω => Finset.single_le_sum (fun j _ => hr ω j) (Finset.mem_univ i)))
  exact ((scheme.response s).expect_mono h).trans_eq ((scheme.response s).expect_const _)

theorem card_bound (scheme : KernelContractScheme prior r c Signal)
    (hr : ∀ ω i, 0 ≤ r ω i) (hc : ∀ i, 0 ≤ c i) (hz : ∃ z, c z = 0) :
    scheme.utility ≤ Fintype.card A * fullDisclosureValue prior r c := by
  have h := integral_mono_ae (scheme.payoff_integrable hr)
    ((Mixed.posterior_expect_integrable prior scheme.kernel (fun ω => value (r ω) c)).const_mul
      (Fintype.card A : ℝ))
    (show ∀ᵐ s ∂scheme.kernel.signalLaw prior, (scheme.response s).expect
      (payoff (meanReward (scheme.kernel.posterior prior s) r) (scheme.share s)) ≤
        Fintype.card A * fullDisclosureValue (scheme.kernel.posterior prior s) r c from by
      filter_upwards [scheme.feasible, scheme.equilibrium] with s hα hp
      exact mixed_posterior_payoff_le _ hr hc hz _ hα hp)
  rw [integral_const_mul, Mixed.integral_posterior_expect] at h
  exact h

end KernelContractScheme

variable {Signal : Type*} [Fintype Signal] [MeasurableSpace Signal] [MeasurableSingletonClass Signal]
variable {prior : FiniteDist Ω} {r : Ω → A → ℝ} {c : A → ℝ}

def ContractScheme.toKernelContract (scheme : ContractScheme prior r c Signal) :
    KernelContractScheme prior r c Signal where
  kernel := scheme.information.toSignalKernel
  share := scheme.share
  response := scheme.response
  feasible := Filter.Eventually.of_forall scheme.feasible
  equilibrium := by
    filter_upwards [scheme.information.posterior_toSignalKernel] with s hs
    rw [hs]
    exact scheme.equilibrium s
  measurable_payoff := (measurable_of_finite _).aestronglyMeasurable

omit [Nonempty A] [DecidableEq A] in
@[simp] theorem ContractScheme.toKernelContract_utility (scheme : ContractScheme prior r c Signal) :
    scheme.toKernelContract.utility = scheme.utility := by
  have hpost := scheme.information.posterior_toSignalKernel
  rw [scheme.information.signalLaw_toSignalKernel] at hpost
  change (∫ s, (scheme.response s).expect (payoff
    (meanReward (scheme.information.toSignalKernel.posterior prior s) r) (scheme.share s))
      ∂scheme.information.toSignalKernel.signalLaw prior) = _
  rw [scheme.information.signalLaw_toSignalKernel]
  calc
    _ = ∫ s, (scheme.response s).expect (payoff
        (meanReward (scheme.information.posterior s) r) (scheme.share s))
          ∂scheme.information.weights.toMeasure :=
      integral_congr_ae (hpost.mono (fun _ h => by rw [h]))
    _ = _ := scheme.information.weights.integral_toMeasure _

/-- An attained full-revelation benchmark is an n-approximation against all
measurable public signals, including selected mixed responses. -/
theorem full_transparency [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (prior : FiniteDist Ω) (r : Ω → A → ℝ) (c : A → ℝ)
    (hr : ∀ ω i, 0 ≤ r ω i) (hc : ∀ i, 0 ≤ c i) (hz : ∃ z, c z = 0) :
    ∃ full : KernelContractScheme prior r c Ω,
      full.kernel = (PosteriorScheme.full prior).toSignalKernel ∧
      full.utility = fullDisclosureValue prior r c ∧
      ∀ (Signal : Type*) [MeasurableSpace Signal] (scheme : KernelContractScheme prior r c Signal),
        scheme.utility ≤ Fintype.card A * full.utility := by
  obtain ⟨full, hinfo, hv⟩ := fullDisclosure_attained prior r c
  refine ⟨full.toKernelContract, ?_, ?_, ?_⟩
  · change full.information.toSignalKernel = _
    rw [hinfo]
  · rw [ContractScheme.toKernelContract_utility, hv]
  · intro Signal _ scheme
    rw [ContractScheme.toKernelContract_utility, hv]
    exact scheme.card_bound hr hc hz

end
end TransparencyLean.MultiAction
