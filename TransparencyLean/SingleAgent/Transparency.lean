import TransparencyLean.SingleAgent.Moments
import TransparencyLean.Mixed.KernelSignals

/-! Theorem B.1, upper bound, for arbitrary measurable public signals. -/

namespace TransparencyLean.SingleAgent

noncomputable section

variable {Ω : Type*} [Fintype Ω]

/-- The moment inequalities imply the 9/8 comparison at every prior. -/
theorem noDisclosure_le_nine_eighths (prior : FiniteDist Ω) {f : Ω → Finset Unit → ℝ} {c : ℝ}
    (hf : ∀ ω, ValidReward (f ω)) (hmono : ∀ ω, Monotone (f ω)) (hc : 0 ≤ c) :
    noDisclosureValue prior f (costs c) ≤ (9 / 8) * fullDisclosureValue prior f (costs c) := by
  let A := prior.expect (fun ω => f ω ∅)
  let F := prior.expect (fun ω => value (f ω) c)
  let R := prior.expect (fun ω => loss (f ω) c)
  have hA : 0 ≤ A := prior.expect_nonneg (fun ω => (hf ω ∅).1)
  have hAF : A ≤ F := prior.expect_mono (fun ω => baseline_le_value (hf ω) hc)
  have hR : 0 ≤ R := prior.expect_nonneg (fun ω => loss_nonneg (hf ω) (hmono ω) hc)
  have hB : F + R = prior.expect (fun ω => f ω Finset.univ) := by
    rw [← FiniteDist.expect_add]
    congr 1
    funext ω
    dsimp [loss]
    ring
  have hmoment : R ^ 2 ≤ c * (A + R) := by
    have h := prior.expect_mono (fun ω => loss_square_bound (hf ω) (hmono ω) hc)
    rw [FiniteDist.expect_mul, FiniteDist.expect_add] at h
    exact (square_expect_le_expect_square prior (fun ω => loss (f ω) c)).trans h
  apply statelessValue_le (fun _ => hc)
  intro α S hα heq
  simp only [principalUtility, Fintype.sum_unique]
  rcases team_cases S with rfl | rfl
  · change (1 - α ()) * A ≤ (9 / 8) * F
    nlinarith [mul_nonneg (hα ()).1 hA]
  · have hi := grand_incentive heq
    change c ≤ α () * (prior.expect (fun ω => f ω Finset.univ) - A) at hi
    rw [← hB] at hi
    have h := nine_eighths_from_moments hA hAF hR (hα ()).1 hmoment hi
    change (1 - α ()) * prior.expect (fun ω => f ω Finset.univ) ≤ (9 / 8) * F
    rw [← hB]
    linarith

theorem mixed_noDisclosure_eq (prior : FiniteDist Ω) {f : Ω → Finset Unit → ℝ} {c : ℝ}
    (hf : ∀ ω, ValidReward (f ω)) (hmono : ∀ ω, Monotone (f ω)) (hc : 0 ≤ c) :
    Mixed.noDisclosureValue prior f (costs c) = noDisclosureValue prior f (costs c) :=
  Mixed.supermodular_noDisclosure_eq_pure prior hf hmono (fun ω => supermodular (f ω)) (fun _ => hc)

theorem mixed_fullDisclosure_eq (prior : FiniteDist Ω) {f : Ω → Finset Unit → ℝ} {c : ℝ}
    (hf : ∀ ω, ValidReward (f ω)) (hmono : ∀ ω, Monotone (f ω)) (hc : 0 ≤ c) :
    Mixed.fullDisclosureValue prior f (costs c) = fullDisclosureValue prior f (costs c) :=
  Mixed.supermodular_fullDisclosure_eq_pure prior hf hmono (fun ω => supermodular (f ω)) (fun _ => hc)

variable {Signal : Type*}

theorem finite_nine_eighths [Fintype Signal] {prior : FiniteDist Ω}
    {f : Ω → Finset Unit → ℝ} {c : ℝ} (scheme : ContractScheme prior f (costs c) Signal)
    (hf : ∀ ω, ValidReward (f ω)) (hmono : ∀ ω, Monotone (f ω)) (hc : 0 ≤ c) :
    scheme.utility ≤ (9 / 8) * fullDisclosureValue prior f (costs c) :=
  scheme.all_or_nothing hf (9 / 8) (fun μ => noDisclosure_le_nine_eighths μ hf hmono hc)

theorem kernel_nine_eighths [MeasurableSpace Signal] {prior : FiniteDist Ω}
    {f : Ω → Finset Unit → ℝ} {c : ℝ} (scheme : KernelContractScheme prior f (costs c) Signal)
    (hf : ∀ ω, ValidReward (f ω)) (hmono : ∀ ω, Monotone (f ω)) (hc : 0 ≤ c) :
    scheme.utility ≤ (9 / 8) * fullDisclosureValue prior f (costs c) :=
  scheme.all_or_nothing hf (9 / 8) (fun μ => noDisclosure_le_nine_eighths μ hf hmono hc)

theorem mixed_kernel_nine_eighths [MeasurableSpace Signal] {prior : FiniteDist Ω}
    {f : Ω → Finset Unit → ℝ} {c : ℝ} (scheme : Mixed.KernelContractScheme prior f (costs c) Signal)
    (hf : ∀ ω, ValidReward (f ω)) (hmono : ∀ ω, Monotone (f ω)) (hc : 0 ≤ c) :
    scheme.utility ≤ (9 / 8) * Mixed.fullDisclosureValue prior f (costs c) := by
  apply scheme.all_or_nothing hf (9 / 8)
  intro μ
  rw [mixed_noDisclosure_eq μ hf hmono hc, mixed_fullDisclosure_eq μ hf hmono hc]
  exact noDisclosure_le_nine_eighths μ hf hmono hc

/-- Full revelation attains the certified benchmark in the pure model. -/
theorem full_transparency [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (prior : FiniteDist Ω) (f : Ω → Finset Unit → ℝ) (c : ℝ)
    (hf : ∀ ω, ValidReward (f ω)) (hmono : ∀ ω, Monotone (f ω)) (hc : 0 ≤ c) :
    ∃ full : KernelContractScheme prior f (costs c) Ω,
      full.kernel = (PosteriorScheme.full prior).toSignalKernel ∧
      full.utility = fullDisclosureValue prior f (costs c) ∧
      ∀ (Signal : Type*) [MeasurableSpace Signal] (scheme : KernelContractScheme prior f (costs c) Signal),
        8 * scheme.utility ≤ 9 * full.utility := by
  obtain ⟨finite, hinfo, hvalue⟩ := fullDisclosure_attained prior f (costs c) hf hmono (fun _ => hc)
  refine ⟨finite.toKernelContract, ?_, ?_, ?_⟩
  · change finite.information.toSignalKernel = _
    rw [hinfo]
  · rw [ContractScheme.toKernelContract_utility, hvalue]
  · intro Signal _ scheme
    rw [ContractScheme.toKernelContract_utility, hvalue]
    linarith [kernel_nine_eighths scheme hf hmono hc]

/-- The same guarantee with an attained mixed full-disclosure benchmark. -/
theorem mixed_full_transparency [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (prior : FiniteDist Ω) (f : Ω → Finset Unit → ℝ) (c : ℝ)
    (hf : ∀ ω, ValidReward (f ω)) (hmono : ∀ ω, Monotone (f ω)) (hc : 0 ≤ c) :
    ∃ full : Mixed.KernelContractScheme prior f (costs c) Ω,
      full.kernel = (PosteriorScheme.full prior).toSignalKernel ∧
      full.utility = Mixed.fullDisclosureValue prior f (costs c) ∧
      ∀ (Signal : Type*) [MeasurableSpace Signal] (scheme : Mixed.KernelContractScheme prior f (costs c) Signal),
        8 * scheme.utility ≤ 9 * full.utility := by
  obtain ⟨finite, hinfo, hvalue⟩ := Mixed.fullDisclosure_attained prior f (costs c) hf (fun _ => hc)
  refine ⟨finite.toKernelContract, ?_, ?_, ?_⟩
  · change finite.information.toSignalKernel = _
    rw [hinfo]
  · rw [Mixed.ContractScheme.toKernelContract_utility, hvalue]
  · intro Signal _ scheme
    rw [Mixed.ContractScheme.toKernelContract_utility, hvalue]
    linarith [mixed_kernel_nine_eighths scheme hf hmono hc]

end

end TransparencyLean.SingleAgent
