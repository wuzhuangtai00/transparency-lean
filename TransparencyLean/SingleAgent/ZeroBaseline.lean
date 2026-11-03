import TransparencyLean.SingleAgent.Transparency

/-! The zero-baseline clause of Theorem B.1, in both equilibrium models. -/

namespace TransparencyLean.SingleAgent

noncomputable section

variable {Ω : Type*} [Fintype Ω]

theorem noDisclosure_le_full_of_zero_baseline (prior : FiniteDist Ω)
    {f : Ω → Finset Unit → ℝ} {c : ℝ} (hf : ∀ ω, ValidReward (f ω))
    (hmono : ∀ ω, Monotone (f ω)) (hc : 0 ≤ c) (hzero : ∀ ω, f ω ∅ = 0) :
    noDisclosureValue prior f (costs c) ≤ fullDisclosureValue prior f (costs c) := by
  have hpost : posteriorReward prior f ∅ = 0 := by
    unfold posteriorReward
    simp_rw [hzero]
    exact FiniteDist.expect_const _ _
  change value (posteriorReward prior f) c ≤ prior.expect (fun ω => value (f ω) c)
  rw [value_zero_baseline (posteriorReward_valid prior hf) (posteriorReward_monotone prior hmono) hc hpost]
  simp_rw [value_zero_baseline (hf _) (hmono _) hc (hzero _)]
  apply max_le
  · exact prior.expect_nonneg (fun ω => le_max_left _ _)
  · have h := prior.expect_mono (fun ω => le_max_right (0 : ℝ) (f ω Finset.univ - c))
    rw [FiniteDist.expect_sub, FiniteDist.expect_const] at h
    exact h

theorem kernel_zero_baseline {Signal : Type*} [MeasurableSpace Signal] {prior : FiniteDist Ω}
    {f : Ω → Finset Unit → ℝ} {c : ℝ} (scheme : KernelContractScheme prior f (costs c) Signal)
    (hf : ∀ ω, ValidReward (f ω)) (hmono : ∀ ω, Monotone (f ω)) (hc : 0 ≤ c)
    (hzero : ∀ ω, f ω ∅ = 0) : scheme.utility ≤ fullDisclosureValue prior f (costs c) := by
  have h := scheme.all_or_nothing hf 1 (fun μ => by
    simpa using noDisclosure_le_full_of_zero_baseline μ hf hmono hc hzero)
  simpa using h

theorem mixed_kernel_zero_baseline {Signal : Type*} [MeasurableSpace Signal] {prior : FiniteDist Ω}
    {f : Ω → Finset Unit → ℝ} {c : ℝ} (scheme : Mixed.KernelContractScheme prior f (costs c) Signal)
    (hf : ∀ ω, ValidReward (f ω)) (hmono : ∀ ω, Monotone (f ω)) (hc : 0 ≤ c)
    (hzero : ∀ ω, f ω ∅ = 0) : scheme.utility ≤ Mixed.fullDisclosureValue prior f (costs c) := by
  have h := scheme.all_or_nothing hf 1 (fun μ => by
    rw [mixed_noDisclosure_eq μ hf hmono hc, mixed_fullDisclosure_eq μ hf hmono hc, one_mul]
    exact noDisclosure_le_full_of_zero_baseline μ hf hmono hc hzero)
  simpa using h

/-- Full revelation is itself a joint optimum when every baseline vanishes. -/
theorem full_optimal_of_zero_baseline [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (prior : FiniteDist Ω) (f : Ω → Finset Unit → ℝ) (c : ℝ)
    (hf : ∀ ω, ValidReward (f ω)) (hmono : ∀ ω, Monotone (f ω)) (hc : 0 ≤ c)
    (hzero : ∀ ω, f ω ∅ = 0) :
    ∃ full : KernelContractScheme prior f (costs c) Ω,
      full.kernel = (PosteriorScheme.full prior).toSignalKernel ∧
      full.utility = fullDisclosureValue prior f (costs c) ∧
      ∀ (Signal : Type*) [MeasurableSpace Signal] (scheme : KernelContractScheme prior f (costs c) Signal),
        scheme.utility ≤ full.utility := by
  obtain ⟨finite, hinfo, hvalue⟩ := fullDisclosure_attained prior f (costs c) hf hmono (fun _ => hc)
  refine ⟨finite.toKernelContract, ?_, ?_, ?_⟩
  · change finite.information.toSignalKernel = _
    rw [hinfo]
  · rw [ContractScheme.toKernelContract_utility, hvalue]
  · intro Signal _ scheme
    rw [ContractScheme.toKernelContract_utility, hvalue]
    exact kernel_zero_baseline scheme hf hmono hc hzero

theorem mixed_full_optimal_of_zero_baseline [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (prior : FiniteDist Ω) (f : Ω → Finset Unit → ℝ) (c : ℝ)
    (hf : ∀ ω, ValidReward (f ω)) (hmono : ∀ ω, Monotone (f ω)) (hc : 0 ≤ c)
    (hzero : ∀ ω, f ω ∅ = 0) :
    ∃ full : Mixed.KernelContractScheme prior f (costs c) Ω,
      full.kernel = (PosteriorScheme.full prior).toSignalKernel ∧
      full.utility = Mixed.fullDisclosureValue prior f (costs c) ∧
      ∀ (Signal : Type*) [MeasurableSpace Signal] (scheme : Mixed.KernelContractScheme prior f (costs c) Signal),
        scheme.utility ≤ full.utility := by
  obtain ⟨finite, hinfo, hvalue⟩ := Mixed.fullDisclosure_attained prior f (costs c) hf (fun _ => hc)
  refine ⟨finite.toKernelContract, ?_, ?_, ?_⟩
  · change finite.information.toSignalKernel = _
    rw [hinfo]
  · rw [Mixed.ContractScheme.toKernelContract_utility, hvalue]
  · intro Signal _ scheme
    rw [Mixed.ContractScheme.toKernelContract_utility, hvalue]
    exact mixed_kernel_zero_baseline scheme hf hmono hc hzero

end

end TransparencyLean.SingleAgent
