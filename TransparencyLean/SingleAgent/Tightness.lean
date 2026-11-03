import TransparencyLean.SingleAgent.TightnessInstance

/-! Convergence and strict lower-factor counterexamples for Theorem B.1. -/

namespace TransparencyLean.SingleAgent.Tightness

open scoped Topology
open Filter

noncomputable section

def smallCost (n : ℕ) : ℝ := 1 / ((n : ℝ) + 4)

theorem smallCost_pos (n : ℕ) : 0 < smallCost n := by unfold smallCost; positivity

theorem smallCost_le (n : ℕ) : smallCost n ≤ 1 / 4 := by
  unfold smallCost
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < n + 4) (by norm_num : (0 : ℝ) < 4)).mpr
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

def familyRatio (n : ℕ) : ℝ :=
  noDisclosureValue (prior (smallCost n) (smallCost_pos n) (smallCost_le n)) (stateReward (smallCost n)) (costs (smallCost n)) /
    fullDisclosureValue (prior (smallCost n) (smallCost_pos n) (smallCost_le n)) (stateReward (smallCost n)) (costs (smallCost n))

theorem familyRatio_eq (n : ℕ) : familyRatio n = ratio (smallCost n) :=
  ratio_exact (smallCost_pos n) (smallCost_le n)

/-- The actual benchmark ratios approach 9/8 along valid finite instances. -/
theorem family_ratio_tendsto : Tendsto familyRatio atTop (𝓝 (9 / 8)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
  refine ⟨k, ?_⟩
  intro n hn
  have hkn : (k : ℝ) < n + 4 := by
    have h : (k : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hscale : 1 < ((n : ℝ) + 4) * ε := (div_lt_iff₀ hε).mp (hk.trans hkn)
  have hsmall : smallCost n < ε := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < n + 4)).mpr
    linarith
  obtain ⟨hlo, hhi⟩ := ratio_gap_bounds (smallCost_pos n) (smallCost_le n)
  rw [familyRatio_eq, Real.dist_eq, abs_of_nonpos (by linarith : ratio (smallCost n) - 9 / 8 ≤ 0)]
  linarith

theorem mixed_family_ratio_tendsto : Tendsto (fun n : ℕ =>
    Mixed.noDisclosureValue (prior (smallCost n) (smallCost_pos n) (smallCost_le n))
        (stateReward (smallCost n)) (costs (smallCost n)) /
      Mixed.fullDisclosureValue (prior (smallCost n) (smallCost_pos n) (smallCost_le n))
        (stateReward (smallCost n)) (costs (smallCost n))) atTop (𝓝 (9 / 8)) := by
  have heq : (fun n : ℕ =>
      Mixed.noDisclosureValue (prior (smallCost n) (smallCost_pos n) (smallCost_le n))
          (stateReward (smallCost n)) (costs (smallCost n)) /
        Mixed.fullDisclosureValue (prior (smallCost n) (smallCost_pos n) (smallCost_le n))
          (stateReward (smallCost n)) (costs (smallCost n))) = familyRatio := by
    funext n
    rw [mixed_ratio_exact, familyRatio_eq]
  rw [heq]
  exact family_ratio_tendsto

theorem exists_ratio_gt (β : ℝ) (hβ : β < 9 / 8) : ∃ n : ℕ, β < ratio (smallCost n) := by
  have h := ((tendsto_order.mp family_ratio_tendsto).1 β hβ).exists
  simpa only [familyRatio_eq] using h

theorem opaque_scheme {c : ℝ} (hc : 0 < c) (hcb : c ≤ 1 / 4) :
    ∃ hidden : KernelContractScheme (prior c hc hcb) (stateReward c) (costs c) Unit,
      hidden.kernel = (PosteriorScheme.uninformative (prior c hc hcb)).toSignalKernel ∧
      hidden.utility = noValue c := by
  obtain ⟨finite, hinfo, hu⟩ := noDisclosure_attained (prior c hc hcb) (stateReward c) (costs c)
    (state_valid hc hcb) (state_monotone hc) (fun _ => le_of_lt hc)
  refine ⟨finite.toKernelContract, ?_, ?_⟩
  · change finite.information.toSignalKernel = _
    rw [hinfo]
  · rw [ContractScheme.toKernelContract_utility, hu, no_disclosure_value hc hcb]

/-- Every factor below 9/8 fails on a valid two-state, one-agent instance. -/
theorem no_better_factor (β : ℝ) (hβ : β < 9 / 8) :
    ∃ (c : ℝ) (hc : 0 < c) (hcb : c ≤ 1 / 4),
      (∀ ω, ValidReward (stateReward c ω) ∧ Monotone (stateReward c ω)) ∧
      ∃ hidden : KernelContractScheme (prior c hc hcb) (stateReward c) (costs c) Unit,
        hidden.kernel = (PosteriorScheme.uninformative (prior c hc hcb)).toSignalKernel ∧
        0 < fullDisclosureValue (prior c hc hcb) (stateReward c) (costs c) ∧
        β * fullDisclosureValue (prior c hc hcb) (stateReward c) (costs c) < hidden.utility := by
  obtain ⟨n, hn⟩ := exists_ratio_gt β hβ
  let c := smallCost n
  have hc : 0 < c := smallCost_pos n
  have hcb : c ≤ 1 / 4 := smallCost_le n
  obtain ⟨hidden, hkernel, hvalue⟩ := opaque_scheme hc hcb
  refine ⟨c, hc, hcb, fun ω => ⟨state_valid hc hcb ω, state_monotone hc ω⟩,
    hidden, hkernel, ?_, ?_⟩
  · rw [full_disclosure_value hc hcb]
    exact fullValue_pos hc hcb
  · rw [full_disclosure_value hc hcb, hvalue]
    change β < ratio c at hn
    rw [← ratio_identity hc hcb] at hn
    exact (lt_div_iff₀ (fullValue_pos hc hcb)).mp hn

/-- Sharpness persists when both information benchmarks optimize over mixing. -/
theorem mixed_no_better_factor (β : ℝ) (hβ : β < 9 / 8) :
    ∃ (c : ℝ) (hc : 0 < c) (hcb : c ≤ 1 / 4),
      (∀ ω, ValidReward (stateReward c ω) ∧ Monotone (stateReward c ω)) ∧
      ∃ hidden : Mixed.KernelContractScheme (prior c hc hcb) (stateReward c) (costs c) Unit,
        hidden.kernel = (PosteriorScheme.uninformative (prior c hc hcb)).toSignalKernel ∧
        0 < Mixed.fullDisclosureValue (prior c hc hcb) (stateReward c) (costs c) ∧
        β * Mixed.fullDisclosureValue (prior c hc hcb) (stateReward c) (costs c) < hidden.utility := by
  obtain ⟨c, hc, hcb, hf, hidden, hk, hpos, hstrict⟩ := no_better_factor β hβ
  refine ⟨c, hc, hcb, hf, Mixed.KernelContractScheme.ofPure hidden, hk, ?_, ?_⟩
  · rwa [mixed_fullDisclosure_eq _ (state_valid hc hcb) (state_monotone hc) (le_of_lt hc)]
  · rwa [mixed_fullDisclosure_eq _ (state_valid hc hcb) (state_monotone hc) (le_of_lt hc),
      Mixed.KernelContractScheme.ofPure_utility]

end

end TransparencyLean.SingleAgent.Tightness
