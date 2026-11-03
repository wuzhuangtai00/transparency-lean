import TransparencyLean.Submodular.Potential
import TransparencyLean.Information.Contracts

namespace TransparencyLean

open scoped BigOperators

noncomputable section

variable {Ω Agent : Type*} [Fintype Ω] [Fintype Agent] [DecidableEq Agent]

omit [Fintype Agent] in
theorem expect_removalMarginal (prior : FiniteDist Ω) (f : Ω → Finset Agent → ℝ)
    (S : Finset Agent) (i : Agent) :
    prior.expect (fun ω => removalMarginal (f ω) S i) =
      removalMarginal (posteriorReward prior f) S i := by
  exact prior.expect_sub (fun ω => f ω S) (fun ω => f ω (S.erase i))

/-- The no-disclosure comparison underlying paper Theorem 4.1. Costs may
vanish and rewards may have a positive value at the empty team. -/
theorem noDisclosure_le_four_thirds (prior : FiniteDist Ω)
    {f : Ω → Finset Agent → ℝ} {c : Agent → ℝ}
    (hf : ∀ ω, ValidReward (f ω)) (hmono : ∀ ω, Monotone (f ω))
    (hsub : ∀ ω, Submodular (f ω)) (hc : ∀ i, 0 ≤ c i) :
    noDisclosureValue prior f c ≤ (4 / 3) * fullDisclosureValue prior f c := by
  classical
  have hF : 0 ≤ fullDisclosureValue prior f c :=
    prior.expect_nonneg (fun ω => statelessValue_nonneg (hf ω) hc)
  by_cases hN : noDisclosureValue prior f c ≤ 0
  · linarith
  let g := posteriorReward prior f
  have hg : ValidReward g := posteriorReward_valid prior hf
  have hgm : Monotone g := posteriorReward_monotone prior hmono
  have hgs : Submodular g := posteriorReward_submodular prior hsub
  obtain ⟨S, hteam, _, _, hvalue⟩ := statelessValue_attained hg hgm hc
  let P := S.filter (fun i => 0 < c i)
  let Z := S \ P
  let d := removalMarginal g S
  let k := fun i => c i / d i
  have hPS : P ⊆ S := Finset.filter_subset _ _
  have hunion : Z ∪ P = S := Finset.sdiff_union_of_subset hPS
  have hdis : Disjoint Z P := Finset.sdiff_disjoint
  have hfree : ∀ i ∈ Z, c i = 0 := by
    intro i hi
    obtain ⟨hiS, hiP⟩ := Finset.mem_sdiff.mp hi
    have hn : ¬0 < c i := fun h => hiP (Finset.mem_filter.mpr ⟨hiS, h⟩)
    exact le_antisymm (le_of_not_gt hn) (hc i)
  have hpaid : ∀ i ∈ P, 0 < k i ∧ 0 < d i ∧ c i = k i * d i := by
    intro i hi
    obtain ⟨hiS, hci⟩ := Finset.mem_filter.mp hi
    have hd : 0 < d i := hci.trans_le (hteam i hiS)
    exact ⟨div_pos hci hd, hd, (div_mul_cancel₀ (c i) (ne_of_gt hd)).symm⟩
  have hsum : (∑ i, minimumContract g c S i) = ∑ i ∈ P, k i := by
    calc
      (∑ i, minimumContract g c S i) = ∑ i ∈ P, minimumContract g c S i := by
        symm
        apply Finset.sum_subset (Finset.subset_univ P)
        intro i _ hiP
        by_cases hiS : i ∈ S
        · have hn : ¬0 < c i := fun h => hiP (Finset.mem_filter.mpr ⟨hiS, h⟩)
          have hci : c i = 0 := le_antisymm (le_of_not_gt hn) (hc i)
          simp [minimumContract, hci]
        · simp [minimumContract, hiS]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [minimumContract, hPS hi, if_true]
        rfl
  have hutility : (1 - ∑ i ∈ P, k i) * g S = noDisclosureValue prior f c := by
    simpa only [principalUtility, hsum] using hvalue
  have hbudget : ∑ i ∈ P, k i ≤ 1 := by
    by_contra hn
    have hh := mul_nonpos_of_nonpos_of_nonneg
      (show 1 - ∑ i ∈ P, k i ≤ 0 by linarith) (hg S).1
    rw [hutility] at hh
    exact hN hh
  have hsumd : ∑ i ∈ P, d i ≤ g S := by
    have h1 : ∑ i ∈ P, d i ≤ ∑ i ∈ S, d i :=
      Finset.sum_le_sum_of_subset_of_nonneg hPS (fun i _ _ => removalMarginal_nonneg hgm S i)
    have h2 : ∑ i ∈ S, d i ≤ g S - g ∅ := sum_removalMarginal_le hgs S
    linarith [(hg ∅).1]
  have hstate : ∀ ω,
      (1 - ∑ i ∈ P, k i) * (f ω S - (1 / 4) * ∑ i ∈ P, d i) +
        ∑ i ∈ P, k i * (removalMarginal (f ω) S i - d i) ≤ statelessValue (f ω) c := by
    intro ω
    simpa only [hunion] using potential_with_free_team (hf ω) (hmono ω) (hsub ω)
      hc Z P hdis hfree hpaid hbudget
  have hmean := prior.expect_mono hstate
  rw [FiniteDist.expect_add, FiniteDist.expect_mul, FiniteDist.expect_sub,
    FiniteDist.expect_const, FiniteDist.expect_finset_sum] at hmean
  have hzero : (∑ i ∈ P, prior.expect
      (fun ω => k i * (removalMarginal (f ω) S i - d i))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [FiniteDist.expect_mul, FiniteDist.expect_sub, FiniteDist.expect_const,
      expect_removalMarginal]
    change k i * (d i - d i) = 0
    ring
  rw [hzero, add_zero] at hmean
  change (1 - ∑ i ∈ P, k i) * (g S - (1 / 4) * ∑ i ∈ P, d i) ≤
    fullDisclosureValue prior f c at hmean
  have hquarter : (3 / 4 : ℝ) * g S ≤ g S - (1 / 4) * ∑ i ∈ P, d i := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hquarter (sub_nonneg.mpr hbudget)
  nlinarith only [hscaled, hmean, hutility]

/-- Paper Theorem 4.1, upper-bound direction for every finite public signaling
scheme and its chosen pure equilibria. Together with `fullDisclosure_attained`,
the right side is the utility of an implementable full-disclosure scheme. -/
theorem ContractScheme.submodular_four_thirds {Signal : Type*} [Fintype Signal]
    {prior : FiniteDist Ω} {f : Ω → Finset Agent → ℝ} {c : Agent → ℝ}
    (scheme : ContractScheme prior f c Signal)
    (hf : ∀ ω, ValidReward (f ω)) (hmono : ∀ ω, Monotone (f ω))
    (hsub : ∀ ω, Submodular (f ω)) (hc : ∀ i, 0 ≤ c i) :
    scheme.utility ≤ (4 / 3) * fullDisclosureValue prior f c :=
  scheme.all_or_nothing hf (4 / 3)
    (fun μ => noDisclosure_le_four_thirds μ hf hmono hsub hc)

/-- Equivalent form without a quotient or a positive-value assumption. -/
theorem ContractScheme.submodular_three_mul_le_four_mul {Signal : Type*} [Fintype Signal]
    {prior : FiniteDist Ω} {f : Ω → Finset Agent → ℝ} {c : Agent → ℝ}
    (scheme : ContractScheme prior f c Signal)
    (hf : ∀ ω, ValidReward (f ω)) (hmono : ∀ ω, Monotone (f ω))
    (hsub : ∀ ω, Submodular (f ω)) (hc : ∀ i, 0 ≤ c i) :
    3 * scheme.utility ≤ 4 * fullDisclosureValue prior f c := by
  linarith [scheme.submodular_four_thirds hf hmono hsub hc]

end

end TransparencyLean
