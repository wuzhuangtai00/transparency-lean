import TransparencyLean.Mixed.Transparency

/-! For supermodular (hence also additive) rewards, mixing cannot improve value. -/

namespace TransparencyLean.Mixed

open scoped BigOperators

noncomputable section

variable {Agent : Type*} [Fintype Agent] [DecidableEq Agent]

def support (x : Agent → ℝ) : Finset Agent := Finset.univ.filter (fun i => 0 < x i)

omit [DecidableEq Agent] in
@[simp] theorem mem_support (x : Agent → ℝ) (i : Agent) : i ∈ support x ↔ 0 < x i := by
  simp [support]

theorem mask_support {x : Agent → ℝ} (hx : ValidProfile x) : mask x (support x) = x := by
  ext i
  by_cases hi : 0 < x i
  · simp [mask, hi]
  · have hz : x i = 0 := le_antisymm (le_of_not_gt hi) (hx i).1
    simp [mask, hi, hz]

theorem extension_le_support {f : Finset Agent → ℝ} (hmono : Monotone f)
    {x : Agent → ℝ} (hx : ValidProfile x) : extension f x ≤ f (support x) := by
  have heq : extension f x = auxiliary f x (support x) := by rw [← extension_mask, mask_support hx]
  rw [heq]
  simpa using sample_mono hx (support x) (g := fun _ => f (support x)) (fun R hR => hmono hR)

omit [Fintype Agent] in
theorem removalMarginal_monotone {f : Finset Agent → ℝ} (hsuper : Supermodular f)
    {S T : Finset Agent} (hST : S ⊆ T) {i : Agent} (hi : i ∈ S) :
    removalMarginal f S i ≤ removalMarginal f T i := by
  have hneg : Submodular (fun R => -f R) := by
    intro A B
    have h := hsuper A B
    dsimp
    linarith
  have h := removalMarginal_antitone hneg hST hi
  unfold removalMarginal at h ⊢
  dsimp only at h
  linarith

theorem marginal_le_support {f : Finset Agent → ℝ} (hsuper : Supermodular f)
    {x : Agent → ℝ} (hx : ValidProfile x) {i : Agent} (hi : i ∈ support x) :
    marginal f x i ≤ f (support x) - f ((support x).erase i) := by
  have heq : marginal f x i =
      sample x ((support x).erase i) (fun R => f (insert i R) - f R) := by
    rw [← marginal_mask, mask_support hx]
  rw [heq]
  have h : sample x ((support x).erase i) (fun R => f (insert i R) - f R) ≤
      sample x ((support x).erase i) (fun _ => f (support x) - f ((support x).erase i)) := by
    apply sample_mono hx
    intro R hR
    have hiR : i ∉ R := fun h => Finset.not_mem_erase i (support x) (hR h)
    have hsub : insert i R ⊆ support x := Finset.insert_subset hi
      (hR.trans (Finset.erase_subset _ _))
    have hm := removalMarginal_monotone hsuper hsub (Finset.mem_insert_self i R)
    simpa [removalMarginal, Finset.erase_insert hiR] using hm
  simpa using h

/-- Every mixed utility is bounded by a pure optimum, including contracts
whose total share exceeds one. Such contracts are handled by their sign. -/
theorem utility_le_pure_of_supermodular {f : Finset Agent → ℝ}
    (hf : ValidReward f) (hmono : Monotone f) (hsuper : Supermodular f)
    {c α x : Agent → ℝ} (hc : ∀ i, 0 ≤ c i) (hα : FeasibleContract α)
    (hx : ValidProfile x) (heq : IsMixedEquilibrium f c α x) :
    utility f α x ≤ TransparencyLean.statelessValue f c := by
  have hF0 : 0 ≤ extension f x := (sample_bounds hx Finset.univ hf).1
  by_cases hbudget : ∑ i, α i ≤ 1
  · let S := support x
    let β := mask α S
    have hβ : FeasibleContract β := mask_valid hα S
    have hteam : IsEquilibrium f c β S := by
      constructor
      · intro i hi
        have hwork := heq.1 i ((mem_support x i).mp hi)
        have hm := mul_le_mul_of_nonneg_left (marginal_le_support hsuper hx hi) (hα i).1
        simpa [β, mask, hi] using hwork.trans hm
      · intro i hi
        simpa [β, mask, hi] using hc i
    have hsum : ∑ i, β i ≤ ∑ i, α i := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ S
      · simp [β, mask, hi]
      · simpa [β, mask, hi] using (hα i).1
    have hu : utility f α x ≤ principalUtility f β S := by
      have hF := extension_le_support hmono hx
      have h₁ := mul_le_mul_of_nonneg_left hF (sub_nonneg.mpr hbudget)
      have h₂ := mul_le_mul_of_nonneg_right (sub_le_sub_left hsum 1) (hf S).1
      exact h₁.trans h₂
    exact hu.trans (TransparencyLean.utility_le_statelessValue hf hβ hteam)
  · have hu : utility f α x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
      (by linarith : 1 - ∑ i, α i ≤ 0) hF0
    exact hu.trans (TransparencyLean.statelessValue_nonneg hf hc)

theorem supermodular_value_eq_pure {f : Finset Agent → ℝ} (hf : ValidReward f)
    (hmono : Monotone f) (hsuper : Supermodular f) {c : Agent → ℝ} (hc : ∀ i, 0 ≤ c i) :
    statelessValue f c = TransparencyLean.statelessValue f c := by
  apply le_antisymm _ (pure_le_mixed hf hc)
  exact statelessValue_le hc (fun _ _ hα hx heq => utility_le_pure_of_supermodular hf hmono hsuper hc hα hx heq)

theorem additive_value_eq_pure {f : Finset Agent → ℝ} (hf : ValidReward f)
    (hadd : IsAdditiveReward f) {c : Agent → ℝ} (hc : ∀ i, 0 ≤ c i) :
    statelessValue f c = TransparencyLean.statelessValue f c := by
  obtain ⟨w, rfl⟩ := hadd
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    simpa [additiveReward] using (hf {i}).1
  exact supermodular_value_eq_pure hf (additiveReward_monotone hw)
    (fun S T => le_of_eq (additiveReward_modular w S T).symm) hc

variable {Ω : Type*} [Fintype Ω]

theorem supermodular_noDisclosure_eq_pure (prior : FiniteDist Ω)
    {f : Ω → Finset Agent → ℝ} {c : Agent → ℝ}
    (hf : ∀ ω, ValidReward (f ω)) (hmono : ∀ ω, Monotone (f ω))
    (hsuper : ∀ ω, Supermodular (f ω)) (hc : ∀ i, 0 ≤ c i) :
    noDisclosureValue prior f c = TransparencyLean.noDisclosureValue prior f c :=
  supermodular_value_eq_pure (posteriorReward_valid prior hf) (posteriorReward_monotone prior hmono)
    (posteriorReward_supermodular prior hsuper) hc

theorem supermodular_fullDisclosure_eq_pure (prior : FiniteDist Ω)
    {f : Ω → Finset Agent → ℝ} {c : Agent → ℝ}
    (hf : ∀ ω, ValidReward (f ω)) (hmono : ∀ ω, Monotone (f ω))
    (hsuper : ∀ ω, Supermodular (f ω)) (hc : ∀ i, 0 ≤ c i) :
    fullDisclosureValue prior f c = TransparencyLean.fullDisclosureValue prior f c := by
  unfold fullDisclosureValue TransparencyLean.fullDisclosureValue
  simp_rw [supermodular_value_eq_pure (hf _) (hmono _) (hsuper _) hc]

theorem additive_fullDisclosure_eq_pure (prior : FiniteDist Ω)
    {f : Ω → Finset Agent → ℝ} {c : Agent → ℝ}
    (hf : ∀ ω, ValidReward (f ω)) (hadd : ∀ ω, IsAdditiveReward (f ω)) (hc : ∀ i, 0 ≤ c i) :
    fullDisclosureValue prior f c = TransparencyLean.fullDisclosureValue prior f c := by
  unfold fullDisclosureValue TransparencyLean.fullDisclosureValue
  simp_rw [additive_value_eq_pure (hf _) (hadd _) hc]

end

end TransparencyLean.Mixed
