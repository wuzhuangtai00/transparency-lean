import TransparencyLean.Mixed.Rounding

/-! A single binary-action agent, represented by Unit. -/

namespace TransparencyLean.SingleAgent

open scoped BigOperators

noncomputable section

def reward (p₀ p₁ : ℝ) (S : Finset Unit) : ℝ := if () ∈ S then p₁ else p₀
def costs (c : ℝ) (_ : Unit) : ℝ := c
def value (f : Finset Unit → ℝ) (c : ℝ) : ℝ := statelessValue f (costs c)

theorem team_cases (S : Finset Unit) : S = ∅ ∨ S = Finset.univ := by
  by_cases h : () ∈ S
  · right
    ext i
    cases i
    simp [h]
  · left
    ext i
    cases i
    simp [h]

@[simp] theorem reward_empty (a b : ℝ) : reward a b ∅ = a := by simp [reward]
@[simp] theorem reward_univ (a b : ℝ) : reward a b Finset.univ = b := by simp [reward]

theorem reward_valid {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) : ValidReward (reward a b) := by
  intro S
  rcases team_cases S with rfl | rfl <;> simp only [reward_empty, reward_univ]
  · exact ⟨ha, hab.trans hb⟩
  · exact ⟨ha.trans hab, hb⟩

theorem reward_monotone {a b : ℝ} (hab : a ≤ b) : Monotone (reward a b) := by
  intro S T hST
  by_cases hS : () ∈ S
  · simp [reward, hS, hST hS]
  · by_cases hT : () ∈ T
    · simpa [reward, hS, hT] using hab
    · simp [reward, hS, hT]

theorem reward_eq (f : Finset Unit → ℝ) : reward (f ∅) (f Finset.univ) = f := by
  funext S
  rcases team_cases S with rfl | rfl <;> simp only [reward_empty, reward_univ]

theorem supermodular (f : Finset Unit → ℝ) : Supermodular f := by
  intro S T
  rcases team_cases S with rfl | rfl <;> rcases team_cases T with rfl | rfl <;> simp [add_comm]

theorem mixed_value_eq (f : Finset Unit → ℝ) (c : ℝ) (hf : ValidReward f)
    (hmono : Monotone f) (hc : 0 ≤ c) : Mixed.statelessValue f (costs c) = value f c :=
  Mixed.supermodular_value_eq_pure hf hmono (supermodular f) (fun _ => hc)

theorem baseline_le_value {f : Finset Unit → ℝ} (hf : ValidReward f) {c : ℝ} (hc : 0 ≤ c) :
    f ∅ ≤ value f c := by
  have h := utility_le_statelessValue hf zero_feasible (empty_zero_equilibrium f (costs c) (fun _ => hc))
  simpa using h

theorem value_le_effort {f : Finset Unit → ℝ} (hf : ValidReward f) (hmono : Monotone f)
    {c : ℝ} (hc : 0 ≤ c) : value f c ≤ f Finset.univ := by
  apply statelessValue_le (fun _ => hc)
  intro α S hα _
  have hnonneg := (hf S).1
  have hshare := (hα ()).1
  have hreward := hmono (Finset.subset_univ S)
  simp only [principalUtility, Fintype.sum_unique]
  change (1 - α ()) * f S ≤ _
  nlinarith

theorem grand_feasible {f : Finset Unit → ℝ} {c : ℝ} (hc : c ≤ f Finset.univ - f ∅) :
    FeasibleTeam f (costs c) Finset.univ := by
  intro i _
  cases i
  simpa [costs, Finset.univ_unique] using hc

theorem grand_incentive {f : Finset Unit → ℝ} {c : ℝ} {α : Unit → ℝ}
    (heq : IsEquilibrium f (costs c) α Finset.univ) : c ≤ α () * (f Finset.univ - f ∅) := by
  simpa [costs, Finset.univ_unique] using heq.1 () (Finset.mem_univ ())

@[simp] theorem minimum_empty_utility (f : Finset Unit → ℝ) (c : ℝ) :
    principalUtility f (minimumContract f (costs c) ∅) ∅ = f ∅ := by
  simp [principalUtility, minimumContract]

@[simp] theorem minimum_grand_utility (f : Finset Unit → ℝ) (c : ℝ) :
    principalUtility f (minimumContract f (costs c) Finset.univ) Finset.univ =
      (1 - c / (f Finset.univ - f ∅)) * f Finset.univ := by
  simp [principalUtility, minimumContract, costs, Finset.univ_unique]

theorem work_payoff_le_value {f : Finset Unit → ℝ} (hf : ValidReward f) (hmono : Monotone f)
    {c : ℝ} (hc : 0 ≤ c) (hfeas : c ≤ f Finset.univ - f ∅) :
    (1 - c / (f Finset.univ - f ∅)) * f Finset.univ ≤ value f c := by
  have hT := grand_feasible hfeas
  have h := utility_le_statelessValue hf (minimumContract_feasible hmono (fun _ => hc) hT)
    (minimumContract_equilibrium (fun _ => hc) hT)
  change principalUtility f (minimumContract f (costs c) Finset.univ) Finset.univ ≤ value f c at h
  rwa [minimum_grand_utility] at h

/-- The exact stateless optimum, including infeasible effort and zero marginal. -/
theorem value_formula {f : Finset Unit → ℝ} (hf : ValidReward f) (hmono : Monotone f)
    {c : ℝ} (hc : 0 ≤ c) :
    value f c = if c ≤ f Finset.univ - f ∅ then
      max (f ∅) ((1 - c / (f Finset.univ - f ∅)) * f Finset.univ) else f ∅ := by
  obtain ⟨S, hS, _, _, hvalue⟩ := statelessValue_attained hf hmono (fun _ : Unit => hc)
  change principalUtility f (minimumContract f (costs c) S) S = value f c at hvalue
  by_cases hfeas : c ≤ f Finset.univ - f ∅
  · rw [if_pos hfeas]
    apply le_antisymm
    · rcases team_cases S with rfl | rfl
      · rw [minimum_empty_utility] at hvalue
        rw [← hvalue]
        exact le_max_left _ _
      · rw [minimum_grand_utility] at hvalue
        rw [← hvalue]
        exact le_max_right _ _
    · exact max_le (baseline_le_value hf hc) (work_payoff_le_value hf hmono hc hfeas)
  · rw [if_neg hfeas]
    rcases team_cases S with rfl | rfl
    · simpa using hvalue.symm
    · have h := hS () (Finset.mem_univ ())
      simp only [costs, Finset.univ_unique, Finset.erase_singleton] at h
      exact False.elim (hfeas h)

theorem value_zero_cost {f : Finset Unit → ℝ} (hf : ValidReward f) (hmono : Monotone f) :
    value f 0 = f Finset.univ := by
  rw [value_formula hf hmono (le_refl 0), if_pos (sub_nonneg.mpr (hmono (Finset.empty_subset _)))]
  simp [max_eq_right (hmono (Finset.empty_subset _))]

theorem value_eq_baseline_of_cost_ge_delta {f : Finset Unit → ℝ} (hf : ValidReward f)
    (hmono : Monotone f) {c : ℝ} (hc : 0 ≤ c) (hcost : f Finset.univ - f ∅ ≤ c) :
    value f c = f ∅ := by
  rw [value_formula hf hmono hc]
  split_ifs with hfeas
  · have heq : c = f Finset.univ - f ∅ := le_antisymm hfeas hcost
    by_cases hz : c = 0
    · have hp : f Finset.univ = f ∅ := by linarith
      simp only [hz, hp, zero_div, sub_zero, one_mul, max_self]
    · rw [← heq, div_self hz]
      simp [max_eq_left (hf ∅).1]
  · rfl

theorem value_high_cost {f : Finset Unit → ℝ} (hf : ValidReward f) (hmono : Monotone f)
    {c : ℝ} (hc : 1 ≤ c) : value f c = f ∅ :=
  value_eq_baseline_of_cost_ge_delta hf hmono (by linarith)
    (by have h₀ := (hf ∅).1; have h₁ := (hf Finset.univ).2; linarith)

/-- With zero baseline, full surplus is extracted whenever effort is worthwhile. -/
theorem value_zero_baseline {f : Finset Unit → ℝ} (hf : ValidReward f) (hmono : Monotone f)
    {c : ℝ} (hc : 0 ≤ c) (hzero : f ∅ = 0) : value f c = max 0 (f Finset.univ - c) := by
  rw [value_formula hf hmono hc, hzero, sub_zero]
  split_ifs with hfeas
  · by_cases hb : f Finset.univ = 0
    · have hc0 : c = 0 := le_antisymm (by rw [hb] at hfeas; exact hfeas) hc
      simp only [hb, hc0, zero_div, one_mul, sub_zero, sub_self, max_self, mul_zero]
    · have hid : (1 - c / f Finset.univ) * f Finset.univ = f Finset.univ - c := by
        linear_combination - (div_mul_cancel₀ c hb)
      rw [hid]
  · rw [max_eq_left (by linarith)]

end

end TransparencyLean.SingleAgent
