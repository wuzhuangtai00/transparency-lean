import TransparencyLean.Model.MinimumPayments

namespace TransparencyLean

open scoped BigOperators

noncomputable section

variable {Agent : Type*} [Fintype Agent] [DecidableEq Agent]

def additiveReward (w : Agent → ℝ) (S : Finset Agent) : ℝ := ∑ i ∈ S, w i

def IsAdditiveReward (f : Finset Agent → ℝ) : Prop := ∃ w, f = additiveReward w

omit [Fintype Agent] [DecidableEq Agent] in
theorem additiveReward_monotone {w : Agent → ℝ} (hw : ∀ i, 0 ≤ w i) :
    Monotone (additiveReward w) := by
  intro S T hST
  exact Finset.sum_le_sum_of_subset_of_nonneg hST (fun i _ _ => hw i)

omit [DecidableEq Agent] in
theorem additiveReward_valid {w : Agent → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i ≤ 1) : ValidReward (additiveReward w) := by
  intro S
  exact ⟨Finset.sum_nonneg (fun i _ => hw i),
    (additiveReward_monotone hw (Finset.subset_univ S)).trans hsum⟩

omit [Fintype Agent] in
theorem additiveReward_modular (w : Agent → ℝ) (S T : Finset Agent) :
    additiveReward w (S ∪ T) + additiveReward w (S ∩ T) =
      additiveReward w S + additiveReward w T := Finset.sum_union_inter

omit [Fintype Agent] in
theorem additiveReward_submodular (w : Agent → ℝ) : Submodular (additiveReward w) :=
  fun S T => le_of_eq (additiveReward_modular w S T)

omit [Fintype Agent] in
theorem additiveReward_marginal (w : Agent → ℝ) (S : Finset Agent) {i : Agent} (hi : i ∈ S) :
    additiveReward w S - additiveReward w (S.erase i) = w i := by
  have h := Finset.sum_erase_add S w hi
  unfold additiveReward
  linarith

omit [Fintype Agent] in
theorem additiveReward_feasibleTeam {w c : Agent → ℝ} (h : ∀ i, c i ≤ w i) (S : Finset Agent) :
    FeasibleTeam (additiveReward w) c S := by
  intro i hi
  rw [additiveReward_marginal w S hi]
  exact h i

theorem additive_minimum_total (w c : Agent → ℝ) (S : Finset Agent) :
    (∑ i, minimumContract (additiveReward w) c S i) = ∑ i ∈ S, c i / w i := by
  calc
    _ = ∑ i ∈ S, minimumContract (additiveReward w) c S i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro i _ hi
      simp [minimumContract, hi]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [minimumContract, hi, if_true, additiveReward_marginal w S hi]

theorem additive_minimum_utility (w c : Agent → ℝ) (S : Finset Agent) :
    principalUtility (additiveReward w) (minimumContract (additiveReward w) c S) S =
      (1 - ∑ i ∈ S, c i / w i) * ∑ i ∈ S, w i := by
  rw [principalUtility, additive_minimum_total]
  rfl

/-- A finite-team maximization certificate for an additive instance. -/
theorem additive_value_eq {w c : Agent → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i ≤ 1) (hc : ∀ i, 0 ≤ c i) (hfeas : ∀ i, c i ≤ w i)
    (T : Finset Agent) (v : ℝ)
    (hupper : ∀ S : Finset Agent, (1 - ∑ i ∈ S, c i / w i) * ∑ i ∈ S, w i ≤ v)
    (hvalue : (1 - ∑ i ∈ T, c i / w i) * ∑ i ∈ T, w i = v) :
    statelessValue (additiveReward w) c = v := by
  have hf := additiveReward_valid hw hsum
  apply le_antisymm
  · apply statelessValue_le hc
    intro α S hα hS
    have h := minimumContract_utility_ge hf hc hα hS
    rw [additive_minimum_utility] at h
    exact h.trans (hupper S)
  · have hT := additiveReward_feasibleTeam hfeas T
    have h := utility_le_statelessValue hf
      (minimumContract_feasible (additiveReward_monotone hw) hc hT)
      (minimumContract_equilibrium hc hT)
    rwa [additive_minimum_utility, hvalue] at h

omit [Fintype Agent] in
/-- Sum of one distinguished agent's weight and a common weight for everyone else. -/
theorem sum_one_special (S : Finset Agent) (ω : Agent) (a b : ℝ) :
    (∑ i ∈ S, if i = ω then a else b) =
      (if ω ∈ S then a else 0) + (S.erase ω).card * b := by
  have hrest : (∑ i ∈ S.erase ω, if i = ω then a else b) = (S.erase ω).card * b := by
    simp only [Finset.sum_ite_of_false (fun i hi => (Finset.mem_erase.mp hi).1)]
    simp
  by_cases hω : ω ∈ S
  · have h := Finset.sum_erase_add S (fun i => if i = ω then a else b) hω
    rw [hrest] at h
    simpa [hω, add_comm] using h.symm
  · rw [Finset.erase_eq_of_not_mem hω] at hrest
    simpa [hω, Finset.erase_eq_of_not_mem hω] using hrest

end

end TransparencyLean
