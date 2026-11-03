import TransparencyLean.SingleAgent.Transparency
import TransparencyLean.SingleAgent.TightnessAlgebra

/-! The paper's two-state tightness family, with k = X = 2 and 0 < c <= 1/4. -/

namespace TransparencyLean.SingleAgent.Tightness

noncomputable section

def prior (c : ℝ) (hc : 0 < c) (hcb : c ≤ 1 / 4) : FiniteDist Bool where
  prob ω := if ω then 1 - 2 * c else 2 * c
  nonneg ω := by cases ω <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith
  sum_eq_one := by simp

def stateReward (c : ℝ) (ω : Bool) : Finset Unit → ℝ :=
  if ω then reward (2 * c) (4 * c) else reward 0 1

theorem state_valid {c : ℝ} (hc : 0 < c) (hcb : c ≤ 1 / 4) (ω : Bool) :
    ValidReward (stateReward c ω) := by
  cases ω
  · exact reward_valid (by norm_num) (by norm_num) (by norm_num)
  · exact reward_valid (by linarith) (by linarith) (by linarith)

theorem state_monotone {c : ℝ} (hc : 0 < c) (ω : Bool) : Monotone (stateReward c ω) := by
  cases ω
  · exact reward_monotone (by norm_num)
  · exact reward_monotone (by linarith)

theorem revealed_value {c : ℝ} (hc : 0 < c) (hcb : c ≤ 1 / 4) (ω : Bool) :
    value (stateReward c ω) c = if ω then 2 * c else 1 - c := by
  rw [value_formula (state_valid hc hcb ω) (state_monotone hc ω) (le_of_lt hc)]
  cases ω
  · change (if c ≤ reward 0 1 Finset.univ - reward 0 1 ∅ then
        max (reward 0 1 ∅) ((1 - c / (reward 0 1 Finset.univ - reward 0 1 ∅)) * reward 0 1 Finset.univ)
        else reward 0 1 ∅) = 1 - c
    simp only [reward_empty, reward_univ, sub_zero, div_one, mul_one]
    rw [if_pos (by linarith), max_eq_right (by linarith)]
  · change (if c ≤ reward (2 * c) (4 * c) Finset.univ - reward (2 * c) (4 * c) ∅ then
        max (reward (2 * c) (4 * c) ∅)
          ((1 - c / (reward (2 * c) (4 * c) Finset.univ - reward (2 * c) (4 * c) ∅)) *
            reward (2 * c) (4 * c) Finset.univ) else reward (2 * c) (4 * c) ∅) = 2 * c
    simp only [reward_empty, reward_univ]
    rw [if_pos (by linarith)]
    have hd : 4 * c - 2 * c ≠ 0 := ne_of_gt (by linarith)
    have heq : (1 - c / (4 * c - 2 * c)) * (4 * c) = 2 * c := by field_simp; ring
    rw [heq, max_self]

theorem mean_reward {c : ℝ} (hc : 0 < c) (hcb : c ≤ 1 / 4) :
    posteriorReward (prior c hc hcb) (stateReward c) = reward (2 * c - 4 * c ^ 2) (6 * c - 8 * c ^ 2) := by
  funext S
  rcases team_cases S with rfl | rfl <;>
    simp [posteriorReward, FiniteDist.expect, prior, stateReward, reward] <;> ring

theorem full_disclosure_value {c : ℝ} (hc : 0 < c) (hcb : c ≤ 1 / 4) :
    fullDisclosureValue (prior c hc hcb) (stateReward c) (costs c) = fullValue c := by
  change (prior c hc hcb).expect (fun ω => value (stateReward c ω) c) = _
  simp_rw [revealed_value hc hcb]
  simp [FiniteDist.expect, prior, fullValue]
  ring

theorem no_disclosure_value {c : ℝ} (hc : 0 < c) (hcb : c ≤ 1 / 4) :
    noDisclosureValue (prior c hc hcb) (stateReward c) (costs c) = noValue c := by
  change value (posteriorReward (prior c hc hcb) (stateReward c)) c = _
  rw [value_formula (posteriorReward_valid _ (state_valid hc hcb))
    (posteriorReward_monotone _ (state_monotone hc)) (le_of_lt hc), mean_reward]
  simp only [reward_empty, reward_univ]
  have hfeas : c ≤ (6 * c - 8 * c ^ 2) - (2 * c - 4 * c ^ 2) := by
    nlinarith [mul_nonneg (le_of_lt hc) (show 0 ≤ 3 - 4 * c by linarith)]
  rw [if_pos hfeas, work_value hc hcb, max_eq_right (baseline_le_noValue hc hcb)]

theorem ratio_exact {c : ℝ} (hc : 0 < c) (hcb : c ≤ 1 / 4) :
    noDisclosureValue (prior c hc hcb) (stateReward c) (costs c) /
      fullDisclosureValue (prior c hc hcb) (stateReward c) (costs c) = ratio c := by
  rw [no_disclosure_value hc hcb, full_disclosure_value hc hcb]
  exact ratio_identity hc hcb

theorem mixed_ratio_exact {c : ℝ} (hc : 0 < c) (hcb : c ≤ 1 / 4) :
    Mixed.noDisclosureValue (prior c hc hcb) (stateReward c) (costs c) /
      Mixed.fullDisclosureValue (prior c hc hcb) (stateReward c) (costs c) = ratio c := by
  rw [mixed_noDisclosure_eq _ (state_valid hc hcb) (state_monotone hc) (le_of_lt hc),
    mixed_fullDisclosure_eq _ (state_valid hc hcb) (state_monotone hc) (le_of_lt hc)]
  exact ratio_exact hc hcb

end

end TransparencyLean.SingleAgent.Tightness
