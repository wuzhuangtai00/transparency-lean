import Mathlib.Tactic

/-! Exact algebra for the paper's k = X = 2 single-agent tightness family. -/

namespace TransparencyLean.SingleAgent.Tightness

noncomputable section

def noValue (c : ℝ) : ℝ := c * (3 - 4 * c) ^ 2 / (2 * (1 - c))
def fullValue (c : ℝ) : ℝ := 2 * c * (2 - 3 * c)
def ratio (c : ℝ) : ℝ := (3 - 4 * c) ^ 2 / (4 * (1 - c) * (2 - 3 * c))

theorem work_value {c : ℝ} (hc : 0 < c) (hcb : c ≤ 1 / 4) :
    (1 - c / ((6 * c - 8 * c ^ 2) - (2 * c - 4 * c ^ 2))) * (6 * c - 8 * c ^ 2) = noValue c := by
  have hd : (6 * c - 8 * c ^ 2) - (2 * c - 4 * c ^ 2) ≠ 0 := by
    have h : 0 < 4 * c * (1 - c) := mul_pos (by positivity) (by linarith)
    nlinarith
  have h₁ : 1 - c ≠ 0 := ne_of_gt (by linarith : 0 < 1 - c)
  unfold noValue
  field_simp
  ring

theorem baseline_le_noValue {c : ℝ} (hc : 0 < c) (hcb : c ≤ 1 / 4) :
    2 * c - 4 * c ^ 2 ≤ noValue c := by
  have h₁ : 0 < 1 - c := by linarith
  have hid : noValue c - (2 * c - 4 * c ^ 2) = c * (5 - 12 * c + 8 * c ^ 2) / (2 * (1 - c)) := by
    unfold noValue
    field_simp
    ring
  have hnum : 0 ≤ 5 - 12 * c + 8 * c ^ 2 := by nlinarith [sq_nonneg c]
  have h : 0 ≤ c * (5 - 12 * c + 8 * c ^ 2) / (2 * (1 - c)) := by positivity
  linarith

theorem fullValue_pos {c : ℝ} (hc : 0 < c) (hcb : c ≤ 1 / 4) : 0 < fullValue c :=
  mul_pos (by positivity) (by linarith)

theorem ratio_identity {c : ℝ} (hc : 0 < c) (hcb : c ≤ 1 / 4) : noValue c / fullValue c = ratio c := by
  have hc0 := ne_of_gt hc
  have h₁ : 1 - c ≠ 0 := ne_of_gt (by linarith : 0 < 1 - c)
  have h₂ : 2 - 3 * c ≠ 0 := ne_of_gt (by linarith : 0 < 2 - 3 * c)
  unfold noValue fullValue ratio
  field_simp
  ring

theorem ratio_gap_identity {c : ℝ} (hcb : c ≤ 1 / 4) :
    9 / 8 - ratio c = c * (3 - 5 * c) / (8 * (1 - c) * (2 - 3 * c)) := by
  have h₁ : 1 - c ≠ 0 := ne_of_gt (by linarith : 0 < 1 - c)
  have h₂ : 2 - 3 * c ≠ 0 := ne_of_gt (by linarith : 0 < 2 - 3 * c)
  unfold ratio
  field_simp
  ring

/-- A quantitative convergence certificate for the exact payoff ratio. -/
theorem ratio_gap_bounds {c : ℝ} (hc : 0 < c) (hcb : c ≤ 1 / 4) :
    0 ≤ 9 / 8 - ratio c ∧ 9 / 8 - ratio c ≤ c := by
  rw [ratio_gap_identity hcb]
  have h₁ : 0 < 1 - c := by linarith
  have h₂ : 0 < 2 - 3 * c := by linarith
  have hden : 0 < 8 * (1 - c) * (2 - 3 * c) := by positivity
  constructor
  · exact div_nonneg (mul_nonneg (le_of_lt hc) (by linarith)) (le_of_lt hden)
  · apply (div_le_iff₀ hden).mpr
    have h := mul_nonneg (le_of_lt hc) (show 0 ≤ 13 - 35 * c + 24 * c ^ 2 by nlinarith [sq_nonneg c])
    nlinarith

end

end TransparencyLean.SingleAgent.Tightness
