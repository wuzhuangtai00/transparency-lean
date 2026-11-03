import Mathlib.Tactic

namespace TransparencyLean.Tightness

noncomputable section

def M (n : ℝ) : ℝ := 2 * n ^ 2 + n + 1
def D (n : ℝ) : ℝ := (2 * n - 1) * M n
def cost (n : ℝ) : ℝ := n / D n
def noValue (n : ℝ) : ℝ := (3 * n ^ 3 + n - 1) / D n
def fullValue (n : ℝ) : ℝ := 3 * n ^ 2 * (3 * n + 2) / (4 * D n)
def ratio (n : ℝ) : ℝ := 4 * (3 * n ^ 3 + n - 1) / (3 * n ^ 2 * (3 * n + 2))

theorem M_pos {n : ℝ} (hn : 2 ≤ n) : 0 < M n := by unfold M; positivity
theorem D_pos {n : ℝ} (hn : 2 ≤ n) : 0 < D n :=
  mul_pos (by linarith) (M_pos hn)
theorem D_identity (n : ℝ) : D n = 4 * n ^ 3 + n - 1 := by unfold D M; ring
theorem cost_pos {n : ℝ} (hn : 2 ≤ n) : 0 < cost n := div_pos (by linarith) (D_pos hn)

theorem cost_small {n : ℝ} (hn : 2 ≤ n) : 2 * n ^ 2 * cost n ≤ 1 := by
  have hd := D_pos hn
  rw [cost, ← mul_div_assoc, div_le_one hd]
  rw [D_identity]
  have hn3 : 0 ≤ n ^ 3 := pow_nonneg (by linarith : 0 ≤ n) 3
  nlinarith

theorem noValue_identity {n : ℝ} (hn : 2 ≤ n) : noValue n = 1 - n ^ 2 * cost n := by
  unfold noValue cost
  field_simp [ne_of_gt (D_pos hn)]
  rw [D_identity]
  ring

theorem no_team_bound {n s : ℝ} (hn : 2 ≤ n) (_hs0 : 0 ≤ s) (hs : s ≤ n) :
    s / n - s ^ 2 * cost n ≤ noValue n := by
  have hn0 : 0 < n := by linarith
  have hc := le_of_lt (cost_pos hn)
  have hsmall := cost_small hn
  have hcoeff : 0 ≤ 1 / n - cost n * (n + s) := by
    have h1 : cost n * (n + s) ≤ 2 * n * cost n := by nlinarith
    have h2 : 2 * n * cost n ≤ 1 / n := by
      apply (le_div_iff₀ hn0).mpr
      nlinarith
    linarith
  have hprod := mul_nonneg (sub_nonneg.mpr hs) hcoeff
  have hid : (1 - n ^ 2 * cost n) - (s / n - s ^ 2 * cost n) =
      (n - s) * (1 / n - cost n * (n + s)) := by
    field_simp
    ring
  rw [noValue_identity hn]
  linarith

/-- The integer rounding step: two adjacent integers straddle the real maximizer. -/
theorem integer_gap_nonneg (m s : ℕ) :
    0 ≤ ((s : ℝ) - m) * ((s : ℝ) - m - 1) := by
  by_cases h : s ≤ m
  · have hh : (s : ℝ) ≤ m := by exact_mod_cast h
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  · have hh : (m : ℝ) + 1 ≤ s := by exact_mod_cast (show m + 1 ≤ s by omega)
    exact mul_nonneg (by linarith) (by linarith)

theorem high_team_bound {n : ℝ} (hn : 2 ≤ n) (m s : ℕ) (heven : n = 2 * m) :
    (1 - (1 + n * s) / M n) * ((n + s) / (2 * n - 1)) ≤ fullValue n := by
  have hd := D_pos hn
  have hm := M_pos hn
  have hb : 0 < 2 * n - 1 := by linarith
  have hid : fullValue n - (1 - (1 + n * s) / M n) * ((n + s) / (2 * n - 1)) =
      n * (((s : ℝ) - m) * ((s : ℝ) - m - 1)) / D n := by
    unfold fullValue D
    field_simp
    rw [heven]
    unfold M
    ring
  have hpos := div_nonneg (mul_nonneg (by linarith : 0 ≤ n) (integer_gap_nonneg m s)) (le_of_lt hd)
  linarith

theorem high_team_value {n : ℝ} (hn : 2 ≤ n) (m : ℕ) (heven : n = 2 * m) :
    (1 - (1 + n * m) / M n) * ((n + m) / (2 * n - 1)) = fullValue n := by
  have hm := ne_of_gt (M_pos hn)
  have hb : 2 * n - 1 ≠ 0 := ne_of_gt (by linarith : 0 < 2 * n - 1)
  unfold fullValue D
  field_simp
  rw [heven]
  unfold M
  ring

theorem low_team_bound {n s : ℝ} (hn : 2 ≤ n) (_hs0 : 0 ≤ s) (hs : s ≤ n) :
    (1 - n * s / M n) * (s / (2 * n - 1)) ≤ fullValue n := by
  have hd := D_pos hn
  have hm := M_pos hn
  have hb : 0 < 2 * n - 1 := by linarith
  have hcoeff : 0 ≤ M n - n * (n + s) := by
    unfold M
    nlinarith [mul_nonneg (by linarith : 0 ≤ n) (sub_nonneg.mpr hs)]
  have hprod := mul_nonneg (sub_nonneg.mpr hs) hcoeff
  have hgap : 0 ≤ n * (5 * n ^ 2 + 2 * n - 4) :=
    mul_nonneg (by linarith) (by nlinarith [sq_nonneg n])
  apply (le_of_sub_nonneg (show 0 ≤ fullValue n -
    (1 - n * s / M n) * (s / (2 * n - 1)) from ?_))
  have hid : fullValue n - (1 - n * s / M n) * (s / (2 * n - 1)) =
      ((n - s) * (M n - n * (n + s)) + n * (5 * n ^ 2 + 2 * n - 4) / 4) / D n := by
    unfold fullValue D
    field_simp
    unfold M
    ring
  rw [hid]
  positivity

theorem fullValue_pos {n : ℝ} (hn : 2 ≤ n) : 0 < fullValue n := by
  unfold fullValue
  exact div_pos (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos (by linarith)))
    (by linarith)) (mul_pos (by norm_num) (D_pos hn))

theorem ratio_identity {n : ℝ} (hn : 2 ≤ n) : noValue n / fullValue n = ratio n := by
  have hd := ne_of_gt (D_pos hn)
  have hn0 : n ≠ 0 := ne_of_gt (by linarith : 0 < n)
  have ht : 3 * n + 2 ≠ 0 := ne_of_gt (by linarith : 0 < 3 * n + 2)
  unfold noValue fullValue ratio
  field_simp
  ring

theorem cost_le_uniform {n : ℝ} (hn : 2 ≤ n) : cost n ≤ 1 / n := by
  apply (le_div_iff₀ (by linarith : 0 < n)).mpr
  have hp := mul_nonneg (show 0 ≤ 2 * n ^ 2 - n by nlinarith [sq_nonneg n])
    (le_of_lt (cost_pos hn))
  nlinarith [cost_small hn]

theorem share_high {n : ℝ} (hn : 2 ≤ n) : cost n / (n / (2 * n - 1)) = 1 / M n := by
  have hn0 : n ≠ 0 := ne_of_gt (by linarith : 0 < n)
  have hb : 2 * n - 1 ≠ 0 := ne_of_gt (by linarith : 0 < 2 * n - 1)
  have hm := ne_of_gt (M_pos hn)
  unfold cost D
  field_simp
  ring

theorem share_low {n : ℝ} (hn : 2 ≤ n) : cost n / (1 / (2 * n - 1)) = n / M n := by
  have hb : 2 * n - 1 ≠ 0 := ne_of_gt (by linarith : 0 < 2 * n - 1)
  have hm := ne_of_gt (M_pos hn)
  unfold cost D
  field_simp
  ring

theorem cost_le_low {n : ℝ} (hn : 2 ≤ n) : cost n ≤ 1 / (2 * n - 1) := by
  apply (div_le_one (one_div_pos.mpr (by linarith : 0 < 2 * n - 1))).mp
  rw [share_low hn]
  apply (div_le_one (M_pos hn)).mpr
  unfold M
  nlinarith [sq_nonneg n]

theorem ratio_gap_identity {n : ℝ} (hn : 2 ≤ n) :
    4 / 3 - ratio n = 4 * (2 * n ^ 2 - n + 1) / (3 * n ^ 2 * (3 * n + 2)) := by
  have hn0 : n ≠ 0 := ne_of_gt (by linarith : 0 < n)
  have ht : 3 * n + 2 ≠ 0 := ne_of_gt (by linarith : 0 < 3 * n + 2)
  unfold ratio
  field_simp
  ring

/-- An explicit error bound for convergence to the sharp constant. -/
theorem ratio_gap_bounds {n : ℝ} (hn : 2 ≤ n) :
    0 ≤ 4 / 3 - ratio n ∧ 4 / 3 - ratio n ≤ 1 / n := by
  have hn0 : 0 < n := by linarith
  have hden : 0 < 3 * n ^ 2 * (3 * n + 2) := by positivity
  rw [ratio_gap_identity hn]
  constructor
  · apply div_nonneg _ (le_of_lt hden)
    have hh : 0 ≤ 2 * n ^ 2 - n + 1 := by nlinarith [sq_nonneg (n - 1)]
    positivity
  · apply (div_le_div_iff₀ hden hn0).mpr
    have hp := mul_nonneg (le_of_lt hn0)
      (show 0 ≤ n ^ 2 + 10 * n - 4 by nlinarith [sq_nonneg n])
    nlinarith

end

end TransparencyLean.Tightness
