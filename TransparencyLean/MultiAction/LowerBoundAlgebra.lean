import TransparencyLean.MultiAction.Model

/-! Equal-revenue costs, with B = 1/gamma and zero-based action indices. -/

namespace TransparencyLean.MultiAction.LowerBound

noncomputable section

def costAt (B : ℝ) (k : ℕ) : ℝ := B ^ k - (k + 1) + k / B

@[simp] theorem costAt_zero (B : ℝ) : costAt B 0 = 0 := by simp [costAt]

theorem costAt_step (B : ℝ) (k : ℕ) :
    costAt B (k + 1) = costAt B k + B ^ k * (B - 1) - 1 + 1 / B := by
  simp only [costAt, Nat.cast_add, Nat.cast_one, pow_succ, add_div]
  ring

theorem costAt_nonneg {B : ℝ} (hB : 2 ≤ B) (k : ℕ) : 0 ≤ costAt B k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [costAt_step]
    have hp : 1 ≤ B ^ k := one_le_pow₀ (show 1 ≤ B by linarith)
    have hd : 0 ≤ 1 / B := div_nonneg (by norm_num) (by linarith)
    have hm := mul_le_mul_of_nonneg_right hp (show 0 ≤ B - 1 by linarith)
    nlinarith

/-- Comparing an active action to its active predecessor bounds its revenue
by exactly one, for every share at which it is a best response. -/
theorem adjacent_revenue_le_one {B α : ℝ} (hB : 1 < B) (k : ℕ)
    (h : α * B ^ k - costAt B k ≤ α * B ^ (k + 1) - costAt B (k + 1)) :
    (1 - α) * B ^ (k + 1) ≤ 1 := by
  rw [costAt_step] at h
  have hh : (1 - α) * (B ^ k * (B - 1)) ≤ 1 - 1 / B := by
    rw [pow_succ] at h
    nlinarith
  have hb0 : 0 < B := by linarith
  have hdiv : B * (1 / B) = 1 := by field_simp
  have hm := mul_le_mul_of_nonneg_right hh (le_of_lt hb0)
  have heq : (B - 1) * ((1 - α) * B ^ (k + 1) - 1) =
      B * ((1 - α) * (B ^ k * (B - 1)) - (1 - 1 / B)) := by
    rw [pow_succ]
    nlinarith [hdiv]
  have hn : (B - 1) * ((1 - α) * B ^ (k + 1) - 1) ≤ 0 := by
    rw [heq]
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hb0) (sub_nonpos.mpr hh)
  nlinarith

def base (m : ℕ) : ℝ := 4 * (m + 2)

theorem base_ge_two (m : ℕ) : 2 ≤ base m := by
  dsimp [base]
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  linarith

theorem base_pos (m : ℕ) : 0 < base m := lt_of_lt_of_le (by norm_num) (base_ge_two m)

theorem base_le_pow {m k : ℕ} (hk : k ≠ 0) : base m ≤ base m ^ k :=
  le_self_pow₀ (by linarith [base_ge_two m]) hk

def share (m : ℕ) : ℝ := 1 - (m + 2) / (2 * base m ^ (m + 1))

theorem share_feasible (m : ℕ) : FeasibleShare (share m) := by
  have hp : 0 < base m ^ (m + 1) := pow_pos (base_pos m) _
  have hB := base_le_pow (m := m) (k := m + 1) (by omega)
  have ht : (0 : ℝ) ≤ m + 2 := by positivity
  have hquot : (m + 2 : ℝ) / (2 * base m ^ (m + 1)) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    change 4 * (m + 2 : ℝ) ≤ base m ^ (m + 1) at hB
    nlinarith
  constructor
  · exact sub_nonneg.mpr hquot
  · dsimp [share]
    exact sub_le_self _ (div_nonneg ht (by positivity))

theorem hidden_payoff (m : ℕ) : (1 - share m) * base m ^ (m + 1) = (m + 2) / 2 := by
  have hp : base m ^ (m + 1) ≠ 0 := ne_of_gt (pow_pos (base_pos m) _)
  unfold share
  field_simp
  ring

theorem top_agent_utility (m : ℕ) :
    share m * base m ^ (m + 1) - costAt (base m) (m + 1) =
      (m + 2) / 2 - (m + 1) / base m := by
  have hh := hidden_payoff m
  simp only [costAt, Nat.cast_add, Nat.cast_one]
  linarith

theorem top_agent_utility_gt_half (m : ℕ) :
    1 / 2 < share m * base m ^ (m + 1) - costAt (base m) (m + 1) := by
  rw [top_agent_utility]
  have hb := base_pos m
  have hratio : (m + 1 : ℝ) / base m < 1 / 4 := by
    apply (div_lt_iff₀ hb).mpr
    dsimp [base]
    linarith
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  linarith

theorem lower_agent_utility_le_half (m k : ℕ) (hk : k ≤ m) :
    share m * (base m ^ k / 2) - costAt (base m) k ≤ 1 / 2 := by
  have hα := share_feasible m
  have hp : 0 ≤ base m ^ k := le_of_lt (pow_pos (base_pos m) _)
  have hmul := mul_le_mul_of_nonneg_right hα.2 (show 0 ≤ base m ^ k / 2 by positivity)
  by_cases hz : k = 0
  · subst k
    simp only [costAt_zero, pow_zero, sub_zero] at *
    linarith
  · have hpow := base_le_pow (m := m) hz
    have hkn : (k : ℝ) ≤ m := Nat.cast_le.mpr hk
    have hdiv : 0 ≤ (k : ℝ) / base m := div_nonneg (Nat.cast_nonneg _) (le_of_lt (base_pos m))
    dsimp [costAt, base] at *
    nlinarith

end
end TransparencyLean.MultiAction.LowerBound
