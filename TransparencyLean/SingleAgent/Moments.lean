import TransparencyLean.SingleAgent.Model

/-! A direct moment proof of the 9/8 inequality, avoiding support reduction
and differentiation of the paper's three-parameter rational function. -/

namespace TransparencyLean.SingleAgent

noncomputable section

def loss (f : Finset Unit → ℝ) (c : ℝ) : ℝ := f Finset.univ - value f c

theorem loss_nonneg {f : Finset Unit → ℝ} (hf : ValidReward f) (hmono : Monotone f)
    {c : ℝ} (hc : 0 ≤ c) : 0 ≤ loss f c := sub_nonneg.mpr (value_le_effort hf hmono hc)

theorem loss_le_delta {f : Finset Unit → ℝ} (hf : ValidReward f) {c : ℝ} (hc : 0 ≤ c) :
    loss f c ≤ f Finset.univ - f ∅ := sub_le_sub_left (baseline_le_value hf hc) _

/-- The reward lost relative to effort satisfies a quadratic bound in each state. -/
theorem loss_square_bound {f : Finset Unit → ℝ} (hf : ValidReward f) (hmono : Monotone f)
    {c : ℝ} (hc : 0 ≤ c) : (loss f c) ^ 2 ≤ c * (f ∅ + loss f c) := by
  have hr0 := loss_nonneg hf hmono hc
  have hrd := loss_le_delta hf hc
  have ha := (hf ∅).1
  by_cases hrc : loss f c ≤ c
  · nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hrc), mul_nonneg hc ha]
  · have hd : 0 < f Finset.univ - f ∅ := by linarith
    have hfeas : c ≤ f Finset.univ - f ∅ := by linarith
    have hwork := work_payoff_le_value hf hmono hc hfeas
    have hscaled := mul_le_mul_of_nonneg_right hwork (le_of_lt hd)
    have hid : ((1 - c / (f Finset.univ - f ∅)) * f Finset.univ) *
        (f Finset.univ - f ∅) = f Finset.univ * (f Finset.univ - f ∅ - c) := by
      linear_combination - f Finset.univ * (div_mul_cancel₀ c (ne_of_gt hd))
    rw [hid] at hscaled
    have hprod := mul_nonneg (sub_nonneg.mpr hrd) (show 0 ≤ loss f c - c by linarith)
    unfold loss at *
    nlinarith

theorem square_expect_le_expect_square {Ω : Type*} [Fintype Ω] (p : FiniteDist Ω) (r : Ω → ℝ) :
    (p.expect r) ^ 2 ≤ p.expect (fun ω => (r ω) ^ 2) := by
  have h := p.expect_nonneg (fun ω => sq_nonneg (r ω - p.expect r))
  have heq : (fun ω => (r ω - p.expect r) ^ 2) =
      (fun ω => (r ω) ^ 2 - (2 * p.expect r) * r ω + (p.expect r) ^ 2) := by
    funext ω
    ring
  rw [heq, FiniteDist.expect_add, FiniteDist.expect_sub, FiniteDist.expect_mul,
    FiniteDist.expect_const] at h
  nlinarith

/-- The scalar inequality behind the sharp constant. The polynomial certificate
is a sum of three weighted squares and the nonnegative moment slack. -/
theorem nine_eighths_from_moments {A F R c α : ℝ}
    (hA : 0 ≤ A) (hAF : A ≤ F) (hR : 0 ≤ R) (hα : 0 ≤ α)
    (hmoment : R ^ 2 ≤ c * (A + R)) (hincentive : c ≤ α * (F + R - A)) :
    8 * ((1 - α) * (F + R)) ≤ 9 * F := by
  by_cases hzero : R = 0
  · rw [hzero]
    nlinarith [mul_nonneg hα (show 0 ≤ F by linarith)]
  · have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hzero)
    have hfac : 0 < (F + R - A) * (A + R) := mul_pos (by linarith) (by linarith)
    have hscale := mul_le_mul_of_nonneg_right hincentive (show 0 ≤ A + R by linarith)
    have hslack : 0 ≤ α * (F + R - A) * (A + R) - R ^ 2 := by linarith
    have h₁ := mul_nonneg hA (sq_nonneg ((F - A) - R))
    have h₂ := mul_nonneg (sub_nonneg.mpr hAF) (sq_nonneg (A - R))
    have h₃ := mul_nonneg hR (sq_nonneg (A - (F - A)))
    have h₄ := mul_nonneg (show 0 ≤ 8 * (F + R) by linarith) hslack
    have hid : (9 * F - 8 * ((1 - α) * (F + R))) * ((F + R - A) * (A + R)) =
        A * ((F - A) - R) ^ 2 + (F - A) * (A - R) ^ 2 + R * (A - (F - A)) ^ 2 +
          8 * (F + R) * (α * (F + R - A) * (A + R) - R ^ 2) := by ring
    have hp : 0 ≤ (9 * F - 8 * ((1 - α) * (F + R))) * ((F + R - A) * (A + R)) := by
      rw [hid]
      linarith
    have h := nonneg_of_mul_nonneg_left hp hfac
    linarith

end

end TransparencyLean.SingleAgent
