import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# The local algebra in the Potential Lemma (paper Lemma 4.2)

These are the scalar inequalities for the three branches of the pruning
procedure. `Pruning.lean` proves the finite-set invariant and terminal contract
bound; `Completion.lean` uses these inequalities in a terminating induction.
The unaffordable branch has the explicit hypothesis `Y ≤ 0` here; the
completion proof derives it from the maximum-ratio ordering rule.
-/

namespace TransparencyLean.PotentialStep

noncomputable section

def parent (B X Y k p d : ℝ) : ℝ := B * (X - d / 4) + k * (p - d) + Y
def keep (B X Y k t : ℝ) : ℝ := (B + k - k / t) * X + Y
def delete (B X Y k d t : ℝ) : ℝ := (B + k) * (X - t * d) + Y

theorem quarter_identity (t : ℝ) : (1 / 4 : ℝ) - t * (1 - t) = (t - 1 / 2) ^ 2 := by
  ring

theorem high_step (Q Φ B k m d p : ℝ)
    (hB : 0 ≤ B) (hk : 0 ≤ k) (hd : 0 ≤ d) (hm : d ≤ m) (hp : p ≤ m) :
    Q + max Φ 0 ≤
      (Q + k * (m - d)) + max (Φ + B * d / 4 - k * (p - d)) 0 := by
  have hq : Q ≤ Q + k * (m - d) := by
    nlinarith [mul_nonneg hk (sub_nonneg.mpr hm)]
  have ht : Q + Φ ≤ (Q + k * (m - d)) + (Φ + B * d / 4 - k * (p - d)) := by
    nlinarith [mul_nonneg hB hd, mul_nonneg hk (sub_nonneg.mpr hp)]
  rw [add_max, add_zero, add_max, add_zero]
  exact max_le_max ht hq

/-- Exact identity behind the t:(1-t) averaging argument. -/
theorem averaged_identity (B X Y k p d t : ℝ) (ht : t ≠ 0) :
    t * keep B X Y k t + (1 - t) * delete B X Y k d t - parent B X Y k p d =
      B * d * (t - 1 / 2) ^ 2 + k * d * (1 - t) ^ 2 + k * (t * d - p) := by
  unfold keep delete parent
  field_simp [ht]
  ring

/-- Affordable low-agent branch: the better potential is at least the parent.
Affordability itself is needed for the algorithm's budget invariant, not this
algebraic inequality. -/
theorem affordable_step (B X Y k p d t : ℝ)
    (hB : 0 ≤ B) (hk : 0 ≤ k) (hd : 0 ≤ d)
    (ht0 : 0 < t) (ht1 : t ≤ 1) (hp : p ≤ t * d) :
    parent B X Y k p d ≤ max (keep B X Y k t) (delete B X Y k d t) := by
  have hid := averaged_identity B X Y k p d t (ne_of_gt ht0)
  have hsq1 := mul_nonneg (mul_nonneg hB hd) (sq_nonneg (t - 1 / 2))
  have hsq2 := mul_nonneg (mul_nonneg hk hd) (sq_nonneg (1 - t))
  have hcorr := mul_nonneg hk (sub_nonneg.mpr hp)
  have havg : parent B X Y k p d ≤
      t * keep B X Y k t + (1 - t) * delete B X Y k d t := by linarith
  have hkeep := mul_le_mul_of_nonneg_left
    (le_max_left (keep B X Y k t) (delete B X Y k d t)) (le_of_lt ht0)
  have hdelete := mul_le_mul_of_nonneg_left
    (le_max_right (keep B X Y k t) (delete B X Y k d t)) (sub_nonneg.mpr ht1)
  nlinarith

/-- Unaffordable branch, including t = 0. A division-free proof of the strict
improvement when the old potential is positive. -/
theorem unaffordable_strict (B X Y k p d t : ℝ)
    (hB : 0 ≤ B) (hk : 0 < k) (hd : 0 < d)
    (hp : p ≤ t * d) (hY : Y ≤ 0)
    (haff : B * t < k * (1 - t)) (hparent : 0 < parent B X Y k p d) :
    parent B X Y k p d < delete B X Y k d t := by
  have hgap : 0 < k * (d - p) - B * t * d := by
    have h1 := mul_pos (sub_pos.mpr haff) hd
    have h2 := mul_nonneg (le_of_lt hk) (sub_nonneg.mpr hp)
    nlinarith
  have hbase : 0 < B * d / 4 + k * (d - p) - B * t * d := by
    nlinarith [mul_nonneg hB (le_of_lt hd)]
  have hprod := mul_pos (show 0 < B + k by linarith) hbase
  have hpos := mul_pos hk hparent
  have hneg := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hk) hY
  have hid : B * (delete B X Y k d t - parent B X Y k p d) =
      k * parent B X Y k p d +
        (B + k) * (B * d / 4 + k * (d - p) - B * t * d) - k * Y := by
    unfold delete parent
    ring
  have hdelta : 0 < B * (delete B X Y k d t - parent B X Y k p d) := by
    linarith
  by_contra h
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos hB
    (sub_nonpos.mpr (le_of_not_gt h))
  linarith

theorem unaffordable_step (B X Y k p d t : ℝ)
    (hB : 0 ≤ B) (hk : 0 < k) (hd : 0 < d)
    (hp : p ≤ t * d) (hY : Y ≤ 0) (haff : B * t < k * (1 - t)) :
    max (parent B X Y k p d) 0 ≤ max (delete B X Y k d t) 0 := by
  by_cases h : 0 < parent B X Y k p d
  · exact max_le_max (le_of_lt (unaffordable_strict B X Y k p d t hB hk hd hp hY haff h)) le_rfl
  · rw [max_eq_right (le_of_not_gt h)]
    exact le_max_right _ _

end

end TransparencyLean.PotentialStep
