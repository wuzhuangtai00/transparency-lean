import TransparencyLean.Model.Additive
import TransparencyLean.Submodular.TightnessAlgebra
import TransparencyLean.Information.Contracts

namespace TransparencyLean.Tightness

open scoped BigOperators

noncomputable section

def weight (n : ℕ) (ω i : Fin n) : ℝ :=
  if i = ω then (n : ℝ) / (2 * n - 1) else 1 / (2 * n - 1)

def reward (n : ℕ) (ω : Fin n) : Finset (Fin n) → ℝ := additiveReward (weight n ω)
def costs (n : ℕ) (_ : Fin n) : ℝ := cost n

def prior (n : ℕ) (hn : 2 ≤ n) : FiniteDist (Fin n) where
  prob _ := 1 / n
  nonneg _ := by positivity
  sum_eq_one := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    simp [hn0]

theorem weight_symm (n : ℕ) (ω i : Fin n) : weight n ω i = weight n i ω := by
  simp only [weight, eq_comm]

theorem weight_pos (n : ℕ) (hn : 2 ≤ n) (ω i : Fin n) : 0 < weight n ω i := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hb : 0 < (2 : ℝ) * n - 1 := by linarith
  unfold weight
  split_ifs <;> positivity

theorem weight_total (n : ℕ) (hn : 2 ≤ n) (ω : Fin n) : ∑ i, weight n ω i = 1 := by
  have hn1 : 1 ≤ n := by omega
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hb : (2 : ℝ) * n - 1 ≠ 0 := ne_of_gt (by linarith : 0 < (2 : ℝ) * n - 1)
  unfold weight
  rw [sum_one_special]
  simp only [Finset.mem_univ, if_true, Finset.card_erase_of_mem (Finset.mem_univ ω),
    Finset.card_univ, Fintype.card_fin, Nat.cast_sub hn1, Nat.cast_one]
  field_simp
  ring

theorem reward_valid (n : ℕ) (hn : 2 ≤ n) (ω : Fin n) : ValidReward (reward n ω) :=
  additiveReward_valid (fun i => le_of_lt (weight_pos n hn ω i)) (le_of_eq (weight_total n hn ω))

theorem reward_monotone (n : ℕ) (hn : 2 ≤ n) (ω : Fin n) : Monotone (reward n ω) :=
  additiveReward_monotone (fun i => le_of_lt (weight_pos n hn ω i))

theorem reward_submodular (n : ℕ) (ω : Fin n) : Submodular (reward n ω) :=
  additiveReward_submodular _

theorem reward_additive (n : ℕ) (ω : Fin n) : IsAdditiveReward (reward n ω) := ⟨weight n ω, rfl⟩

theorem costs_pos (n : ℕ) (hn : 2 ≤ n) (i : Fin n) : 0 < costs n i :=
  cost_pos (by exact_mod_cast hn)

theorem cost_le_weight (n : ℕ) (hn : 2 ≤ n) (ω i : Fin n) : costs n i ≤ weight n ω i := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hb : 0 < (2 : ℝ) * n - 1 := by linarith
  change cost n ≤ _
  unfold weight
  split_ifs
  · exact (cost_le_low hnr).trans ((div_le_div_iff_of_pos_right hb).mpr (by linarith))
  · exact cost_le_low hnr

theorem mean_weight (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    (prior n hn).expect (fun ω => weight n ω i) = 1 / n := by
  change (∑ ω, (1 / (n : ℝ)) * weight n ω i) = _
  rw [← Finset.mul_sum]
  simp_rw [weight_symm n _ i]
  rw [weight_total n hn i, mul_one]

theorem mean_reward (n : ℕ) (hn : 2 ≤ n) :
    posteriorReward (prior n hn) (reward n) = additiveReward (fun _ : Fin n => 1 / (n : ℝ)) := by
  funext S
  change (prior n hn).expect (fun ω => ∑ i ∈ S, weight n ω i) = _
  rw [FiniteDist.expect_finset_sum]
  simp_rw [mean_weight n hn]
  rfl

theorem uniform_revenue (n : ℕ) (hn : 2 ≤ n) (S : Finset (Fin n)) :
    (1 - ∑ _i ∈ S, cost (n : ℝ) / (1 / (n : ℝ))) * (∑ _i ∈ S, 1 / (n : ℝ)) =
      (S.card : ℝ) / n - (S.card : ℝ) ^ 2 * cost n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp only [Finset.sum_const, nsmul_eq_mul]
  field_simp
  ring

theorem no_disclosure_value (n : ℕ) (hn : 2 ≤ n) :
    noDisclosureValue (prior n hn) (reward n) (costs n) = noValue n := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [noDisclosureValue, mean_reward]
  apply additive_value_eq (fun _ => by positivity) (by simp [hn0])
    (fun i => le_of_lt (costs_pos n hn i)) (fun _ => cost_le_uniform hnr) Finset.univ
  · intro S
    change (1 - ∑ _i ∈ S, cost (n : ℝ) / (1 / (n : ℝ))) * (∑ _i ∈ S, 1 / (n : ℝ)) ≤ _
    rw [uniform_revenue n hn S]
    exact no_team_bound hnr (Nat.cast_nonneg _)
      (by exact_mod_cast (show S.card ≤ n by simpa using Finset.card_le_univ S))
  · change (1 - ∑ _i ∈ (Finset.univ : Finset (Fin n)), cost (n : ℝ) / (1 / (n : ℝ))) *
        (∑ _i ∈ (Finset.univ : Finset (Fin n)), 1 / (n : ℝ)) = _
    rw [uniform_revenue n hn, Finset.card_univ, Fintype.card_fin, div_self hn0, ← noValue_identity hnr]

theorem minimum_share (n : ℕ) (hn : 2 ≤ n) (ω i : Fin n) :
    costs n i / weight n ω i = if i = ω then 1 / M n else (n : ℝ) / M n := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold costs weight
  split_ifs
  · exact share_high hnr
  · exact share_low hnr

theorem high_revenue (n : ℕ) (hn : 2 ≤ n) (ω : Fin n) (S : Finset (Fin n)) (hω : ω ∈ S) :
    (1 - ∑ i ∈ S, costs n i / weight n ω i) * (∑ i ∈ S, weight n ω i) =
      (1 - (1 + (n : ℝ) * (S.erase ω).card) / M n) *
        (((n : ℝ) + (S.erase ω).card) / (2 * n - 1)) := by
  simp_rw [minimum_share n hn, weight]
  rw [sum_one_special, sum_one_special]
  simp only [hω, if_true]
  ring

theorem low_revenue (n : ℕ) (hn : 2 ≤ n) (ω : Fin n) (S : Finset (Fin n)) (hω : ω ∉ S) :
    (1 - ∑ i ∈ S, costs n i / weight n ω i) * (∑ i ∈ S, weight n ω i) =
      (1 - (n : ℝ) * S.card / M n) * ((S.card : ℝ) / (2 * n - 1)) := by
  simp_rw [minimum_share n hn, weight]
  rw [sum_one_special, sum_one_special]
  simp only [hω, if_false, zero_add, Finset.erase_eq_of_not_mem hω]
  ring

theorem revealed_value (n : ℕ) (hn : 2 ≤ n) (heven : Even n) (ω : Fin n) :
    statelessValue (reward n ω) (costs n) = fullValue n := by
  classical
  obtain ⟨m, hm⟩ := heven
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmr : (n : ℝ) = 2 * m := by exact_mod_cast (show n = 2 * m by omega)
  have hsize : m ≤ (Finset.univ.erase ω).card := by
    simp only [Finset.card_erase_of_mem (Finset.mem_univ ω), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨L, hL, hcard⟩ := Finset.exists_subset_card_eq hsize
  have hωL : ω ∉ L := fun h => Finset.not_mem_erase ω Finset.univ (hL h)
  apply additive_value_eq (fun i => le_of_lt (weight_pos n hn ω i))
    (le_of_eq (weight_total n hn ω)) (fun i => le_of_lt (costs_pos n hn i))
    (cost_le_weight n hn ω) (insert ω L)
  · intro S
    by_cases hω : ω ∈ S
    · rw [high_revenue n hn ω S hω]
      exact high_team_bound hnr m (S.erase ω).card hmr
    · rw [low_revenue n hn ω S hω]
      exact low_team_bound hnr (Nat.cast_nonneg _)
        (by exact_mod_cast (show S.card ≤ n by simpa using Finset.card_le_univ S))
  · rw [high_revenue n hn ω (insert ω L) (Finset.mem_insert_self ω L)]
    simp only [Finset.erase_insert hωL, hcard]
    exact high_team_value hnr m hmr

theorem full_disclosure_value (n : ℕ) (hn : 2 ≤ n) (heven : Even n) :
    fullDisclosureValue (prior n hn) (reward n) (costs n) = fullValue n := by
  unfold fullDisclosureValue
  simp_rw [revealed_value n hn heven]
  exact FiniteDist.expect_const _ _

end

end TransparencyLean.Tightness
