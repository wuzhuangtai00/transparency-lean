import TransparencyLean.Model.MinimumPayments

namespace TransparencyLean

open scoped BigOperators

variable {Agent : Type*} [DecidableEq Agent]

def removalMarginal (f : Finset Agent → ℝ) (S : Finset Agent) (i : Agent) : ℝ :=
  f S - f (S.erase i)

theorem removalMarginal_nonneg {f : Finset Agent → ℝ} (hmono : Monotone f)
    (S : Finset Agent) (i : Agent) : 0 ≤ removalMarginal f S i :=
  sub_nonneg.mpr (hmono (Finset.erase_subset i S))

/-- Removing other agents increases a retained agent's marginal contribution. -/
theorem removalMarginal_antitone {f : Finset Agent → ℝ} (hsub : Submodular f)
    {S T : Finset Agent} (hST : S ⊆ T) {i : Agent} (hi : i ∈ S) :
    removalMarginal f T i ≤ removalMarginal f S i := by
  have hu : S ∪ T.erase i = T := by
    ext j
    simp only [Finset.mem_union, Finset.mem_erase]
    constructor
    · rintro (h | ⟨_, h⟩)
      · exact hST h
      · exact h
    · intro hj
      by_cases hji : j = i
      · exact Or.inl (hji ▸ hi)
      · exact Or.inr ⟨hji, hj⟩
  have hh : S ∩ T.erase i = S.erase i := by
    ext j
    simp only [Finset.mem_inter, Finset.mem_erase]
    exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, hST h.2⟩⟩
  have h := hsub S (T.erase i)
  rw [hu, hh] at h
  unfold removalMarginal
  linarith

theorem sum_removalMarginal_le {f : Finset Agent → ℝ} (hsub : Submodular f)
    (S : Finset Agent) : ∑ i ∈ S, removalMarginal f S i ≤ f S - f ∅ := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha]
    have hm : removalMarginal f (insert a S) a = f (insert a S) - f S := by
      simp [removalMarginal, ha]
    rw [hm]
    have hs := Finset.sum_le_sum (fun i (hi : i ∈ S) =>
      removalMarginal_antitone hsub (Finset.subset_insert a S) hi)
    linarith

theorem kept_union_erase {K R : Finset Agent} {i : Agent}
    (hnot : i ∉ K) : K ∪ R.erase i = (K ∪ R).erase i := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [hnot]
  · simp [hji, and_or_left]

theorem insert_kept_union_erase {K R : Finset Agent} {i : Agent} (hi : i ∈ R) :
    insert i K ∪ R.erase i = K ∪ R := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [hi]
  · simp [hji]

theorem sum_insert_update (K : Finset Agent) {i : Agent} (hi : i ∉ K)
    (a : Agent → ℝ) (v : ℝ) :
    ∑ j ∈ insert i K, Function.update a i v j = v + ∑ j ∈ K, a j := by
  rw [Finset.sum_insert hi, Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact Function.update_of_ne (ne_of_mem_of_not_mem hj hi) v a

end TransparencyLean
