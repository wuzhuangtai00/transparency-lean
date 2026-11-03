import TransparencyLean.Submodular.Completion

namespace TransparencyLean

open scoped BigOperators

noncomputable section

variable {Agent : Type*} [Fintype Agent] [DecidableEq Agent]

/-- Potential Lemma with a fixed team of free agents retained throughout.
The benchmark marginal `d` and share `k` satisfy `c = k * d` on the paid team.
This form avoids a separate change of ground set for zero-cost agents. -/
theorem potential_with_free_team {f : Finset Agent → ℝ} {c k d : Agent → ℝ}
    (hf : ValidReward f) (hmono : Monotone f) (hsub : Submodular f)
    (hc : ∀ i, 0 ≤ c i) (Z P : Finset Agent) (hdis : Disjoint Z P)
    (hfree : ∀ i ∈ Z, c i = 0)
    (hpaid : ∀ i ∈ P, 0 < k i ∧ 0 < d i ∧ c i = k i * d i)
    (hbudget : ∑ i ∈ P, k i ≤ 1) :
    (1 - ∑ i ∈ P, k i) * (f (Z ∪ P) - (1 / 4) * ∑ i ∈ P, d i) +
      ∑ i ∈ P, k i * (removalMarginal f (Z ∪ P) i - d i) ≤ statelessValue f c := by
  let cfg : Pruning.Config f c k d (removalMarginal f (Z ∪ P)) := {
    kept := Z
    remaining := P
    reserved := fun _ => 0
    saving := fun _ => 0
    budget := 1 - ∑ i ∈ P, k i
    disjoint := hdis
    budget_nonneg := sub_nonneg.mpr hbudget
    balance := by simp
    remaining_good := hpaid
    marginal_bound := fun _ _ => le_rfl
    kept_good := by
      intro i hi
      simp [hfree i hi]
  }
  have h := Pruning.Config.completion hf hmono hsub hc cfg
  have hs : cfg.secured = 0 := by simp [Pruning.Config.secured, cfg]
  rw [Pruning.Config.guarantee, hs, zero_add] at h
  exact (le_max_left cfg.potential 0).trans h

/-- Paper Lemma 4.2 (Potential Lemma), with its benchmark `d_i = c_i / k_i`.
The reward need not be normalized at the empty team. -/
theorem potential_lemma {f : Finset Agent → ℝ} {c k : Agent → ℝ}
    (hf : ValidReward f) (hmono : Monotone f) (hsub : Submodular f)
    (hc : ∀ i, 0 ≤ c i) (S : Finset Agent)
    (hcost : ∀ i ∈ S, 0 < c i) (hk : ∀ i ∈ S, 0 < k i)
    (hbudget : ∑ i ∈ S, k i ≤ 1) :
    (1 - ∑ i ∈ S, k i) * (f S - (1 / 4) * ∑ i ∈ S, c i / k i) +
      ∑ i ∈ S, k i * (removalMarginal f S i - c i / k i) ≤ statelessValue f c := by
  have hp : ∀ i ∈ S, 0 < k i ∧ 0 < c i / k i ∧ c i = k i * (c i / k i) := by
    intro i hi
    exact ⟨hk i hi, div_pos (hcost i hi) (hk i hi),
      (mul_div_cancel₀ (c i) (ne_of_gt (hk i hi))).symm⟩
  simpa only [Finset.empty_union] using potential_with_free_team hf hmono hsub hc
    ∅ S (Finset.disjoint_empty_left S) (by simp) hp hbudget

end

end TransparencyLean
