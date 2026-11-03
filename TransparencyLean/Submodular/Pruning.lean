import TransparencyLean.Submodular.SetFunctions
import TransparencyLean.Submodular.PotentialStep

namespace TransparencyLean.Pruning

open scoped BigOperators

noncomputable section

variable {Agent : Type*} [DecidableEq Agent]

/-- A partially processed team. `saving i` records utility already secured by
a kept agent. The key invariant is `saving i + c i ≤ reserved i * marginal i`.
It subsumes both high and low agents, and allows zero-cost agents to be kept
from the outset. -/
structure Config (f : Finset Agent → ℝ) (c k d p : Agent → ℝ) where
  kept : Finset Agent
  remaining : Finset Agent
  reserved : Agent → ℝ
  saving : Agent → ℝ
  budget : ℝ
  disjoint : Disjoint kept remaining
  budget_nonneg : 0 ≤ budget
  balance : budget + ∑ i ∈ kept, reserved i + ∑ i ∈ remaining, k i = 1
  remaining_good : ∀ i ∈ remaining, 0 < k i ∧ 0 < d i ∧ c i = k i * d i
  marginal_bound : ∀ i ∈ remaining, p i ≤ removalMarginal f (kept ∪ remaining) i
  kept_good : ∀ i ∈ kept, 0 ≤ reserved i ∧ 0 ≤ saving i ∧
    saving i + c i ≤ reserved i * removalMarginal f (kept ∪ remaining) i

variable {f : Finset Agent → ℝ} {c k d p : Agent → ℝ}

def Config.team (cfg : Config f c k d p) : Finset Agent := cfg.kept ∪ cfg.remaining
def Config.secured (cfg : Config f c k d p) : ℝ := ∑ i ∈ cfg.kept, cfg.saving i
def Config.potential (cfg : Config f c k d p) : ℝ :=
  cfg.budget * (f cfg.team - (1 / 4) * ∑ i ∈ cfg.remaining, d i) +
    ∑ i ∈ cfg.remaining, k i * (p i - d i)
def Config.guarantee (cfg : Config f c k d p) : ℝ := cfg.secured + max cfg.potential 0

theorem Config.not_kept (cfg : Config f c k d p) {i : Agent} (hi : i ∈ cfg.remaining) :
    i ∉ cfg.kept := fun h => Finset.disjoint_left.mp cfg.disjoint h hi

def Config.drop (cfg : Config f c k d p) (hsub : Submodular f)
    (i : Agent) (hi : i ∈ cfg.remaining) : Config f c k d p where
  kept := cfg.kept
  remaining := cfg.remaining.erase i
  reserved := cfg.reserved
  saving := cfg.saving
  budget := cfg.budget + k i
  disjoint := cfg.disjoint.mono_right (Finset.erase_subset i cfg.remaining)
  budget_nonneg := add_nonneg cfg.budget_nonneg (le_of_lt (cfg.remaining_good i hi).1)
  balance := by
    have h := Finset.sum_erase_add cfg.remaining k hi
    have hb := cfg.balance
    linarith
  remaining_good j hj := cfg.remaining_good j (Finset.mem_of_mem_erase hj)
  marginal_bound j hj := by
    apply (cfg.marginal_bound j (Finset.mem_of_mem_erase hj)).trans
    exact removalMarginal_antitone hsub
      (Finset.union_subset_union (Finset.Subset.refl _) (Finset.erase_subset i _))
      (Finset.mem_union_right _ hj)
  kept_good j hj := by
    have hg := cfg.kept_good j hj
    have hm := removalMarginal_antitone hsub
      (Finset.union_subset_union (Finset.Subset.refl cfg.kept)
        (Finset.erase_subset i cfg.remaining)) (Finset.mem_union_left _ hj)
    exact ⟨hg.1, hg.2.1, hg.2.2.trans (mul_le_mul_of_nonneg_left hm hg.1)⟩

def Config.retain (cfg : Config f c k d p) (i : Agent) (hi : i ∈ cfg.remaining)
    (a q : ℝ) (ha : 0 ≤ a) (hq : 0 ≤ q)
    (hm : q + c i ≤ a * removalMarginal f cfg.team i)
    (hb : 0 ≤ cfg.budget + k i - a) : Config f c k d p where
  kept := insert i cfg.kept
  remaining := cfg.remaining.erase i
  reserved := Function.update cfg.reserved i a
  saving := Function.update cfg.saving i q
  budget := cfg.budget + k i - a
  disjoint := by
    apply Finset.disjoint_left.mpr
    intro j hj hjR
    rcases Finset.mem_insert.mp hj with hji | hjK
    · subst j
      exact Finset.not_mem_erase i cfg.remaining hjR
    · exact Finset.disjoint_left.mp cfg.disjoint hjK (Finset.mem_of_mem_erase hjR)
  budget_nonneg := hb
  balance := by
    rw [sum_insert_update cfg.kept (cfg.not_kept hi)]
    have h := Finset.sum_erase_add cfg.remaining k hi
    have hbal := cfg.balance
    linarith
  remaining_good j hj := cfg.remaining_good j (Finset.mem_of_mem_erase hj)
  marginal_bound j hj := by
    rw [insert_kept_union_erase hi]
    exact cfg.marginal_bound j (Finset.mem_of_mem_erase hj)
  kept_good j hj := by
    rw [insert_kept_union_erase hi]
    rcases Finset.mem_insert.mp hj with hji | hjK
    · subst j
      simpa only [Function.update_self] using (show
        0 ≤ a ∧ 0 ≤ q ∧ q + c i ≤ a * removalMarginal f cfg.team i from ⟨ha, hq, hm⟩)
    · have hji : j ≠ i := ne_of_mem_of_not_mem hjK (cfg.not_kept hi)
      simp only [Function.update_of_ne hji]
      exact cfg.kept_good j hjK

def Config.restReward (cfg : Config f c k d p) (i : Agent) : ℝ :=
  f cfg.team - (1 / 4) * ∑ j ∈ cfg.remaining.erase i, d j

def Config.restCorrection (cfg : Config f c k d p) (i : Agent) : ℝ :=
  ∑ j ∈ cfg.remaining.erase i, k j * (p j - d j)

theorem Config.parent_potential (cfg : Config f c k d p) (i : Agent)
    (hi : i ∈ cfg.remaining) :
    cfg.potential = PotentialStep.parent cfg.budget (cfg.restReward i)
      (cfg.restCorrection i) (k i) (p i) (d i) := by
  have hd := Finset.sum_erase_add cfg.remaining d hi
  have hp := Finset.sum_erase_add cfg.remaining (fun j => k j * (p j - d j)) hi
  unfold Config.potential Config.restReward Config.restCorrection PotentialStep.parent
  rw [← hd, ← hp]
  ring

theorem Config.drop_potential (cfg : Config f c k d p) (hsub : Submodular f)
    (i : Agent) (hi : i ∈ cfg.remaining) (t : ℝ)
    (ht : t * d i = removalMarginal f cfg.team i) :
    (cfg.drop hsub i hi).potential = PotentialStep.delete cfg.budget
      (cfg.restReward i) (cfg.restCorrection i) (k i) (d i) t := by
  have ht' : f (cfg.team.erase i) = f cfg.team - t * d i := by
    unfold removalMarginal at ht
    linarith
  simp only [Config.potential, Config.drop, Config.team]
  rw [kept_union_erase (cfg.not_kept hi)]
  change (cfg.budget + k i) * (f (cfg.team.erase i) -
    (1 / 4) * ∑ j ∈ cfg.remaining.erase i, d j) +
    ∑ j ∈ cfg.remaining.erase i, k j * (p j - d j) = _
  rw [ht']
  unfold PotentialStep.delete Config.restReward Config.restCorrection
  ring

theorem Config.retain_potential (cfg : Config f c k d p) (i : Agent)
    (hi : i ∈ cfg.remaining) (a q : ℝ) (ha : 0 ≤ a) (hq : 0 ≤ q)
    (hm : q + c i ≤ a * removalMarginal f cfg.team i)
    (hb : 0 ≤ cfg.budget + k i - a) :
    (cfg.retain i hi a q ha hq hm hb).potential =
      (cfg.budget + k i - a) * cfg.restReward i + cfg.restCorrection i := by
  simp only [Config.potential, Config.retain, Config.team]
  rw [insert_kept_union_erase hi]
  rfl

theorem Config.retain_secured (cfg : Config f c k d p) (i : Agent)
    (hi : i ∈ cfg.remaining) (a q : ℝ) (ha : 0 ≤ a) (hq : 0 ≤ q)
    (hm : q + c i ≤ a * removalMarginal f cfg.team i)
    (hb : 0 ≤ cfg.budget + k i - a) :
    (cfg.retain i hi a q ha hq hm hb).secured = cfg.secured + q := by
  change (∑ j ∈ insert i cfg.kept, Function.update cfg.saving i q j) = _
  rw [sum_insert_update cfg.kept (cfg.not_kept hi)]
  simp only [Config.secured, add_comm]

/-- The surplus recorded for one kept agent is paid for by reducing its
reserved payment to the minimum incentive-compatible payment. -/
theorem saving_le_payment_reduction (a q c δ r : ℝ)
    (ha : 0 ≤ a) (hq : 0 ≤ q) (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hr : δ ≤ r) (h : q + c ≤ a * δ) : q ≤ (a - c / δ) * r := by
  by_cases hz : δ = 0
  · have hqz : q = 0 := by rw [hz] at h; nlinarith
    rw [hz, div_zero, sub_zero, hqz]
    exact mul_nonneg ha (hz ▸ hr)
  · have hd : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hz)
    have hca : c / δ ≤ a := (div_le_iff₀ hd).mpr (by linarith)
    have hprod := mul_nonneg (sub_nonneg.mpr hca) (sub_nonneg.mpr hr)
    have hid : c / δ * δ = c := div_mul_cancel₀ c hz
    nlinarith

variable [Fintype Agent]

theorem Config.terminal (cfg : Config f c k d p) (hf : ValidReward f)
    (hmono : Monotone f) (hc : ∀ i, 0 ≤ c i) (hR : cfg.remaining = ∅) :
    cfg.guarantee ≤ statelessValue f c := by
  have hbal : cfg.budget + ∑ i ∈ cfg.kept, cfg.reserved i = 1 := by
    simpa only [hR, Finset.sum_empty, add_zero] using cfg.balance
  have hg : ∀ i ∈ cfg.kept, 0 ≤ cfg.reserved i ∧ 0 ≤ cfg.saving i ∧
      cfg.saving i + c i ≤ cfg.reserved i * removalMarginal f cfg.kept i := by
    simpa only [hR, Finset.union_empty] using cfg.kept_good
  have ha : ∀ i ∈ cfg.kept, cfg.reserved i ≤ 1 := by
    intro i hi
    have hs := Finset.single_le_sum (fun j hj => (hg j hj).1) hi
    linarith [cfg.budget_nonneg]
  have hteam : FeasibleTeam f c cfg.kept := by
    intro i hi
    have hm := removalMarginal_nonneg hmono cfg.kept i
    have hmul := mul_le_mul_of_nonneg_right (ha i hi) hm
    have hh := hg i hi
    change c i ≤ removalMarginal f cfg.kept i
    nlinarith
  have hsum : (∑ i, minimumContract f c cfg.kept i) =
      ∑ i ∈ cfg.kept, minimumContract f c cfg.kept i := by
    symm
    apply Finset.sum_subset (Finset.subset_univ cfg.kept)
    intro i _ hi
    simp [minimumContract, hi]
  have hsave : cfg.secured ≤ ((∑ i ∈ cfg.kept, cfg.reserved i) -
      ∑ i ∈ cfg.kept, minimumContract f c cfg.kept i) * f cfg.kept := by
    calc
      cfg.secured ≤ ∑ i ∈ cfg.kept,
          (cfg.reserved i - minimumContract f c cfg.kept i) * f cfg.kept := by
        apply Finset.sum_le_sum
        intro i hi
        simp only [minimumContract, hi, if_true]
        exact saving_le_payment_reduction _ _ _ _ _ (hg i hi).1 (hg i hi).2.1
          (hc i) (removalMarginal_nonneg hmono cfg.kept i)
          (by linarith [(hf (cfg.kept.erase i)).1])
          (hg i hi).2.2
      _ = _ := by rw [← Finset.sum_mul, Finset.sum_sub_distrib]
  have hpot : cfg.potential = cfg.budget * f cfg.kept := by
    simp [Config.potential, Config.team, hR]
  have hguar : cfg.guarantee = cfg.secured + cfg.budget * f cfg.kept := by
    rw [Config.guarantee, hpot, max_eq_left (mul_nonneg cfg.budget_nonneg (hf _).1)]
  apply le_trans _ (utility_le_statelessValue hf
    (minimumContract_feasible hmono hc hteam) (minimumContract_equilibrium hc hteam))
  rw [hguar, principalUtility, hsum]
  calc
    cfg.secured + cfg.budget * f cfg.kept ≤
        ((∑ i ∈ cfg.kept, cfg.reserved i) -
          ∑ i ∈ cfg.kept, minimumContract f c cfg.kept i) * f cfg.kept +
          cfg.budget * f cfg.kept := add_le_add_right hsave _
    _ = _ := by rw [← hbal]; ring

end

end TransparencyLean.Pruning
