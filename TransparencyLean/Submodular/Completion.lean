import TransparencyLean.Submodular.Pruning

namespace TransparencyLean.Pruning

open scoped BigOperators

noncomputable section

variable {Agent : Type*} [Fintype Agent] [DecidableEq Agent]
variable {f : Finset Agent → ℝ} {c k d p : Agent → ℝ}

/-- Every valid partial pruning configuration has a completion whose utility
is at least its guarantee. Strong induction checks all three branches of the
paper's pruning procedure, including its maximum-ratio ordering rule. -/
theorem Config.completion (hf : ValidReward f) (hmono : Monotone f)
    (hsub : Submodular f) (hc : ∀ i, 0 ≤ c i) (cfg : Config f c k d p) :
    cfg.guarantee ≤ statelessValue f c := by
  classical
  suffices main : ∀ n, ∀ cfg : Config f c k d p, cfg.remaining.card = n →
      cfg.guarantee ≤ statelessValue f c from main _ cfg rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro cfg hn
    by_cases hR : cfg.remaining = ∅
    · exact cfg.terminal hf hmono hc hR
    obtain ⟨i, hi, hmax⟩ := cfg.remaining.exists_max_image
      (fun j => removalMarginal f cfg.team j / d j) (Finset.nonempty_iff_ne_empty.mpr hR)
    obtain ⟨hk, hd, hcost⟩ := cfg.remaining_good i hi
    let t := removalMarginal f cfg.team i / d i
    have ht : t * d i = removalMarginal f cfg.team i := div_mul_cancel₀ _ (ne_of_gt hd)
    have ht0 : 0 ≤ t := div_nonneg (removalMarginal_nonneg hmono _ _) (le_of_lt hd)
    have hp : p i ≤ t * d i := ht.symm ▸ cfg.marginal_bound i hi
    have hsmaller : (cfg.remaining.erase i).card < n := by
      rw [← hn]
      exact Finset.card_erase_lt_of_mem hi
    have hdel := ih _ hsmaller (cfg.drop hsub i hi) rfl
    change cfg.secured + max (cfg.drop hsub i hi).potential 0 ≤ statelessValue f c at hdel
    rw [cfg.drop_potential hsub i hi t ht] at hdel
    have hret : ∀ (a q : ℝ) (ha : 0 ≤ a) (hq : 0 ≤ q)
        (hm : q + c i ≤ a * removalMarginal f cfg.team i)
        (hb : 0 ≤ cfg.budget + k i - a),
        cfg.secured + q + max ((cfg.budget + k i - a) * cfg.restReward i +
          cfg.restCorrection i) 0 ≤ statelessValue f c := by
      intro a q ha hq hm hb
      have hh := ih _ hsmaller (cfg.retain i hi a q ha hq hm hb) rfl
      simpa only [Config.guarantee, Config.retain_secured, Config.retain_potential] using hh
    by_cases hhigh : 1 ≤ t
    · have hm : d i ≤ removalMarginal f cfg.team i := by nlinarith
      have hq : 0 ≤ k i * (removalMarginal f cfg.team i - d i) :=
        mul_nonneg (le_of_lt hk) (sub_nonneg.mpr hm)
      have hinc : k i * (removalMarginal f cfg.team i - d i) + c i ≤
          k i * removalMarginal f cfg.team i := by rw [hcost]; nlinarith
      have hb : 0 ≤ cfg.budget + k i - k i := by simpa using cfg.budget_nonneg
      have hh := hret (k i) _ (le_of_lt hk) hq hinc hb
      have hphi : (cfg.budget + k i - k i) * cfg.restReward i + cfg.restCorrection i =
          cfg.potential + cfg.budget * d i / 4 - k i * (p i - d i) := by
        rw [cfg.parent_potential i hi]
        unfold PotentialStep.parent
        ring
      rw [hphi] at hh
      exact (PotentialStep.high_step cfg.secured cfg.potential cfg.budget (k i)
        (removalMarginal f cfg.team i) (d i) (p i) cfg.budget_nonneg
        (le_of_lt hk) (le_of_lt hd) hm (cfg.marginal_bound i hi)).trans hh
    · have ht1 : t < 1 := lt_of_not_ge hhigh
      by_cases haff : k i * (1 - t) ≤ cfg.budget * t
      · have htpos : 0 < t := by
          by_cases hz : t = 0
          · rw [hz] at haff
            nlinarith
          · exact lt_of_le_of_ne ht0 (Ne.symm hz)
        have ha : 0 ≤ k i / t := div_nonneg (le_of_lt hk) (le_of_lt htpos)
        have hb : 0 ≤ cfg.budget + k i - k i / t := by
          apply sub_nonneg.mpr
          apply (div_le_iff₀ htpos).mpr
          nlinarith
        have hinc : 0 + c i ≤ k i / t * removalMarginal f cfg.team i := by
          rw [← ht, ← mul_assoc, div_mul_cancel₀ _ (ne_of_gt htpos), hcost]
          simp
        have hkeep := hret (k i / t) 0 ha le_rfl hinc hb
        simp only [add_zero] at hkeep
        change cfg.secured + max (PotentialStep.keep cfg.budget (cfg.restReward i)
          (cfg.restCorrection i) (k i) t) 0 ≤ statelessValue f c at hkeep
        have havg := PotentialStep.affordable_step cfg.budget (cfg.restReward i)
          (cfg.restCorrection i) (k i) (p i) (d i) t cfg.budget_nonneg
          (le_of_lt hk) (le_of_lt hd) htpos (le_of_lt ht1) hp
        rw [Config.guarantee, cfg.parent_potential i hi]
        rw [add_max, add_zero]
        apply max_le
        · have hm := max_le
            (show PotentialStep.keep cfg.budget (cfg.restReward i)
                (cfg.restCorrection i) (k i) t ≤ statelessValue f c - cfg.secured by
              linarith [le_max_left (PotentialStep.keep cfg.budget (cfg.restReward i)
                (cfg.restCorrection i) (k i) t) 0])
            (show PotentialStep.delete cfg.budget (cfg.restReward i)
                (cfg.restCorrection i) (k i) (d i) t ≤ statelessValue f c - cfg.secured by
              linarith [le_max_left (PotentialStep.delete cfg.budget (cfg.restReward i)
                (cfg.restCorrection i) (k i) (d i) t) 0])
          linarith
        · linarith [le_max_right (PotentialStep.delete cfg.budget (cfg.restReward i)
            (cfg.restCorrection i) (k i) (d i) t) 0]
      · have hY : cfg.restCorrection i ≤ 0 := by
          apply Finset.sum_nonpos
          intro j hj
          have hjR := Finset.mem_of_mem_erase hj
          obtain ⟨hkj, hdj, _⟩ := cfg.remaining_good j hjR
          have hr : removalMarginal f cfg.team j ≤ t * d j :=
            (div_le_iff₀ hdj).mp (hmax j hjR)
          have hpj : p j ≤ removalMarginal f cfg.team j := cfg.marginal_bound j hjR
          apply mul_nonpos_of_nonneg_of_nonpos (le_of_lt hkj)
          nlinarith
        have hstep := PotentialStep.unaffordable_step cfg.budget (cfg.restReward i)
          (cfg.restCorrection i) (k i) (p i) (d i) t cfg.budget_nonneg hk hd hp hY
          (lt_of_not_ge haff)
        rw [Config.guarantee, cfg.parent_potential i hi]
        exact (add_le_add_left hstep cfg.secured).trans hdel

end

end TransparencyLean.Pruning
