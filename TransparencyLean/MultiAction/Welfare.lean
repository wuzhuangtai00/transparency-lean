import TransparencyLean.MultiAction.Model

/-! A self-contained proof that linear contracts recover at least 1/n of
first-best welfare. Inductively remove an action of largest reward. The last
action's extra welfare is bounded by its revenue at its first inducing share.
This discharges the external welfare theorem used in the paper's proof. -/

namespace TransparencyLean.MultiAction

open scoped BigOperators
noncomputable section

variable {A : Type*} [DecidableEq A]

theorem welfare_bound_finset (S : Finset A) (r c : A → ℝ) (M : ℝ)
    (hr : ∀ i ∈ S, 0 ≤ r i) (hc : ∀ i ∈ S, 0 ≤ c i) (hM : 0 ≤ M)
    (hbound : ∀ α i, FeasibleShare α → i ∈ S →
      (∀ j ∈ S, α * r j - c j ≤ α * r i - c i) → payoff r α i ≤ M) :
    ∀ i ∈ S, r i - c i ≤ S.card * M := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro i hi
    obtain ⟨j, hj, hmax⟩ := S.exists_max_image r ⟨i, hi⟩
    let T := S.erase j
    have hT : T ⊂ S := Finset.erase_ssubset hj
    have hsub : ∀ k ∈ T, k ∈ S := fun k hk => Finset.mem_of_mem_erase hk
    have hcard : (S.card : ℝ) = T.card + 1 := by
      exact_mod_cast (Finset.card_erase_add_one hj).symm
    have hboundT : ∀ α k, FeasibleShare α → k ∈ T →
        (∀ l ∈ T, α * r l - c l ≤ α * r k - c k) → payoff r α k ≤ M := by
      intro α k hα hk hbest
      by_cases hjk : α * r j - c j ≤ α * r k - c k
      · apply hbound α k hα (hsub k hk)
        intro l hl
        by_cases hlj : l = j
        · simpa [hlj] using hjk
        · exact hbest l (Finset.mem_erase.mpr ⟨hlj, hl⟩)
      · have hbj : ∀ l ∈ S, α * r l - c l ≤ α * r j - c j := by
          intro l hl
          by_cases hlj : l = j
          · simp [hlj]
          · exact (hbest l (Finset.mem_erase.mpr ⟨hlj, hl⟩)).trans (le_of_not_ge hjk)
        exact (mul_le_mul_of_nonneg_left (hmax k (hsub k hk))
          (sub_nonneg.mpr hα.2)).trans (hbound α j hα hj hbj)
    have hwT : ∀ k ∈ T, r k - c k ≤ T.card * M :=
      ih T hT (fun k hk => hr k (hsub k hk)) (fun k hk => hc k (hsub k hk)) hboundT
    have hstep : (T.card : ℝ) * M ≤ S.card * M := by rw [hcard]; nlinarith
    by_cases hij : i = j
    · subst i
      by_cases hdom : ∃ k ∈ T, r j - c j ≤ r k - c k
      · obtain ⟨k, hk, hkj⟩ := hdom
        exact hkj.trans ((hwT k hk).trans hstep)
      have hw : ∀ k ∈ T, r k - c k < r j - c j := by
        intro k hk
        exact lt_of_not_ge (fun h => hdom ⟨k, hk, h⟩)
      let q := fun k => max 0 ((c j - c k) / (r j - r k))
      obtain ⟨k, hk, hq⟩ := S.exists_max_image q ⟨j, hj⟩
      let α := q k
      have hα0 : 0 ≤ α := le_max_left _ _
      have hα1 : α ≤ 1 := by
        apply max_le (by norm_num)
        by_cases he : r j = r k
        · simp [he]
        · have hd : 0 < r j - r k := sub_pos.mpr (lt_of_le_of_ne (hmax k hk) (Ne.symm he))
          apply (div_le_iff₀ hd).mpr
          by_cases hkj : k = j
          · subst k; simp at hd
          · have hh := hw k (Finset.mem_erase.mpr ⟨hkj, hk⟩)
            linarith
      have hbest : ∀ l ∈ S, α * r l - c l ≤ α * r j - c j := by
        intro l hl
        by_cases hlj : l = j
        · simp [hlj]
        have hlw := hw l (Finset.mem_erase.mpr ⟨hlj, hl⟩)
        by_cases he : r j = r l
        · rw [he]; linarith
        · have hd : 0 < r j - r l := sub_pos.mpr (lt_of_le_of_ne (hmax l hl) (Ne.symm he))
          have hfrac : (c j - c l) / (r j - r l) ≤ α :=
            (le_max_right _ _).trans (hq l hl)
          have hh := (div_le_iff₀ hd).mp hfrac
          nlinarith
      have hp := hbound α j ⟨hα0, hα1⟩ hj hbest
      by_cases hz : α = 0
      · have hcj := hc j hj
        simp only [payoff, hz, sub_zero, one_mul] at hp
        have hcount : 1 ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨j, hj⟩
        nlinarith
      · have hαpos : 0 < α := lt_of_le_of_ne hα0 (Ne.symm hz)
        have hfrac : α = (c j - c k) / (r j - r k) := by
          have hh : 0 < max 0 ((c j - c k) / (r j - r k)) := hαpos
          rcases lt_max_iff.mp hh with h | h
          · linarith
          · exact max_eq_right (le_of_lt h)
        have hne : r j ≠ r k := by
          intro he
          have : α = 0 := by dsimp [α, q]; simp [he]
          exact hz this
        have hkj : k ≠ j := fun he => hne (congrArg r he.symm)
        have hd : r j - r k ≠ 0 := sub_ne_zero.mpr hne
        have heq : α * (r j - r k) = c j - c k := (eq_div_iff hd).mp hfrac
        have hkr := hr k hk
        have hkw := hwT k (Finset.mem_erase.mpr ⟨hkj, hk⟩)
        have hprod := mul_nonneg (sub_nonneg.mpr hα1) hkr
        dsimp [payoff] at hp
        rw [hcard]
        nlinarith
    · exact (hwT i (Finset.mem_erase.mpr ⟨hij, hi⟩)).trans hstep

variable [Fintype A] [Nonempty A]

theorem welfare_le_card_value {r c : A → ℝ} (hr : ∀ i, 0 ≤ r i)
    (hc : ∀ i, 0 ≤ c i) (i : A) : r i - c i ≤ Fintype.card A * value r c := by
  simpa using welfare_bound_finset Finset.univ r c (value r c)
    (fun j _ => hr j) (fun j _ => hc j) (value_nonneg hr)
    (fun α j hα _ hj => payoff_le_value hr hα (fun k => hj k (Finset.mem_univ k))) i
    (Finset.mem_univ i)

end
end TransparencyLean.MultiAction
