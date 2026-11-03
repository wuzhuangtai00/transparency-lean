import TransparencyLean.Mixed.Contracts

/-! Paper Lemma A.1, including implementation at zero costs and zero probabilities. -/

namespace TransparencyLean.Mixed

open scoped BigOperators

noncomputable section

variable {Agent : Type*} [Fintype Agent] [DecidableEq Agent]

def auxiliaryCost (x c : Agent → ℝ) (i : Agent) : ℝ := x i * c i

omit [Fintype Agent] [DecidableEq Agent] in
theorem auxiliaryCost_nonneg {x c : Agent → ℝ} (hx : ValidProfile x) (hc : ∀ i, 0 ≤ c i) :
    ∀ i, 0 ≤ auxiliaryCost x c i := fun i => mul_nonneg (hx i).1 (hc i)

/-- Lemma A.1(ii): the grand auxiliary team implements a mixed equilibrium. -/
theorem grand_equilibrium {f : Finset Agent → ℝ} {c α x : Agent → ℝ}
    (hx : ValidProfile x) (heq : IsMixedEquilibrium f c α x) :
    IsEquilibrium (auxiliary f x) (auxiliaryCost x c) α Finset.univ := by
  constructor
  · intro i _
    rw [auxiliary_marginal f x Finset.univ (Finset.mem_univ i), mask_univ]
    by_cases hi : 0 < x i
    · have h := mul_le_mul_of_nonneg_left (heq.1 i hi) (hx i).1
      unfold auxiliaryCost
      nlinarith
    · have hz : x i = 0 := le_antisymm (le_of_not_gt hi) (hx i).1
      simp [auxiliaryCost, hz]
  · simp

theorem grand_utility (f : Finset Agent → ℝ) (α x : Agent → ℝ) :
    principalUtility (auxiliary f x) α Finset.univ = utility f α x := rfl

/-- A positive-effort agent receives exactly its original indifference payment. -/
theorem minimum_indifference {f : Finset Agent → ℝ} {c x : Agent → ℝ}
    (hc : ∀ i, 0 ≤ c i) {T : Finset Agent}
    (hT : FeasibleTeam (auxiliary f x) (auxiliaryCost x c) T)
    {i : Agent} (hi : i ∈ T) (hxi : 0 < x i) :
    minimumContract (auxiliary f x) (auxiliaryCost x c) T i * marginal f (mask x T) i = c i := by
  by_cases hci : c i = 0
  · simp [minimumContract, auxiliaryCost, hi, hci]
  · have hci0 : 0 < c i := lt_of_le_of_ne (hc i) (Ne.symm hci)
    have hd : 0 < x i * marginal f (mask x T) i := by
      have h := hT i hi
      rw [auxiliary_marginal f x T hi] at h
      exact lt_of_lt_of_le (mul_pos hxi hci0) h
    have hm : marginal f (mask x T) i ≠ 0 := by
      intro hz
      simp [hz] at hd
    rw [minimumContract, if_pos hi, auxiliary_marginal f x T hi]
    unfold auxiliaryCost
    field_simp [ne_of_gt hxi, hm]
    ring

/-- Lemma A.1(iii), with zero-effort and zero-cost agents handled explicitly. -/
theorem minimum_implementation {f : Finset Agent → ℝ} (hmono : Monotone f)
    {c x : Agent → ℝ} (hc : ∀ i, 0 ≤ c i) (hx : ValidProfile x) {T : Finset Agent}
    (hT : FeasibleTeam (auxiliary f x) (auxiliaryCost x c) T) :
    let β := minimumContract (auxiliary f x) (auxiliaryCost x c) T
    FeasibleContract β ∧ ValidProfile (mask x T) ∧ IsMixedEquilibrium f c β (mask x T) ∧
      utility f β (mask x T) = principalUtility (auxiliary f x) β T := by
  dsimp only
  refine ⟨minimumContract_feasible (auxiliary_monotone hmono hx) (auxiliaryCost_nonneg hx hc) hT,
    mask_valid hx T, ?_, ?_⟩
  · constructor
    · intro i hpos
      have hi : i ∈ T := by by_contra h; simp [mask, h] at hpos
      have hxi : 0 < x i := by simpa [mask, hi] using hpos
      exact le_of_eq (minimum_indifference hc hT hi hxi).symm
    · intro i _
      by_cases hi : i ∈ T
      · by_cases hxi : 0 < x i
        · exact le_of_eq (minimum_indifference hc hT hi hxi)
        · have hz : x i = 0 := le_antisymm (le_of_not_gt hxi) (hx i).1
          simpa [minimumContract, auxiliaryCost, hi, hz] using hc i
      · simpa [minimumContract, hi] using hc i
  · simp [utility, principalUtility]

/-- The auxiliary pure optimum is bounded by the original mixed optimum. -/
theorem statewise_comparison {f : Finset Agent → ℝ} (hf : ValidReward f) (hmono : Monotone f)
    {c x : Agent → ℝ} (hc : ∀ i, 0 ≤ c i) (hx : ValidProfile x) :
    TransparencyLean.statelessValue (auxiliary f x) (auxiliaryCost x c) ≤ statelessValue f c := by
  obtain ⟨T, hT, _, _, hvalue⟩ := TransparencyLean.statelessValue_attained
    (auxiliary_valid hf hx) (auxiliary_monotone hmono hx) (auxiliaryCost_nonneg hx hc)
  obtain ⟨hβ, hy, heq, hu⟩ := minimum_implementation hmono hc hx hT
  have h := utility_le_statelessValue hf hβ hy heq
  rwa [hu, hvalue] at h

variable {Ω : Type*} [Fintype Ω]

omit [Fintype Agent] in
theorem sample_expect (p : FiniteDist Ω) (f : Ω → Finset Agent → ℝ)
    (x : Agent → ℝ) (T : Finset Agent) :
    sample x T (posteriorReward p f) = p.expect (fun ω => sample x T (f ω)) := by
  unfold sample posteriorReward FiniteDist.expect
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro R _
  ring

omit [Fintype Agent] in
theorem auxiliary_posterior (p : FiniteDist Ω) (f : Ω → Finset Agent → ℝ) (x : Agent → ℝ) :
    auxiliary (posteriorReward p f) x = posteriorReward p (fun ω => auxiliary (f ω) x) :=
  funext (sample_expect p f x)

/-- The posterior version of A.1(ii), with equality of principal utility. -/
theorem posterior_grand_equilibrium (p : FiniteDist Ω) (f : Ω → Finset Agent → ℝ)
    {c α x : Agent → ℝ} (hx : ValidProfile x) (heq : IsMixedEquilibrium (posteriorReward p f) c α x) :
    IsEquilibrium (posteriorReward p (fun ω => auxiliary (f ω) x)) (auxiliaryCost x c) α Finset.univ ∧
      principalUtility (posteriorReward p (fun ω => auxiliary (f ω) x)) α Finset.univ =
        utility (posteriorReward p f) α x := by
  rw [← auxiliary_posterior]
  exact ⟨grand_equilibrium hx heq, grand_utility _ _ _⟩

end

end TransparencyLean.Mixed
