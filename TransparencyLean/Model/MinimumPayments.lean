import TransparencyLean.Model.Contracts

namespace TransparencyLean

open scoped BigOperators

variable {Agent : Type*} [Fintype Agent] [DecidableEq Agent]

def FeasibleTeam (f : Finset Agent → ℝ) (c : Agent → ℝ) (S : Finset Agent) : Prop :=
  ∀ i ∈ S, c i ≤ f S - f (S.erase i)

noncomputable def minimumContract (f : Finset Agent → ℝ) (c : Agent → ℝ)
    (S : Finset Agent) (i : Agent) : ℝ :=
  if i ∈ S then c i / (f S - f (S.erase i)) else 0

omit [Fintype Agent] in
theorem equilibrium_feasibleTeam {f : Finset Agent → ℝ} (hmono : Monotone f)
    {c α : Agent → ℝ} {S : Finset Agent}
    (hα : FeasibleContract α) (hS : IsEquilibrium f c α S) : FeasibleTeam f c S := by
  intro i hi
  have hd : 0 ≤ f S - f (S.erase i) := sub_nonneg.mpr (hmono (Finset.erase_subset i S))
  have h := mul_le_mul_of_nonneg_right (hα i).2 hd
  have heq := hS.1 i hi
  nlinarith

omit [Fintype Agent] in
theorem minimumContract_feasible {f : Finset Agent → ℝ} (hmono : Monotone f)
    {c : Agent → ℝ} (hc : ∀ i, 0 ≤ c i) {S : Finset Agent}
    (hS : FeasibleTeam f c S) : FeasibleContract (minimumContract f c S) := by
  intro i
  by_cases hi : i ∈ S
  · simp only [minimumContract, hi, if_true]
    have hd : 0 ≤ f S - f (S.erase i) := sub_nonneg.mpr (hmono (Finset.erase_subset i S))
    constructor
    · exact div_nonneg (hc i) hd
    · by_cases hz : f S - f (S.erase i) = 0
      · simp [hz]
      · exact (div_le_one (lt_of_le_of_ne hd (Ne.symm hz))).mpr (hS i hi)
  · simp [minimumContract, hi]

omit [Fintype Agent] in
theorem minimumContract_equilibrium {f : Finset Agent → ℝ}
    {c : Agent → ℝ} (hc : ∀ i, 0 ≤ c i) {S : Finset Agent}
    (hS : FeasibleTeam f c S) : IsEquilibrium f c (minimumContract f c S) S := by
  constructor
  · intro i hi
    simp only [minimumContract, hi, if_true]
    by_cases hz : c i = 0
    · simp [hz]
    · have hd : 0 < f S - f (S.erase i) :=
        lt_of_lt_of_le (lt_of_le_of_ne (hc i) (Ne.symm hz)) (hS i hi)
      rw [div_mul_cancel₀ _ (ne_of_gt hd)]
  · intro i hi
    simpa [minimumContract, hi] using hc i

omit [Fintype Agent] in
/-- Even at zero costs or zero marginals, the guarded feasible-team model
does not interpret division by zero as free implementation of costly effort. -/
theorem minimumContract_le {f : Finset Agent → ℝ} {c α : Agent → ℝ}
    (hc : ∀ i, 0 ≤ c i) {S : Finset Agent}
    (hα : FeasibleContract α) (hS : IsEquilibrium f c α S) :
    ∀ i, minimumContract f c S i ≤ α i := by
  intro i
  by_cases hi : i ∈ S
  · simp only [minimumContract, hi, if_true]
    by_cases hz : c i = 0
    · simpa [hz] using (hα i).1
    · have hcpos : 0 < c i := lt_of_le_of_ne (hc i) (Ne.symm hz)
      have hin := hS.1 i hi
      have hprod : 0 < α i * (f S - f (S.erase i)) := hcpos.trans_le hin
      have hd : 0 < f S - f (S.erase i) := by
        by_contra h
        have hn := mul_nonpos_of_nonneg_of_nonpos (hα i).1 (le_of_not_gt h)
        linarith
      exact (div_le_iff₀ hd).mpr hin
  · simpa [minimumContract, hi] using (hα i).1

theorem minimumContract_utility_ge {f : Finset Agent → ℝ} (hf : ValidReward f)
    {c α : Agent → ℝ} (hc : ∀ i, 0 ≤ c i) {S : Finset Agent}
    (hα : FeasibleContract α) (hS : IsEquilibrium f c α S) :
    principalUtility f α S ≤ principalUtility f (minimumContract f c S) S := by
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset Agent)) =>
    minimumContract_le hc hα hS i)
  have h0 := (hf S).1
  unfold principalUtility
  nlinarith

/-- A stateless optimum is attained by a minimum-payment contract for a team.
This uses a finite maximization, not compactness or an assumed optimizer. -/
theorem statelessValue_attained {f : Finset Agent → ℝ} (hf : ValidReward f)
    (hmono : Monotone f) {c : Agent → ℝ} (hc : ∀ i, 0 ≤ c i) :
    ∃ S, FeasibleTeam f c S ∧
      FeasibleContract (minimumContract f c S) ∧
      IsEquilibrium f c (minimumContract f c S) S ∧
      principalUtility f (minimumContract f c S) S = statelessValue f c := by
  classical
  let teams := (Finset.univ : Finset (Finset Agent)).filter (FeasibleTeam f c)
  have hnonempty : teams.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [teams, FeasibleTeam]
  obtain ⟨S, hS, hmax⟩ := teams.exists_max_image
    (fun T => principalUtility f (minimumContract f c T) T) hnonempty
  have hSfeas : FeasibleTeam f c S := (Finset.mem_filter.mp hS).2
  have hα := minimumContract_feasible hmono hc hSfeas
  have hNE := minimumContract_equilibrium hc hSfeas
  refine ⟨S, hSfeas, hα, hNE, le_antisymm (utility_le_statelessValue hf hα hNE) ?_⟩
  apply statelessValue_le hc
  intro α T hαT hT
  apply (minimumContract_utility_ge hf hc hαT hT).trans
  apply hmax T
  simp only [teams, Finset.mem_filter, Finset.mem_univ, true_and]
  exact equilibrium_feasibleTeam hmono hαT hT

end TransparencyLean
