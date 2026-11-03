import TransparencyLean.MultiAction.Information
import TransparencyLean.MultiAction.LowerBoundAlgebra

/-! The paper's two-state, 2n-1-action lower-bound family, specialized to
gamma = 1/(4n), n = m+2. All displayed values belong to actual contracts.
The full-disclosure optimum is exactly one; hiding the state earns n/2. -/

namespace TransparencyLean.MultiAction.LowerBound

noncomputable section

abbrev Action (m : ℕ) := Option (Bool × Fin (m + 1))

theorem action_count (m : ℕ) : Fintype.card (Action m) = 2 * (m + 2) - 1 := by
  simp only [Action, Fintype.card_option, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  omega

def prior : FiniteDist Bool where
  prob _ := 1 / 2
  nonneg _ := by norm_num
  sum_eq_one := by norm_num [Fintype.sum_bool]

def stateReward (m : ℕ) (ω : Bool) : Action m → ℝ
  | none => base m ^ (m + 1)
  | some (b, k) => if b = ω then base m ^ k.val else 0

def costs (m : ℕ) : Action m → ℝ
  | none => costAt (base m) (m + 1)
  | some (_, k) => costAt (base m) k.val

theorem reward_nonneg (m : ℕ) (ω : Bool) (i : Action m) : 0 ≤ stateReward m ω i := by
  cases i with
  | none => exact le_of_lt (pow_pos (base_pos m) _)
  | some a =>
    dsimp [stateReward]
    split_ifs
    · exact le_of_lt (pow_pos (base_pos m) _)
    · exact le_rfl

theorem reward_le_top (m : ℕ) (ω : Bool) (i : Action m) :
    stateReward m ω i ≤ base m ^ (m + 1) := by
  cases i with
  | none => exact le_rfl
  | some a =>
    dsimp [stateReward]
    split_ifs
    · exact pow_le_pow_right₀ (by linarith [base_ge_two m]) (Nat.le_of_lt a.2.isLt)
    · exact le_of_lt (pow_pos (base_pos m) _)

/-- Realization by the paper's two common reward outcomes, zero and B^(n-1). -/
def outcomeDist (m : ℕ) (ω : Bool) (i : Action m) : FiniteDist Bool where
  prob b := if b then stateReward m ω i / base m ^ (m + 1)
    else 1 - stateReward m ω i / base m ^ (m + 1)
  nonneg b := by
    have hp : 0 < base m ^ (m + 1) := pow_pos (base_pos m) _
    cases b
    · exact sub_nonneg.mpr ((div_le_one hp).mpr (reward_le_top m ω i))
    · exact div_nonneg (reward_nonneg m ω i) (le_of_lt hp)
  sum_eq_one := by simp

theorem expected_outcome (m : ℕ) (ω : Bool) (i : Action m) :
    (outcomeDist m ω i).expect (fun b => if b then base m ^ (m + 1) else 0) = stateReward m ω i := by
  have hp : base m ^ (m + 1) ≠ 0 := ne_of_gt (pow_pos (base_pos m) _)
  simp [FiniteDist.expect, outcomeDist, hp]

theorem costs_nonneg (m : ℕ) (i : Action m) : 0 ≤ costs m i := by
  cases i <;> exact costAt_nonneg (base_ge_two m) _

theorem zero_cost (m : ℕ) : ∃ i, costs m i = 0 :=
  ⟨some (false, ⟨0, by omega⟩), costAt_zero _⟩

theorem revealed_payoff_le_one (m : ℕ) (ω : Bool) {α : ℝ} {i : Action m}
    (hα : FeasibleShare α) (hi : BestResponse (stateReward m ω) (costs m) α i) :
    payoff (stateReward m ω) α i ≤ 1 := by
  have hB : 1 < base m := by linarith [base_ge_two m]
  cases i with
  | none =>
    have hh := hi (some (ω, ⟨m, by omega⟩))
    simp only [stateReward, costs, if_pos rfl] at hh
    exact adjacent_revenue_le_one hB m hh
  | some a =>
    rcases a with ⟨b, ⟨k, hk⟩⟩
    by_cases hb : b = ω
    · subst b
      cases k with
      | zero =>
        simpa [payoff, stateReward] using sub_le_self (1 : ℝ) hα.1
      | succ k =>
        have hh := hi (some (ω, ⟨k, by omega⟩))
        simp only [stateReward, costs, if_pos rfl] at hh
        simpa [payoff, stateReward] using adjacent_revenue_le_one hB k hh
    · simp [payoff, stateReward, hb]

theorem revealed_value (m : ℕ) (ω : Bool) : value (stateReward m ω) (costs m) = 1 := by
  apply le_antisymm
  · exact value_le (fun α i hα hi => revealed_payoff_le_one m ω hα hi)
  · let i : Action m := some (ω, ⟨0, by omega⟩)
    have hi : BestResponse (stateReward m ω) (costs m) 0 i := by
      intro j
      have hc := costs_nonneg m j
      simpa [i, costs] using hc
    have h := payoff_le_value (reward_nonneg m ω) ⟨le_rfl, zero_le_one⟩ hi
    simpa [payoff, i, stateReward] using h

theorem full_disclosure_value (m : ℕ) :
    fullDisclosureValue prior (stateReward m) (costs m) = 1 := by
  unfold fullDisclosureValue
  simp_rw [revealed_value]
  exact prior.expect_const _

def hiddenReward (m : ℕ) : Action m → ℝ
  | none => base m ^ (m + 1)
  | some (_, k) => base m ^ k.val / 2

theorem mean_reward (m : ℕ) : meanReward prior (stateReward m) = hiddenReward m := by
  funext i
  cases i with
  | none => simp [meanReward, FiniteDist.expect, prior, stateReward, hiddenReward]
  | some a =>
    rcases a with ⟨b, k⟩
    cases b <;> simp [meanReward, FiniteDist.expect, prior, stateReward, hiddenReward] <;> ring

theorem hidden_equilibrium (m : ℕ) :
    BestResponse (meanReward prior (stateReward m)) (costs m) (share m) none := by
  rw [mean_reward]
  intro i
  cases i with
  | none => exact le_rfl
  | some a =>
    rcases a with ⟨b, k⟩
    exact (lower_agent_utility_le_half m k.val (by omega)).trans
      (le_of_lt (top_agent_utility_gt_half m))

def hidden_scheme (m : ℕ) : ContractScheme prior (stateReward m) (costs m) Unit where
  information := PosteriorScheme.uninformative prior
  share _ := share m
  response _ := FiniteDist.pointMass none
  feasible _ := share_feasible m
  equilibrium _ := pointMass_bestResponse (hidden_equilibrium m)

theorem hidden_scheme_utility (m : ℕ) : (hidden_scheme m).utility = (m + 2) / 2 := by
  change (FiniteDist.pointMass ()).expect (fun _ : Unit => (FiniteDist.pointMass none).expect
    (payoff (meanReward prior (stateReward m)) (share m))) = _
  simp only [FiniteDist.expect_pointMass, mean_reward]
  exact hidden_payoff m

/-- The witnessed ratio is (N+1)/4, where N is the total number of actions.
This is a lower bound on joint design, not a claim of optimality of hiding. -/
theorem linear_separation (m : ℕ) :
    ∃ hidden : KernelContractScheme prior (stateReward m) (costs m) Unit,
      hidden.kernel = (PosteriorScheme.uninformative prior).toSignalKernel ∧
      fullDisclosureValue prior (stateReward m) (costs m) = 1 ∧
      4 * hidden.utility = (Fintype.card (Action m) : ℝ) + 1 := by
  refine ⟨(hidden_scheme m).toKernelContract, rfl, full_disclosure_value m, ?_⟩
  rw [ContractScheme.toKernelContract_utility, hidden_scheme_utility]
  have hcard : (Fintype.card (Action m) : ℝ) + 1 = 2 * (m + 2 : ℝ) := by
    simp only [Action, Fintype.card_option, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
    push_cast
    ring
  rw [hcard]
  ring

/-- No constant independent of the action count bounds the loss from full
disclosure, even with two equally likely states and a pure hidden response. -/
theorem no_constant_factor (β : ℝ) :
    ∃ (m : ℕ) (hidden : KernelContractScheme prior (stateReward m) (costs m) Unit),
      (∀ ω i, 0 ≤ stateReward m ω i) ∧ (∀ i, 0 ≤ costs m i) ∧ (∃ i, costs m i = 0) ∧
      hidden.kernel = (PosteriorScheme.uninformative prior).toSignalKernel ∧
      0 < fullDisclosureValue prior (stateReward m) (costs m) ∧
      β * fullDisclosureValue prior (stateReward m) (costs m) < hidden.utility := by
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * β)
  refine ⟨m, (hidden_scheme m).toKernelContract, reward_nonneg m, costs_nonneg m, zero_cost m,
    rfl, ?_, ?_⟩
  · rw [full_disclosure_value]; norm_num
  · rw [ContractScheme.toKernelContract_utility, hidden_scheme_utility, full_disclosure_value]
    linarith

end
end TransparencyLean.MultiAction.LowerBound
