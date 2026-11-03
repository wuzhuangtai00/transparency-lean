import TransparencyLean.Information.Contracts

/-!
# The exact supermodular separation (paper Theorem 5.1)

Rewards and costs are divided by eight, as specified in the paper, so rewards
are probabilities in [0,1]. All arithmetic in the proofs is exact over ℝ.
-/

noncomputable section

namespace TransparencyLean.SupermodularExample

open scoped BigOperators

abbrev Agent := Fin 2
abbrev State := Bool

def cost (i : Agent) : ℝ := if i = 0 then 1 / 4 else 1 / 2

def reward (ω : State) (S : Finset Agent) : ℝ :=
  if ω then
    if 0 ∈ S then (if 1 ∈ S then 5 / 6 else 5 / 42) else 0
  else
    if 0 ∈ S then (if 1 ∈ S then 1 else 1 / 4)
    else (if 1 ∈ S then 1 / 4 else 0)

def prior : FiniteDist State where
  prob _ := 1 / 2
  nonneg _ := by norm_num
  sum_eq_one := by norm_num [Fintype.sum_bool]

def opaqueContract (i : Agent) : ℝ := if i = 0 then 6 / 19 else 28 / 41

theorem cost_nonneg : ∀ i, 0 ≤ cost i := by
  intro i
  fin_cases i <;> norm_num [cost]

theorem reward_valid (ω : State) : ValidReward (reward ω) := by
  intro S
  cases ω <;> fin_cases S <;> norm_num [reward]

theorem reward_monotone (ω : State) : Monotone (reward ω) := by
  intro S T h
  have h0 : (0 : Agent) ∈ S → (0 : Agent) ∈ T := fun hi => h hi
  have h1 : (1 : Agent) ∈ S → (1 : Agent) ∈ T := fun hi => h hi
  cases ω <;> fin_cases S <;> fin_cases T <;> norm_num [reward] at h0 h1 ⊢

theorem reward_supermodular (ω : State) : Supermodular (reward ω) := by
  intro S T
  cases ω <;> fin_cases S <;> fin_cases T <;> norm_num [reward]

/-- Every feasible pure equilibrium in either revealed state gives payoff ≤ 0.
The empty team and zero contract attain zero. -/
theorem revealed_utility_nonpos (ω : State) (α : Agent → ℝ) (S : Finset Agent)
    (hα : FeasibleContract α) (hS : IsEquilibrium (reward ω) cost α S) :
    principalUtility (reward ω) α S ≤ 0 := by
  have h0 := hS.1 0
  have h1 := hS.1 1
  have ha0 := (hα 0).1
  have ha1 := (hα 1).1
  cases ω <;> fin_cases S <;>
    norm_num [reward, cost, principalUtility, Fin.sum_univ_two] at h0 h1 ⊢ <;>
    linarith

theorem revealed_value_zero (ω : State) : statelessValue (reward ω) cost = 0 := by
  apply le_antisymm
  · exact statelessValue_le cost_nonneg (revealed_utility_nonpos ω)
  · exact statelessValue_nonneg (reward_valid ω) cost_nonneg

theorem fullDisclosure_zero : fullDisclosureValue prior reward cost = 0 := by
  simp [fullDisclosureValue, revealed_value_zero]

theorem opaqueContract_feasible : FeasibleContract opaqueContract := by
  intro i
  fin_cases i <;> norm_num [opaqueContract]

theorem opaque_equilibrium :
    IsEquilibrium (posteriorReward prior reward) cost opaqueContract Finset.univ := by
  constructor
  · intro i _
    fin_cases i <;>
      norm_num [posteriorReward, FiniteDist.expect, prior, reward, cost,
        opaqueContract, Fintype.sum_bool]
  · simp

theorem opaque_utility :
    principalUtility (posteriorReward prior reward) opaqueContract Finset.univ =
      (11 / 9348 : ℝ) := by
  norm_num [principalUtility, posteriorReward, FiniteDist.expect, prior, reward,
    opaqueContract, Fin.sum_univ_two, Fintype.sum_bool]

theorem noDisclosure_positive : 0 < noDisclosureValue prior reward cost := by
  have h := utility_le_statelessValue (posteriorReward_valid prior reward_valid)
    opaqueContract_feasible opaque_equilibrium
  rw [opaque_utility] at h
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 11 / 9348) h

/-- Concrete exact certificate of paper Theorem 5.1. -/
theorem separation :
    (∀ ω, ValidReward (reward ω) ∧ Monotone (reward ω) ∧ Supermodular (reward ω)) ∧
    (∀ i, 0 ≤ cost i) ∧
    fullDisclosureValue prior reward cost = 0 ∧
    0 < noDisclosureValue prior reward cost := by
  exact ⟨fun ω => ⟨reward_valid ω, reward_monotone ω, reward_supermodular ω⟩,
    cost_nonneg, fullDisclosure_zero, noDisclosure_positive⟩

/-- No finite multiplicative factor bounds no disclosure by full disclosure. -/
theorem no_finite_factor (β : ℝ) :
    ¬ noDisclosureValue prior reward cost ≤ β * fullDisclosureValue prior reward cost := by
  rw [fullDisclosure_zero, mul_zero]
  exact not_le.mpr noDisclosure_positive

end TransparencyLean.SupermodularExample
