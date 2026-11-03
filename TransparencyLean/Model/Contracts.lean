import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Binary-action team contracts

Rewards may have a positive baseline; costs may be zero. Contracts constrain
each individual share to [0,1], exactly as in the paper. A bound on the total
share is not built into the model. Equilibria use weak incentive inequalities.
-/

namespace TransparencyLean

open scoped BigOperators

variable {Agent : Type*} [Fintype Agent] [DecidableEq Agent]

def ValidReward (f : Finset Agent → ℝ) : Prop := ∀ S, 0 ≤ f S ∧ f S ≤ 1

def Submodular (f : Finset Agent → ℝ) : Prop :=
  ∀ S T, f (S ∪ T) + f (S ∩ T) ≤ f S + f T

def Supermodular (f : Finset Agent → ℝ) : Prop :=
  ∀ S T, f S + f T ≤ f (S ∪ T) + f (S ∩ T)

def FeasibleContract (α : Agent → ℝ) : Prop := ∀ i, 0 ≤ α i ∧ α i ≤ 1

def agentUtility (f : Finset Agent → ℝ) (c α : Agent → ℝ)
    (S : Finset Agent) (i : Agent) : ℝ :=
  α i * f S - if i ∈ S then c i else 0

def principalUtility (f : Finset Agent → ℝ) (α : Agent → ℝ)
    (S : Finset Agent) : ℝ := (1 - ∑ i, α i) * f S

def IsEquilibrium (f : Finset Agent → ℝ) (c α : Agent → ℝ)
    (S : Finset Agent) : Prop :=
  (∀ i ∈ S, c i ≤ α i * (f S - f (S.erase i))) ∧
  (∀ i ∉ S, α i * (f (insert i S) - f S) ≤ c i)

omit [Fintype Agent] in
/-- The marginal formulation is exactly the unilateral-deviation definition. -/
theorem isEquilibrium_iff_bestResponse (f : Finset Agent → ℝ)
    (c α : Agent → ℝ) (S : Finset Agent) :
    IsEquilibrium f c α S ↔ ∀ i,
      agentUtility f c α (S.erase i) i ≤ agentUtility f c α S i ∧
      agentUtility f c α (insert i S) i ≤ agentUtility f c α S i := by
  constructor
  · rintro ⟨hin, hout⟩ i
    by_cases hi : i ∈ S
    · constructor
      · have h := hin i hi
        simp only [agentUtility, Finset.not_mem_erase, if_false, hi, if_true]
        nlinarith
      · simp [Finset.insert_eq_of_mem hi]
    · constructor
      · simp [Finset.erase_eq_of_not_mem hi]
      · have h := hout i hi
        simp only [agentUtility, Finset.mem_insert_self, if_true, hi, if_false]
        nlinarith
  · intro h
    constructor
    · intro i hi
      have h' := (h i).1
      simp only [agentUtility, Finset.not_mem_erase, if_false, hi, if_true] at h'
      nlinarith
    · intro i hi
      have h' := (h i).2
      simp only [agentUtility, Finset.mem_insert_self, if_true, hi, if_false] at h'
      nlinarith

omit [Fintype Agent] [DecidableEq Agent] in
theorem zero_feasible : FeasibleContract (fun _ : Agent => 0) := by
  intro i
  norm_num

omit [Fintype Agent] in
theorem empty_zero_equilibrium (f : Finset Agent → ℝ) (c : Agent → ℝ)
    (hc : ∀ i, 0 ≤ c i) : IsEquilibrium f c (fun _ => 0) ∅ := by
  constructor
  · simp
  · intro i _
    simpa using hc i

omit [DecidableEq Agent] in
@[simp] theorem principalUtility_zero (f : Finset Agent → ℝ) (S : Finset Agent) :
    principalUtility f (fun _ => 0) S = f S := by
  simp [principalUtility]

omit [DecidableEq Agent] in
theorem principalUtility_le_one {f : Finset Agent → ℝ} (hf : ValidReward f)
    {α : Agent → ℝ} (hα : FeasibleContract α) (S : Finset Agent) :
    principalUtility f α S ≤ 1 := by
  have hs : 0 ≤ ∑ i, α i := Finset.sum_nonneg (fun i _ => (hα i).1)
  have h0 := (hf S).1
  have h1 := (hf S).2
  unfold principalUtility
  nlinarith

/-- Utilities attainable by a feasible contract and a selected pure equilibrium.
Maximizing this set implements the paper's principal-favorable selection rule. -/
def achievableUtilities (f : Finset Agent → ℝ) (c : Agent → ℝ) : Set ℝ :=
  {u | ∃ α S, FeasibleContract α ∧ IsEquilibrium f c α S ∧
    principalUtility f α S = u}

noncomputable def statelessValue (f : Finset Agent → ℝ) (c : Agent → ℝ) : ℝ :=
  sSup (achievableUtilities f c)

theorem achievable_nonempty (f : Finset Agent → ℝ) (c : Agent → ℝ)
    (hc : ∀ i, 0 ≤ c i) : (achievableUtilities f c).Nonempty := by
  exact ⟨f ∅, (fun _ => 0), ∅, zero_feasible, empty_zero_equilibrium f c hc,
    principalUtility_zero f ∅⟩

theorem achievable_bddAbove {f : Finset Agent → ℝ} (hf : ValidReward f)
    (c : Agent → ℝ) : BddAbove (achievableUtilities f c) := by
  refine ⟨1, ?_⟩
  rintro u ⟨α, S, hα, _, rfl⟩
  exact principalUtility_le_one hf hα S

theorem utility_le_statelessValue {f : Finset Agent → ℝ} (hf : ValidReward f)
    {c α : Agent → ℝ} {S : Finset Agent}
    (hα : FeasibleContract α) (hS : IsEquilibrium f c α S) :
    principalUtility f α S ≤ statelessValue f c := by
  exact le_csSup (achievable_bddAbove hf c) ⟨α, S, hα, hS, rfl⟩

theorem statelessValue_le {f : Finset Agent → ℝ} {c : Agent → ℝ}
    (hc : ∀ i, 0 ≤ c i) {v : ℝ}
    (h : ∀ α S, FeasibleContract α → IsEquilibrium f c α S →
      principalUtility f α S ≤ v) : statelessValue f c ≤ v := by
  apply csSup_le (achievable_nonempty f c hc)
  rintro u ⟨α, S, hα, hS, rfl⟩
  exact h α S hα hS

theorem statelessValue_nonneg {f : Finset Agent → ℝ} (hf : ValidReward f)
    {c : Agent → ℝ} (hc : ∀ i, 0 ≤ c i) : 0 ≤ statelessValue f c := by
  have h := utility_le_statelessValue hf zero_feasible (empty_zero_equilibrium f c hc)
  rw [principalUtility_zero] at h
  exact (hf ∅).1.trans h

theorem statelessValue_le_one {f : Finset Agent → ℝ} (hf : ValidReward f)
    {c : Agent → ℝ} (hc : ∀ i, 0 ≤ c i) : statelessValue f c ≤ 1 := by
  exact statelessValue_le hc (fun α S hα _ => principalUtility_le_one hf hα S)

end TransparencyLean
