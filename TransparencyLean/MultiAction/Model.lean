import TransparencyLean.Model.FiniteProbability
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact

/-! A single agent with finitely many actions and arbitrary nonnegative expected
rewards. Linear shares lie in [0,1]; ties are selected in the principal's favor.
No upper bound of one is imposed on expected rewards. -/

namespace TransparencyLean.MultiAction

open scoped BigOperators
open Set
noncomputable section

variable {A : Type*} [Fintype A] [Nonempty A]

def FeasibleShare (α : ℝ) : Prop := 0 ≤ α ∧ α ≤ 1

def BestResponse (r c : A → ℝ) (α : ℝ) (i : A) : Prop :=
  ∀ j, α * r j - c j ≤ α * r i - c i

def payoff (r : A → ℝ) (α : ℝ) (i : A) : ℝ := (1 - α) * r i

theorem bestResponse_exists (r c : A → ℝ) (α : ℝ) :
    ∃ i, BestResponse r c α i := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.univ.exists_max_image (fun j => α * r j - c j)
    Finset.univ_nonempty
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

def achievable (r c : A → ℝ) : Set ℝ :=
  {u | ∃ α i, FeasibleShare α ∧ BestResponse r c α i ∧ payoff r α i = u}

def value (r c : A → ℝ) : ℝ := sSup (achievable r c)

theorem achievable_nonempty (r c : A → ℝ) : (achievable r c).Nonempty := by
  obtain ⟨i, hi⟩ := bestResponse_exists r c 0
  exact ⟨payoff r 0 i, 0, i, ⟨le_rfl, zero_le_one⟩, hi, rfl⟩

omit [Fintype A] [Nonempty A] in
theorem payoff_nonneg {r : A → ℝ} (hr : ∀ i, 0 ≤ r i) {α : ℝ}
    (hα : FeasibleShare α) (i : A) : 0 ≤ payoff r α i :=
  mul_nonneg (sub_nonneg.mpr hα.2) (hr i)

omit [Fintype A] [Nonempty A] in
theorem payoff_le_reward {r : A → ℝ} (hr : ∀ i, 0 ≤ r i) {α : ℝ}
    (hα : FeasibleShare α) (i : A) : payoff r α i ≤ r i := by
  dsimp [payoff]
  nlinarith [mul_nonneg hα.1 (hr i)]

omit [Nonempty A] in
theorem achievable_bddAbove {r c : A → ℝ} (hr : ∀ i, 0 ≤ r i) :
    BddAbove (achievable r c) := by
  classical
  refine ⟨∑ i, r i, ?_⟩
  rintro u ⟨α, i, hα, _, rfl⟩
  exact (payoff_le_reward hr hα i).trans
    (Finset.single_le_sum (fun j _ => hr j) (Finset.mem_univ i))

omit [Nonempty A] in
theorem payoff_le_value {r c : A → ℝ} (hr : ∀ i, 0 ≤ r i) {α : ℝ} {i : A}
    (hα : FeasibleShare α) (hi : BestResponse r c α i) : payoff r α i ≤ value r c :=
  le_csSup (achievable_bddAbove hr) ⟨α, i, hα, hi, rfl⟩

theorem value_le {r c : A → ℝ} {v : ℝ}
    (h : ∀ α i, FeasibleShare α → BestResponse r c α i → payoff r α i ≤ v) :
    value r c ≤ v := by
  apply csSup_le (achievable_nonempty r c)
  rintro u ⟨α, i, hα, hi, rfl⟩
  exact h α i hα hi

theorem value_nonneg {r c : A → ℝ} (hr : ∀ i, 0 ≤ r i) : 0 ≤ value r c := by
  obtain ⟨i, hi⟩ := bestResponse_exists r c 0
  exact (payoff_nonneg hr ⟨le_rfl, zero_le_one⟩ i).trans
    (payoff_le_value hr ⟨le_rfl, zero_le_one⟩ hi)

omit [Nonempty A] in
theorem achievable_compact (r c : A → ℝ) : IsCompact (achievable r c) := by
  have hdom (i : A) : IsCompact {α : ℝ | FeasibleShare α ∧ BestResponse r c α i} := by
    have hclosed : IsClosed {α : ℝ | BestResponse r c α i} := by
      simp only [BestResponse, setOf_forall]
      exact isClosed_iInter fun j => isClosed_le (by fun_prop) (by fun_prop)
    exact isCompact_Icc.inter_right hclosed
  have heq : achievable r c = ⋃ i : A,
      (fun α => payoff r α i) '' {α | FeasibleShare α ∧ BestResponse r c α i} := by
    ext u
    simp only [achievable, mem_setOf_eq, mem_iUnion, mem_image]
    constructor
    · rintro ⟨α, i, hα, hi, hu⟩
      exact ⟨i, α, ⟨hα, hi⟩, hu⟩
    · rintro ⟨i, α, ⟨hα, hi⟩, hu⟩
      exact ⟨α, i, hα, hi, hu⟩
  rw [heq]
  exact isCompact_iUnion fun i => (hdom i).image (by unfold payoff; fun_prop)

theorem value_attained (r c : A → ℝ) :
    ∃ α i, FeasibleShare α ∧ BestResponse r c α i ∧ payoff r α i = value r c :=
  (achievable_compact r c).sSup_mem (achievable_nonempty r c)

omit [Fintype A] [Nonempty A] in
/-- Adding a common amount to all costs does not change incentives or revenue. -/
theorem cost_shift (r c : A → ℝ) (d : ℝ) :
    value r (fun i => c i - d) = value r c := by
  have h : ∀ α i, BestResponse r (fun j => c j - d) α i ↔ BestResponse r c α i := by
    intro α i
    simp only [BestResponse]
    constructor <;> intro h j <;> specialize h j <;> linarith
  simp only [value, achievable, h]

/-- The paper's zero-minimum-cost normalization is without loss. -/
theorem cost_normalization (c : A → ℝ) :
    ∃ d : ℝ, (∀ i, 0 ≤ c i - d) ∧ (∃ i, c i - d = 0) ∧
      ∀ r : A → ℝ, value r (fun i => c i - d) = value r c := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.univ.exists_min_image c Finset.univ_nonempty
  exact ⟨c i, fun j => sub_nonneg.mpr (hi j (Finset.mem_univ j)),
    ⟨i, sub_self _⟩, fun r => cost_shift r c _⟩

def MixedBestResponse (r c : A → ℝ) (α : ℝ) (p : FiniteDist A) : Prop :=
  ∀ i, 0 < p.prob i → BestResponse r c α i

omit [Nonempty A] in
theorem mixedBestResponse_iff_pureDeviation (r c : A → ℝ) (α : ℝ) (p : FiniteDist A) :
    MixedBestResponse r c α p ↔
      ∀ j, α * r j - c j ≤ p.expect (fun i => α * r i - c i) := by
  classical
  let u := fun i => α * r i - c i
  constructor
  · intro h j
    change u j ≤ p.expect u
    rw [← p.expect_const (u j)]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : 0 < p.prob i
    · exact mul_le_mul_of_nonneg_left (h i hi j) (p.nonneg i)
    · have hz : p.prob i = 0 := le_antisymm (le_of_not_gt hi) (p.nonneg i)
      simp [hz]
  · intro h i hi j
    have hzero : p.expect (fun k => p.expect u - u k) = 0 := by
      rw [p.expect_sub, p.expect_const, sub_self]
    have hnonneg : ∀ k, 0 ≤ p.prob k * (p.expect u - u k) :=
      fun k => mul_nonneg (p.nonneg k) (sub_nonneg.mpr (h k))
    have ht : p.prob i * (p.expect u - u i) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hnonneg k)).mp hzero i (Finset.mem_univ i)
    have heq : p.expect u = u i := by nlinarith
    change u j ≤ u i
    rw [← heq]
    exact h j

omit [Nonempty A] in
/-- Support on pure best responses is equivalent to optimality against every
alternative mixed action, rather than merely a definition of equilibrium. -/
theorem mixedBestResponse_iff (r c : A → ℝ) (α : ℝ) (p : FiniteDist A) :
    MixedBestResponse r c α p ↔ ∀ q : FiniteDist A,
      q.expect (fun i => α * r i - c i) ≤ p.expect (fun i => α * r i - c i) := by
  classical
  rw [mixedBestResponse_iff_pureDeviation]
  constructor
  · intro h q
    exact (q.expect_mono h).trans_eq (q.expect_const _)
  · intro h j
    simpa using h (FiniteDist.pointMass j)

omit [Nonempty A] in
/-- A mixed best response can be replaced by a pure best response with at
least as much principal revenue, at the same share. -/
theorem mixed_dominated {r c : A → ℝ} {α : ℝ} (p : FiniteDist A)
    (hp : MixedBestResponse r c α p) :
    ∃ i, BestResponse r c α i ∧ p.expect (payoff r α) ≤ payoff r α i := by
  classical
  let S := Finset.univ.filter (fun i => 0 < p.prob i)
  have hS : S.Nonempty := by
    by_contra h
    have hz : ∀ i, p.prob i = 0 := by
      intro i
      have hn : ¬ 0 < p.prob i := by
        intro hi
        exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
      exact le_antisymm (le_of_not_gt hn) (p.nonneg i)
    simpa [hz] using p.sum_eq_one
  obtain ⟨i, hi, hmax⟩ := S.exists_max_image (payoff r α) hS
  refine ⟨i, hp i (Finset.mem_filter.mp hi).2, ?_⟩
  rw [← p.expect_const (payoff r α i)]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : 0 < p.prob j
  · exact mul_le_mul_of_nonneg_left
      (hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)) (p.nonneg j)
  · have hz : p.prob j = 0 := le_antisymm (le_of_not_gt hj) (p.nonneg j)
    simp [hz]

end
end TransparencyLean.MultiAction
