import TransparencyLean.Mixed.Contracts
import TransparencyLean.Information.FeasiblePayoffs

/-! Compactness gives an attained mixed stateless benchmark, including ties. -/

namespace TransparencyLean.Mixed

open scoped BigOperators
open Set

noncomputable section

variable {Agent : Type*} [Fintype Agent] [DecidableEq Agent]

omit [Fintype Agent] in
@[fun_prop] theorem continuous_sample (A : Finset Agent) (f : Finset Agent → ℝ) :
    Continuous (fun x => sample x A f) := by
  unfold sample sampleWeight
  fun_prop

@[fun_prop] theorem continuous_extension (f : Finset Agent → ℝ) : Continuous (extension f) :=
  continuous_sample _ f

@[fun_prop] theorem continuous_marginal (f : Finset Agent → ℝ) (i : Agent) :
    Continuous (fun x => marginal f x i) := continuous_sample _ _

@[fun_prop] theorem continuous_utility (f : Finset Agent → ℝ) :
    Continuous (fun z : (Agent → ℝ) × (Agent → ℝ) => utility f z.1 z.2) := by
  unfold utility
  fun_prop

/-- Polynomial inequalities describe equilibrium on the closed probability cube. -/
theorem equilibrium_complementarity {f : Finset Agent → ℝ} {c α x : Agent → ℝ}
    (hx : ValidProfile x) : IsMixedEquilibrium f c α x ↔
      ∀ i, x i * (c i - α i * marginal f x i) ≤ 0 ∧
        (1 - x i) * (α i * marginal f x i - c i) ≤ 0 := by
  constructor
  · rintro ⟨hw, hs⟩ i
    constructor
    · by_cases hi : 0 < x i
      · exact mul_nonpos_of_nonneg_of_nonpos (hx i).1 (sub_nonpos.mpr (hw i hi))
      · have hz : x i = 0 := le_antisymm (le_of_not_gt hi) (hx i).1
        simp [hz]
    · by_cases hi : x i < 1
      · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hx i).2) (sub_nonpos.mpr (hs i hi))
      · have hz : x i = 1 := le_antisymm (hx i).2 (le_of_not_gt hi)
        simp [hz]
  · intro h
    constructor
    · intro i hi
      have hh := (h i).1
      nlinarith
    · intro i hi
      have hh := (h i).2
      nlinarith

def feasibleDomain (f : Finset Agent → ℝ) (c : Agent → ℝ) : Set ((Agent → ℝ) × (Agent → ℝ)) :=
  {z | FeasibleContract z.1 ∧ ValidProfile z.2 ∧ IsMixedEquilibrium f c z.1 z.2}

theorem feasibleDomain_compact (f : Finset Agent → ℝ) (c : Agent → ℝ) :
    IsCompact (feasibleDomain f c) := by
  have hclosed : IsClosed {z : (Agent → ℝ) × (Agent → ℝ) |
      ∀ i, z.2 i * (c i - z.1 i * marginal f z.2 i) ≤ 0 ∧
        (1 - z.2 i) * (z.1 i * marginal f z.2 i - c i) ≤ 0} := by
    simp only [setOf_forall, setOf_and]
    apply isClosed_iInter
    intro i
    exact (isClosed_le (by fun_prop) continuous_const).inter
      (isClosed_le (by fun_prop) continuous_const)
  have heq : feasibleDomain f c =
      (Icc (fun _ => 0) (fun _ => 1) ×ˢ Icc (fun _ => 0) (fun _ => 1)) ∩
      {z | ∀ i, z.2 i * (c i - z.1 i * marginal f z.2 i) ≤ 0 ∧
        (1 - z.2 i) * (z.1 i * marginal f z.2 i - c i) ≤ 0} := by
    ext z
    constructor
    · rintro ⟨hα, hx, heq⟩
      exact ⟨⟨⟨fun i => (hα i).1, fun i => (hα i).2⟩,
        ⟨fun i => (hx i).1, fun i => (hx i).2⟩⟩, (equilibrium_complementarity hx).mp heq⟩
    · rintro ⟨⟨hα, hx⟩, heq⟩
      have hx' : ValidProfile z.2 := fun i => ⟨hx.1 i, hx.2 i⟩
      exact ⟨fun i => ⟨hα.1 i, hα.2 i⟩, hx', (equilibrium_complementarity hx').mpr heq⟩
  rw [heq]
  exact (isCompact_Icc.prod isCompact_Icc).inter_right hclosed

/-- The mixed stateless supremum is a maximum over actual contracts and profiles. -/
theorem statelessValue_attained {f : Finset Agent → ℝ} (hf : ValidReward f)
    {c : Agent → ℝ} (hc : ∀ i, 0 ≤ c i) :
    ∃ α x, FeasibleContract α ∧ ValidProfile x ∧ IsMixedEquilibrium f c α x ∧
      utility f α x = statelessValue f c := by
  have hne : (feasibleDomain f c).Nonempty :=
    ⟨(fun _ => 0, pureProfile ∅), zero_feasible, pureProfile_valid ∅,
      (pure_equilibrium_iff f c _ ∅).mpr (empty_zero_equilibrium f c hc)⟩
  obtain ⟨z, hz, hmax⟩ := (feasibleDomain_compact f c).exists_isMaxOn hne
    (continuous_utility f).continuousOn
  refine ⟨z.1, z.2, hz.1, hz.2.1, hz.2.2,
    le_antisymm (utility_le_statelessValue hf hz.1 hz.2.1 hz.2.2) ?_⟩
  apply statelessValue_le hc
  intro α x hα hx heq
  exact hmax (show (α, x) ∈ feasibleDomain f c from ⟨hα, hx, heq⟩)

end

end TransparencyLean.Mixed
