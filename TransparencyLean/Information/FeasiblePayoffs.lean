import TransparencyLean.Information.Contracts
import TransparencyLean.Information.CompactConvex

namespace TransparencyLean

open scoped BigOperators
open Set

noncomputable section

variable {Ω Agent : Type*} [Fintype Ω] [Fintype Agent] [DecidableEq Agent]

/-- Raw probability vectors give the simplex its ordinary Euclidean topology. -/
def probabilityVectors (Ω : Type*) [Fintype Ω] : Set (Ω → ℝ) :=
  {q | (∀ ω, 0 ≤ q ω) ∧ ∑ ω, q ω = 1}

theorem probabilityVectors_compact : IsCompact (probabilityVectors Ω) := by
  have heq : probabilityVectors Ω =
      Icc (fun _ => 0) (fun _ => 1) ∩ {q : Ω → ℝ | ∑ ω, q ω = 1} := by
    ext q
    constructor
    · intro h
      refine ⟨⟨h.1, ?_⟩, h.2⟩
      intro ω
      exact (Finset.single_le_sum (fun η _ => h.1 η) (Finset.mem_univ ω)).trans_eq h.2
    · exact fun h => ⟨h.1.1, h.2⟩
  rw [heq]
  exact isCompact_Icc.inter_right (isClosed_eq (by fun_prop) continuous_const)

def rewardAt (q : Ω → ℝ) (f : Ω → Finset Agent → ℝ) (S : Finset Agent) : ℝ :=
  ∑ ω, q ω * f ω S

omit [Fintype Agent] [DecidableEq Agent] in
@[fun_prop] theorem continuous_rewardAt (f : Ω → Finset Agent → ℝ) (S : Finset Agent) :
    Continuous (fun q => rewardAt q f S) := by
  unfold rewardAt
  fun_prop

abbrev PosteriorPayoff (Ω : Type*) := (Ω → ℝ) × ℝ

def feasibleDomain (f : Ω → Finset Agent → ℝ) (c : Agent → ℝ) (S : Finset Agent) :
    Set ((Ω → ℝ) × (Agent → ℝ)) :=
  {a | a.1 ∈ probabilityVectors Ω ∧ FeasibleContract a.2 ∧
    IsEquilibrium (rewardAt a.1 f) c a.2 S}

def payoffMap (f : Ω → Finset Agent → ℝ) (S : Finset Agent)
    (a : (Ω → ℝ) × (Agent → ℝ)) : PosteriorPayoff Ω :=
  (a.1, principalUtility (rewardAt a.1 f) a.2 S)

def feasiblePayoffs (f : Ω → Finset Agent → ℝ) (c : Agent → ℝ) : Set (PosteriorPayoff Ω) :=
  ⋃ S : Finset Agent, payoffMap f S '' feasibleDomain f c S

omit [Fintype Agent] in
theorem feasibleDomain_compact (f : Ω → Finset Agent → ℝ) (c : Agent → ℝ)
    (S : Finset Agent) : IsCompact (feasibleDomain f c S) := by
  have hcontract : IsCompact {α : Agent → ℝ | FeasibleContract α} := by
    have heq : {α : Agent → ℝ | FeasibleContract α} = Icc (fun _ => 0) (fun _ => 1) := by
      ext α
      exact forall_and
    rw [heq]
    exact isCompact_Icc
  have hclosed : IsClosed {a : (Ω → ℝ) × (Agent → ℝ) |
      IsEquilibrium (rewardAt a.1 f) c a.2 S} := by
    simp only [IsEquilibrium, Set.setOf_and, Set.setOf_forall]
    apply IsClosed.inter
    · apply isClosed_iInter
      intro i
      apply isClosed_iInter
      intro _
      exact isClosed_le continuous_const (by fun_prop)
    · apply isClosed_iInter
      intro i
      apply isClosed_iInter
      intro _
      exact isClosed_le (by fun_prop) continuous_const
  have heq : feasibleDomain f c S =
      (probabilityVectors Ω ×ˢ {α | FeasibleContract α}) ∩
        {a | IsEquilibrium (rewardAt a.1 f) c a.2 S} := by
    ext a
    exact and_assoc.symm
  rw [heq]
  exact (probabilityVectors_compact.prod hcontract).inter_right hclosed

omit [DecidableEq Agent] in
@[fun_prop] theorem continuous_payoffMap (f : Ω → Finset Agent → ℝ) (S : Finset Agent) :
    Continuous (payoffMap f S) := by
  unfold payoffMap principalUtility
  fun_prop

theorem feasiblePayoffs_compact (f : Ω → Finset Agent → ℝ) (c : Agent → ℝ) :
    IsCompact (feasiblePayoffs f c) := by
  apply isCompact_iUnion
  intro S
  exact (feasibleDomain_compact f c S).image (continuous_payoffMap f S)

theorem mem_feasiblePayoffs_iff (f : Ω → Finset Agent → ℝ) (c : Agent → ℝ)
    (x : PosteriorPayoff Ω) :
    x ∈ feasiblePayoffs f c ↔ ∃ (q : FiniteDist Ω) (α : Agent → ℝ) (S : Finset Agent),
      FeasibleContract α ∧ IsEquilibrium (posteriorReward q f) c α S ∧
      q.prob = x.1 ∧ principalUtility (posteriorReward q f) α S = x.2 := by
  constructor
  · intro hx
    obtain ⟨S, a, ha, hax⟩ := Set.mem_iUnion.mp hx
    let q : FiniteDist Ω := ⟨a.1, ha.1.1, ha.1.2⟩
    refine ⟨q, a.2, S, ha.2.1, ha.2.2, ?_, ?_⟩
    · exact congrArg Prod.fst hax
    · exact congrArg Prod.snd hax
  · rintro ⟨q, α, S, hα, hS, hq, hu⟩
    refine Set.mem_iUnion.mpr ⟨S, (q.prob, α), ⟨⟨q.nonneg, q.sum_eq_one⟩, hα, hS⟩, ?_⟩
    exact Prod.ext hq hu

theorem feasiblePayoffs_convexHull_compact (f : Ω → Finset Agent → ℝ) (c : Agent → ℝ) :
    IsCompact (convexHull ℝ (feasiblePayoffs f c)) :=
  compact_convexHull (feasiblePayoffs_compact f c)

end

end TransparencyLean
