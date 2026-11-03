import TransparencyLean.Mixed.KernelSignals

/-! Exact finite reduction and optimal joint-scheme attainment with mixed equilibria. -/

namespace TransparencyLean.Mixed

open scoped BigOperators
open Set MeasureTheory

noncomputable section

variable {Ω Agent : Type*} [Fintype Ω] [Fintype Agent] [DecidableEq Agent]

abbrev PosteriorChoice (Ω Agent : Type*) := (Ω → ℝ) × ((Agent → ℝ) × (Agent → ℝ))

def posteriorDomain (f : Ω → Finset Agent → ℝ) (c : Agent → ℝ) : Set (PosteriorChoice Ω Agent) :=
  {z | z.1 ∈ probabilityVectors Ω ∧ FeasibleContract z.2.1 ∧ ValidProfile z.2.2 ∧
    IsMixedEquilibrium (rewardAt z.1 f) c z.2.1 z.2.2}

def payoffMap (f : Ω → Finset Agent → ℝ) (z : PosteriorChoice Ω Agent) : PosteriorPayoff Ω :=
  (z.1, utility (rewardAt z.1 f) z.2.1 z.2.2)

def feasiblePayoffs (f : Ω → Finset Agent → ℝ) (c : Agent → ℝ) : Set (PosteriorPayoff Ω) :=
  payoffMap f '' posteriorDomain f c

@[fun_prop] theorem continuous_joint_marginal (f : Ω → Finset Agent → ℝ) (i : Agent) :
    Continuous (fun z : PosteriorChoice Ω Agent => marginal (rewardAt z.1 f) z.2.2 i) := by
  unfold marginal sample sampleWeight rewardAt
  fun_prop

@[fun_prop] theorem continuous_payoffMap (f : Ω → Finset Agent → ℝ) : Continuous (payoffMap f) := by
  unfold payoffMap utility extension sample sampleWeight rewardAt
  fun_prop

theorem posteriorDomain_compact (f : Ω → Finset Agent → ℝ) (c : Agent → ℝ) :
    IsCompact (posteriorDomain f c) := by
  have hclosed : IsClosed {z : PosteriorChoice Ω Agent |
      ∀ i, z.2.2 i * (c i - z.2.1 i * marginal (rewardAt z.1 f) z.2.2 i) ≤ 0 ∧
        (1 - z.2.2 i) * (z.2.1 i * marginal (rewardAt z.1 f) z.2.2 i - c i) ≤ 0} := by
    simp only [setOf_forall, setOf_and]
    apply isClosed_iInter
    intro i
    exact (isClosed_le (by fun_prop) continuous_const).inter
      (isClosed_le (by fun_prop) continuous_const)
  have heq : posteriorDomain f c =
      (probabilityVectors Ω ×ˢ
        (Icc (fun _ => 0) (fun _ => 1) ×ˢ Icc (fun _ => 0) (fun _ => 1))) ∩
      {z | ∀ i, z.2.2 i * (c i - z.2.1 i * marginal (rewardAt z.1 f) z.2.2 i) ≤ 0 ∧
        (1 - z.2.2 i) * (z.2.1 i * marginal (rewardAt z.1 f) z.2.2 i - c i) ≤ 0} := by
    ext z
    constructor
    · rintro ⟨hq, hα, hx, heq⟩
      exact ⟨⟨hq, ⟨⟨fun i => (hα i).1, fun i => (hα i).2⟩,
        ⟨fun i => (hx i).1, fun i => (hx i).2⟩⟩⟩, (equilibrium_complementarity hx).mp heq⟩
    · rintro ⟨⟨hq, hα, hx⟩, heq⟩
      have hx' : ValidProfile z.2.2 := fun i => ⟨hx.1 i, hx.2 i⟩
      exact ⟨hq, fun i => ⟨hα.1 i, hα.2 i⟩, hx', (equilibrium_complementarity hx').mpr heq⟩
  rw [heq]
  exact (probabilityVectors_compact.prod (isCompact_Icc.prod isCompact_Icc)).inter_right hclosed

theorem feasiblePayoffs_compact (f : Ω → Finset Agent → ℝ) (c : Agent → ℝ) :
    IsCompact (feasiblePayoffs f c) :=
  (posteriorDomain_compact f c).image (continuous_payoffMap f)

theorem mem_feasiblePayoffs_iff (f : Ω → Finset Agent → ℝ) (c : Agent → ℝ) (z : PosteriorPayoff Ω) :
    z ∈ feasiblePayoffs f c ↔ ∃ (q : FiniteDist Ω) (α x : Agent → ℝ),
      FeasibleContract α ∧ ValidProfile x ∧ IsMixedEquilibrium (posteriorReward q f) c α x ∧
      q.prob = z.1 ∧ utility (posteriorReward q f) α x = z.2 := by
  constructor
  · rintro ⟨a, ha, haz⟩
    let q : FiniteDist Ω := ⟨a.1, ha.1.1, ha.1.2⟩
    exact ⟨q, a.2.1, a.2.2, ha.2.1, ha.2.2.1, ha.2.2.2,
      congrArg Prod.fst haz, congrArg Prod.snd haz⟩
  · rintro ⟨q, α, x, hα, hx, heq, hq, hu⟩
    exact ⟨(q.prob, α, x), ⟨⟨q.nonneg, q.sum_eq_one⟩, hα, hx, heq⟩, Prod.ext hq hu⟩

theorem finite_scheme_of_mem_convexHull (prior : FiniteDist Ω)
    {f : Ω → Finset Agent → ℝ} {c : Agent → ℝ} {u : ℝ}
    (hu : (prior.prob, u) ∈ convexHull ℝ (feasiblePayoffs f c)) :
    ∃ scheme : ContractScheme prior f c (Fin (supportBound Ω)), scheme.utility = u := by
  classical
  obtain ⟨w, z, hw, hsum, hz, hmean⟩ := convexHull_fixed_mixture hu
  choose q α x hα hx heq hq hv using fun i => (mem_feasiblePayoffs_iff f c (z i)).mp (hz i)
  let weights : FiniteDist (Fin (supportBound Ω)) := ⟨w, hw, hsum⟩
  have hplausible : ∀ ω, weights.expect (fun i => (q i).prob ω) = prior.prob ω := by
    intro ω
    have hh := congrArg (fun v : PosteriorPayoff Ω => v.1 ω) hmean
    simpa [FiniteDist.expect, weights, hq, Prod.fst_sum, Finset.sum_apply] using hh
  let scheme : ContractScheme prior f c (Fin (supportBound Ω)) := {
    information := ⟨weights, q, hplausible⟩
    contract := α
    profile := x
    feasible := hα
    valid := hx
    equilibrium := heq
  }
  refine ⟨scheme, ?_⟩
  have hh := congrArg Prod.snd hmean
  simpa [ContractScheme.utility, scheme, FiniteDist.expect, weights, hv, Prod.snd_sum] using hh

namespace KernelContractScheme

variable {Signal : Type*} [MeasurableSpace Signal]
variable {prior : FiniteDist Ω} {f : Ω → Finset Agent → ℝ} {c : Agent → ℝ}

def outcome (scheme : KernelContractScheme prior f c Signal) (s : Signal) : PosteriorPayoff Ω :=
  ((scheme.kernel.posterior prior s).prob,
    Mixed.utility (posteriorReward (scheme.kernel.posterior prior s) f) (scheme.contract s) (scheme.profile s))

theorem ae_outcome_mem (scheme : KernelContractScheme prior f c Signal) :
    ∀ᵐ s ∂scheme.kernel.signalLaw prior, scheme.outcome s ∈ feasiblePayoffs f c := by
  filter_upwards [scheme.feasible, scheme.valid, scheme.equilibrium] with s hα hx heq
  exact (mem_feasiblePayoffs_iff f c _).mpr
    ⟨scheme.kernel.posterior prior s, scheme.contract s, scheme.profile s, hα, hx, heq, rfl, rfl⟩

theorem outcome_integrable (scheme : KernelContractScheme prior f c Signal) :
    Integrable scheme.outcome (scheme.kernel.signalLaw prior) := by
  obtain ⟨M, hM⟩ := (feasiblePayoffs_compact f c).isBounded.exists_norm_le
  apply (integrable_const M).mono'
    ((scheme.kernel.posterior_measurable prior).aestronglyMeasurable.prodMk scheme.measurable_payoff)
  exact scheme.ae_outcome_mem.mono (fun _ h => hM _ h)

theorem integral_outcome (scheme : KernelContractScheme prior f c Signal) :
    (∫ s, scheme.outcome s ∂scheme.kernel.signalLaw prior) = (prior.prob, scheme.utility) := by
  apply Prod.ext
  · ext ω
    rw [fst_integral scheme.outcome_integrable]
    have heval := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Ω => ℝ) ω).integral_comp_comm
      scheme.outcome_integrable.fst
    exact heval.symm.trans (scheme.kernel.posterior_plausible prior ω)
  · exact snd_integral scheme.outcome_integrable

theorem mean_mem_convexHull (scheme : KernelContractScheme prior f c Signal) :
    (prior.prob, scheme.utility) ∈ convexHull ℝ (feasiblePayoffs f c) := by
  have h := (convex_convexHull ℝ (feasiblePayoffs f c)).integral_mem
    (compact_convexHull (feasiblePayoffs_compact f c)).isClosed
    (scheme.ae_outcome_mem.mono (fun _ h => subset_convexHull ℝ _ h)) scheme.outcome_integrable
  rwa [scheme.integral_outcome] at h

/-- Exact finite replacement preserves prior and mixed-equilibrium utility. -/
theorem finite_equivalent (scheme : KernelContractScheme prior f c Signal) :
    ∃ finite : ContractScheme prior f c (Fin (supportBound Ω)), finite.utility = scheme.utility :=
  finite_scheme_of_mem_convexHull prior scheme.mean_mem_convexHull

end KernelContractScheme

/-- The finite-signal attainment footnote also holds with mixed equilibrium
selection: one finite public kernel dominates every admissible measurable scheme. -/
theorem kernel_optimum_attained (prior : FiniteDist Ω) (f : Ω → Finset Agent → ℝ)
    (c : Agent → ℝ) (hc : ∀ i, 0 ≤ c i) :
    ∃ optimal : KernelContractScheme prior f c (Fin (supportBound Ω)),
      ∀ (Signal : Type*) [MeasurableSpace Signal]
        (scheme : KernelContractScheme prior f c Signal), scheme.utility ≤ optimal.utility := by
  let C := convexHull ℝ (feasiblePayoffs f c) ∩ {z | z.1 = prior.prob}
  have hC : IsCompact C := (compact_convexHull (feasiblePayoffs_compact f c)).inter_right
    (isClosed_eq continuous_fst continuous_const)
  have hbase : (prior.prob, posteriorReward prior f ∅) ∈ feasiblePayoffs f c := by
    apply (mem_feasiblePayoffs_iff f c _).mpr
    refine ⟨prior, fun _ => 0, pureProfile ∅, zero_feasible, pureProfile_valid ∅,
      (pure_equilibrium_iff _ _ _ _).mpr (empty_zero_equilibrium _ c hc), rfl, ?_⟩
    simp
  have hne : C.Nonempty := ⟨(prior.prob, posteriorReward prior f ∅), subset_convexHull ℝ _ hbase, rfl⟩
  obtain ⟨z, hz, hmax⟩ := hC.exists_isMaxOn hne continuous_snd.continuousOn
  have hu : (prior.prob, z.2) ∈ convexHull ℝ (feasiblePayoffs f c) := by
    have heq : (prior.prob, z.2) = z := Prod.ext hz.2.symm rfl
    rw [heq]
    exact hz.1
  obtain ⟨finite, hfinite⟩ := finite_scheme_of_mem_convexHull prior hu
  refine ⟨finite.toKernelContract, ?_⟩
  intro Signal _ scheme
  rw [ContractScheme.toKernelContract_utility, hfinite]
  exact hmax (show (prior.prob, scheme.utility) ∈ C from ⟨scheme.mean_mem_convexHull, rfl⟩)

end

end TransparencyLean.Mixed
