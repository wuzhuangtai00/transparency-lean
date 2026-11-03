import TransparencyLean.MultiAction.Information

/-! Exact finite support and joint optimum attainment for the multi-action
model, with arbitrary selected mixed best responses. -/

namespace TransparencyLean.MultiAction

open scoped BigOperators
open Set MeasureTheory
noncomputable section

variable {Ω A : Type*} [Fintype Ω] [Fintype A] [Nonempty A] [DecidableEq A]

omit [Nonempty A] [DecidableEq A] in
theorem mixed_complementarity (r c : A → ℝ) (α : ℝ) (p : FiniteDist A) :
    MixedBestResponse r c α p ↔
      ∀ i j, p.prob i * (α * r j - c j - (α * r i - c i)) ≤ 0 := by
  constructor
  · intro h i j
    by_cases hi : 0 < p.prob i
    · exact mul_nonpos_of_nonneg_of_nonpos (p.nonneg i) (sub_nonpos.mpr (h i hi j))
    · have hz : p.prob i = 0 := le_antisymm (le_of_not_gt hi) (p.nonneg i)
      simp [hz]
  · intro h i hi j
    have hh := h i j
    nlinarith

abbrev PosteriorChoice (Ω A : Type*) := (Ω → ℝ) × (ℝ × (A → ℝ))

def meanAt (q : Ω → ℝ) (r : Ω → A → ℝ) (i : A) : ℝ := ∑ ω, q ω * r ω i

def posteriorDomain (r : Ω → A → ℝ) (c : A → ℝ) : Set (PosteriorChoice Ω A) :=
  {z | z.1 ∈ probabilityVectors Ω ∧ FeasibleShare z.2.1 ∧ z.2.2 ∈ probabilityVectors A ∧
    ∀ i j, z.2.2 i * (z.2.1 * meanAt z.1 r j - c j - (z.2.1 * meanAt z.1 r i - c i)) ≤ 0}

def payoffMap (r : Ω → A → ℝ) (z : PosteriorChoice Ω A) : PosteriorPayoff Ω :=
  (z.1, ∑ i, z.2.2 i * payoff (meanAt z.1 r) z.2.1 i)

def feasiblePayoffs (r : Ω → A → ℝ) (c : A → ℝ) : Set (PosteriorPayoff Ω) :=
  payoffMap r '' posteriorDomain r c

omit [Nonempty A] [DecidableEq A] in
@[fun_prop] theorem continuous_payoffMap (r : Ω → A → ℝ) : Continuous (payoffMap r) := by
  unfold payoffMap payoff meanAt
  fun_prop

omit [Nonempty A] [DecidableEq A] in
theorem posteriorDomain_compact (r : Ω → A → ℝ) (c : A → ℝ) :
    IsCompact (posteriorDomain r c) := by
  have hclosed : IsClosed {z : PosteriorChoice Ω A |
      ∀ i j, z.2.2 i * (z.2.1 * meanAt z.1 r j - c j - (z.2.1 * meanAt z.1 r i - c i)) ≤ 0} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le (by unfold meanAt; fun_prop) continuous_const
  have heq : posteriorDomain r c =
      (probabilityVectors Ω ×ˢ (Icc 0 1 ×ˢ probabilityVectors A)) ∩
      {z | ∀ i j, z.2.2 i * (z.2.1 * meanAt z.1 r j - c j - (z.2.1 * meanAt z.1 r i - c i)) ≤ 0} := by
    ext z
    simp only [posteriorDomain, mem_setOf_eq, mem_inter_iff, mem_prod, mem_Icc, FeasibleShare]
    tauto
  rw [heq]
  exact (probabilityVectors_compact.prod (isCompact_Icc.prod probabilityVectors_compact)).inter_right hclosed

omit [Nonempty A] [DecidableEq A] in
theorem feasiblePayoffs_compact (r : Ω → A → ℝ) (c : A → ℝ) :
    IsCompact (feasiblePayoffs r c) :=
  (posteriorDomain_compact r c).image (continuous_payoffMap r)

omit [Nonempty A] [DecidableEq A] in
theorem mem_feasiblePayoffs_iff (r : Ω → A → ℝ) (c : A → ℝ) (z : PosteriorPayoff Ω) :
    z ∈ feasiblePayoffs r c ↔ ∃ (q : FiniteDist Ω) (α : ℝ) (p : FiniteDist A),
      FeasibleShare α ∧ MixedBestResponse (meanReward q r) c α p ∧
      q.prob = z.1 ∧ p.expect (payoff (meanReward q r) α) = z.2 := by
  constructor
  · rintro ⟨a, ha, haz⟩
    let q : FiniteDist Ω := ⟨a.1, ha.1.1, ha.1.2⟩
    let p : FiniteDist A := ⟨a.2.2, ha.2.2.1.1, ha.2.2.1.2⟩
    exact ⟨q, a.2.1, p, ha.2.1, (mixed_complementarity _ _ _ _).mpr ha.2.2.2,
      congrArg Prod.fst haz, congrArg Prod.snd haz⟩
  · rintro ⟨q, α, p, hα, heq, hq, hu⟩
    exact ⟨(q.prob, α, p.prob), ⟨⟨q.nonneg, q.sum_eq_one⟩, hα,
      ⟨p.nonneg, p.sum_eq_one⟩, (mixed_complementarity _ _ _ _).mp heq⟩, Prod.ext hq hu⟩

omit [Nonempty A] [DecidableEq A] in
theorem finite_scheme_of_mem_convexHull (prior : FiniteDist Ω)
    {r : Ω → A → ℝ} {c : A → ℝ} {u : ℝ}
    (hu : (prior.prob, u) ∈ convexHull ℝ (feasiblePayoffs r c)) :
    ∃ scheme : ContractScheme prior r c (Fin (supportBound Ω)), scheme.utility = u := by
  classical
  obtain ⟨w, z, hw, hsum, hz, hmean⟩ := convexHull_fixed_mixture hu
  choose q α p hα heq hq hv using fun i => (mem_feasiblePayoffs_iff r c (z i)).mp (hz i)
  let weights : FiniteDist (Fin (supportBound Ω)) := ⟨w, hw, hsum⟩
  have hplausible : ∀ ω, weights.expect (fun i => (q i).prob ω) = prior.prob ω := by
    intro ω
    have hh := congrArg (fun v : PosteriorPayoff Ω => v.1 ω) hmean
    simpa [FiniteDist.expect, weights, hq, Prod.fst_sum, Finset.sum_apply] using hh
  let scheme : ContractScheme prior r c (Fin (supportBound Ω)) := {
    information := ⟨weights, q, hplausible⟩
    share := α
    response := p
    feasible := hα
    equilibrium := heq }
  refine ⟨scheme, ?_⟩
  have hh := congrArg Prod.snd hmean
  change (∑ i, w i * (p i).expect (payoff (meanReward (q i) r) (α i))) = u
  simp_rw [hv]
  simpa [Prod.snd_sum] using hh

namespace KernelContractScheme

variable {Signal : Type*} [MeasurableSpace Signal]
variable {prior : FiniteDist Ω} {r : Ω → A → ℝ} {c : A → ℝ}

def outcome (scheme : KernelContractScheme prior r c Signal) (s : Signal) : PosteriorPayoff Ω :=
  ((scheme.kernel.posterior prior s).prob,
    (scheme.response s).expect (payoff (meanReward (scheme.kernel.posterior prior s) r) (scheme.share s)))

omit [Nonempty A] [DecidableEq A] in
theorem ae_outcome_mem (scheme : KernelContractScheme prior r c Signal) :
    ∀ᵐ s ∂scheme.kernel.signalLaw prior, scheme.outcome s ∈ feasiblePayoffs r c := by
  filter_upwards [scheme.feasible, scheme.equilibrium] with s hα heq
  exact (mem_feasiblePayoffs_iff r c _).mpr
    ⟨scheme.kernel.posterior prior s, scheme.share s, scheme.response s, hα, heq, rfl, rfl⟩

omit [Nonempty A] [DecidableEq A] in
theorem outcome_integrable (scheme : KernelContractScheme prior r c Signal) :
    Integrable scheme.outcome (scheme.kernel.signalLaw prior) := by
  obtain ⟨M, hM⟩ := (feasiblePayoffs_compact r c).isBounded.exists_norm_le
  apply (integrable_const M).mono'
    ((scheme.kernel.posterior_measurable prior).aestronglyMeasurable.prodMk scheme.measurable_payoff)
  exact scheme.ae_outcome_mem.mono (fun _ h => hM _ h)

omit [Nonempty A] [DecidableEq A] in
theorem integral_outcome (scheme : KernelContractScheme prior r c Signal) :
    (∫ s, scheme.outcome s ∂scheme.kernel.signalLaw prior) = (prior.prob, scheme.utility) := by
  apply Prod.ext
  · ext ω
    rw [fst_integral scheme.outcome_integrable]
    have heval := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Ω => ℝ) ω).integral_comp_comm
      scheme.outcome_integrable.fst
    exact heval.symm.trans (scheme.kernel.posterior_plausible prior ω)
  · exact snd_integral scheme.outcome_integrable

omit [Nonempty A] [DecidableEq A] in
theorem mean_mem_convexHull (scheme : KernelContractScheme prior r c Signal) :
    (prior.prob, scheme.utility) ∈ convexHull ℝ (feasiblePayoffs r c) := by
  have h := (convex_convexHull ℝ (feasiblePayoffs r c)).integral_mem
    (compact_convexHull (feasiblePayoffs_compact r c)).isClosed
    (scheme.ae_outcome_mem.mono (fun _ h => subset_convexHull ℝ _ h)) scheme.outcome_integrable
  rwa [scheme.integral_outcome] at h

omit [Nonempty A] [DecidableEq A] in
/-- Exact finite replacement preserves prior and mixed-response utility. -/
theorem finite_equivalent (scheme : KernelContractScheme prior r c Signal) :
    ∃ finite : ContractScheme prior r c (Fin (supportBound Ω)), finite.utility = scheme.utility :=
  finite_scheme_of_mem_convexHull prior scheme.mean_mem_convexHull

end KernelContractScheme

/-- The finite-signal existence footnote also holds for the multi-action
extension, with the same conservative |Omega|+2 support bound. -/
theorem kernel_optimum_attained (prior : FiniteDist Ω) (r : Ω → A → ℝ) (c : A → ℝ) :
    ∃ optimal : KernelContractScheme prior r c (Fin (supportBound Ω)),
      ∀ (Signal : Type*) [MeasurableSpace Signal]
        (scheme : KernelContractScheme prior r c Signal), scheme.utility ≤ optimal.utility := by
  let C := convexHull ℝ (feasiblePayoffs r c) ∩ {z | z.1 = prior.prob}
  have hC : IsCompact C := (compact_convexHull (feasiblePayoffs_compact r c)).inter_right
    (isClosed_eq continuous_fst continuous_const)
  obtain ⟨i, hi⟩ := bestResponse_exists (meanReward prior r) c 0
  have hbase : (prior.prob, payoff (meanReward prior r) 0 i) ∈ feasiblePayoffs r c := by
    apply (mem_feasiblePayoffs_iff r c _).mpr
    exact ⟨prior, 0, FiniteDist.pointMass i, ⟨le_rfl, zero_le_one⟩,
      pointMass_bestResponse hi, rfl, FiniteDist.expect_pointMass _ _⟩
  have hne : C.Nonempty := ⟨(prior.prob, payoff (meanReward prior r) 0 i),
    subset_convexHull ℝ _ hbase, rfl⟩
  obtain ⟨z, hz, hmax⟩ := hC.exists_isMaxOn hne continuous_snd.continuousOn
  have hu : (prior.prob, z.2) ∈ convexHull ℝ (feasiblePayoffs r c) := by
    have heq : (prior.prob, z.2) = z := Prod.ext hz.2.symm rfl
    rw [heq]
    exact hz.1
  obtain ⟨finite, hfinite⟩ := finite_scheme_of_mem_convexHull prior hu
  refine ⟨finite.toKernelContract, ?_⟩
  intro Signal _ scheme
  rw [ContractScheme.toKernelContract_utility, hfinite]
  exact hmax (show (prior.prob, scheme.utility) ∈ C from ⟨scheme.mean_mem_convexHull, rfl⟩)

omit [Nonempty A] in
/-- At finitely many signals, replacing each mixed response by its best
supported pure action preserves information and weakly improves revenue. -/
theorem ContractScheme.purify {Signal : Type*} [Fintype Signal] {prior : FiniteDist Ω}
    {r : Ω → A → ℝ} {c : A → ℝ} (scheme : ContractScheme prior r c Signal) :
    ∃ pure : ContractScheme prior r c Signal,
      pure.information = scheme.information ∧ pure.share = scheme.share ∧
      (∀ s, ∃ i, pure.response s = FiniteDist.pointMass i) ∧ scheme.utility ≤ pure.utility := by
  choose i hi hdom using fun s => mixed_dominated (scheme.response s) (scheme.equilibrium s)
  let pure : ContractScheme prior r c Signal := {
    information := scheme.information
    share := scheme.share
    response s := FiniteDist.pointMass (i s)
    feasible := scheme.feasible
    equilibrium s := pointMass_bestResponse (hi s) }
  refine ⟨pure, rfl, rfl, fun s => ⟨i s, rfl⟩, ?_⟩
  apply scheme.information.weights.expect_mono
  intro s
  simpa only [pure, FiniteDist.expect_pointMass] using hdom s

/-- A jointly optimal kernel can use both finitely many signals and pure
responses, even when every competing scheme is allowed to mix. -/
theorem pure_kernel_optimum_attained (prior : FiniteDist Ω) (r : Ω → A → ℝ) (c : A → ℝ) :
    ∃ optimal : KernelContractScheme prior r c (Fin (supportBound Ω)),
      (∀ s, ∃ i, optimal.response s = FiniteDist.pointMass i) ∧
      ∀ (Signal : Type*) [MeasurableSpace Signal]
        (scheme : KernelContractScheme prior r c Signal), scheme.utility ≤ optimal.utility := by
  obtain ⟨optimal, hopt⟩ := kernel_optimum_attained prior r c
  obtain ⟨finite, hf⟩ := optimal.finite_equivalent
  obtain ⟨pure, _, _, hp, hdom⟩ := finite.purify
  refine ⟨pure.toKernelContract, hp, ?_⟩
  intro Signal _ scheme
  rw [ContractScheme.toKernelContract_utility]
  exact ((hopt Signal scheme).trans_eq hf.symm).trans hdom

end
end TransparencyLean.MultiAction
