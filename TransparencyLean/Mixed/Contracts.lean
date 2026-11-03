import TransparencyLean.Mixed.Bernoulli

/-! Mixed best responses, pure embedding, and stateless mixed benchmarks. -/

namespace TransparencyLean.Mixed

open scoped BigOperators

noncomputable section

variable {Agent : Type*} [Fintype Agent] [DecidableEq Agent]

def IsMixedEquilibrium (f : Finset Agent → ℝ) (c α x : Agent → ℝ) : Prop :=
  (∀ i, 0 < x i → c i ≤ α i * marginal f x i) ∧
  (∀ i, x i < 1 → α i * marginal f x i ≤ c i)

def utility (f : Finset Agent → ℝ) (α x : Agent → ℝ) : ℝ :=
  (1 - ∑ i, α i) * extension f x

def expectedAgentUtility (f : Finset Agent → ℝ) (c α x : Agent → ℝ) (i : Agent) : ℝ :=
  α i * extension f x - x i * c i

theorem agentUtility_deviation (f : Finset Agent → ℝ) (c α x : Agent → ℝ) (i : Agent) (t : ℝ) :
    expectedAgentUtility f c α (Function.update x i t) i - expectedAgentUtility f c α x i =
      (t - x i) * (α i * marginal f x i - c i) := by
  have h := extension_deviation f x i t
  simp only [expectedAgentUtility, Function.update_self]
  linear_combination α i * h

/-- The support inequalities are equivalent to all unilateral mixed deviations. -/
theorem isMixedEquilibrium_iff_bestResponse (f : Finset Agent → ℝ) (c α : Agent → ℝ)
    {x : Agent → ℝ} (hx : ValidProfile x) :
    IsMixedEquilibrium f c α x ↔ ∀ i t, 0 ≤ t → t ≤ 1 →
      expectedAgentUtility f c α (Function.update x i t) i ≤ expectedAgentUtility f c α x i := by
  constructor
  · rintro ⟨hwork, hshirk⟩ i t ht0 ht1
    have h₀ : 0 ≤ x i * (α i * marginal f x i - c i) := by
      by_cases h : 0 < x i
      · exact mul_nonneg (hx i).1 (sub_nonneg.mpr (hwork i h))
      · have hz : x i = 0 := le_antisymm (le_of_not_gt h) (hx i).1
        simp [hz]
    have h₁ : (1 - x i) * (α i * marginal f x i - c i) ≤ 0 := by
      by_cases h : x i < 1
      · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hx i).2)
          (sub_nonpos.mpr (hshirk i h))
      · have hz : x i = 1 := le_antisymm (hx i).2 (le_of_not_gt h)
        simp [hz]
    have ha := mul_nonneg (sub_nonneg.mpr ht1) h₀
    have hb := mul_nonpos_of_nonneg_of_nonpos ht0 h₁
    have hd := agentUtility_deviation f c α x i t
    nlinarith
  · intro h
    constructor
    · intro i hi
      have h₀ := h i 0 (by norm_num) (by norm_num)
      have hd := agentUtility_deviation f c α x i 0
      nlinarith
    · intro i hi
      have h₁ := h i 1 (by norm_num) (by norm_num)
      have hd := agentUtility_deviation f c α x i 1
      nlinarith

theorem pure_equilibrium_iff (f : Finset Agent → ℝ) (c α : Agent → ℝ) (T : Finset Agent) :
    IsMixedEquilibrium f c α (pureProfile T) ↔ IsEquilibrium f c α T := by
  simp only [IsMixedEquilibrium, IsEquilibrium, pureProfile, mask, marginal_mask, sample_one]
  constructor
  · rintro ⟨hwork, hshirk⟩
    constructor
    · intro i hi
      simpa [hi, Finset.insert_erase hi] using hwork i (by simp [hi])
    · intro i hi
      simpa [Finset.erase_eq_of_not_mem hi] using hshirk i (by simp [hi])
  · rintro ⟨hwork, hshirk⟩
    constructor
    · intro i hi
      have hiT : i ∈ T := by by_contra h; simp [h] at hi
      simpa [Finset.insert_erase hiT] using hwork i hiT
    · intro i hi
      have hiT : i ∉ T := by intro h; simp [h] at hi
      simpa [Finset.erase_eq_of_not_mem hiT] using hshirk i hiT

@[simp] theorem utility_pure (f : Finset Agent → ℝ) (α : Agent → ℝ) (T : Finset Agent) :
    utility f α (pureProfile T) = principalUtility f α T := by
  simp [utility, principalUtility]

theorem utility_le_one {f : Finset Agent → ℝ} (hf : ValidReward f)
    {α x : Agent → ℝ} (hα : FeasibleContract α) (hx : ValidProfile x) : utility f α x ≤ 1 := by
  have hs : 0 ≤ ∑ i, α i := Finset.sum_nonneg (fun i _ => (hα i).1)
  have hb := sample_bounds hx Finset.univ hf
  unfold utility extension
  nlinarith

def achievableUtilities (f : Finset Agent → ℝ) (c : Agent → ℝ) : Set ℝ :=
  {u | ∃ α x, FeasibleContract α ∧ ValidProfile x ∧ IsMixedEquilibrium f c α x ∧ utility f α x = u}

def statelessValue (f : Finset Agent → ℝ) (c : Agent → ℝ) : ℝ := sSup (achievableUtilities f c)

theorem achievable_nonempty (f : Finset Agent → ℝ) (c : Agent → ℝ)
    (hc : ∀ i, 0 ≤ c i) : (achievableUtilities f c).Nonempty := by
  refine ⟨f ∅, fun _ => 0, pureProfile ∅, zero_feasible, pureProfile_valid ∅, ?_, ?_⟩
  · exact (pure_equilibrium_iff f c _ ∅).mpr (empty_zero_equilibrium f c hc)
  · simp

theorem achievable_bddAbove {f : Finset Agent → ℝ} (hf : ValidReward f) (c : Agent → ℝ) :
    BddAbove (achievableUtilities f c) := by
  refine ⟨1, ?_⟩
  rintro u ⟨α, x, hα, hx, _, rfl⟩
  exact utility_le_one hf hα hx

theorem utility_le_statelessValue {f : Finset Agent → ℝ} (hf : ValidReward f)
    {c α x : Agent → ℝ} (hα : FeasibleContract α) (hx : ValidProfile x)
    (heq : IsMixedEquilibrium f c α x) : utility f α x ≤ statelessValue f c :=
  le_csSup (achievable_bddAbove hf c) ⟨α, x, hα, hx, heq, rfl⟩

theorem statelessValue_le {f : Finset Agent → ℝ} {c : Agent → ℝ} (hc : ∀ i, 0 ≤ c i)
    {v : ℝ} (h : ∀ α x, FeasibleContract α → ValidProfile x → IsMixedEquilibrium f c α x →
      utility f α x ≤ v) : statelessValue f c ≤ v := by
  apply csSup_le (achievable_nonempty f c hc)
  rintro u ⟨α, x, hα, hx, heq, rfl⟩
  exact h α x hα hx heq

theorem pure_le_mixed {f : Finset Agent → ℝ} (hf : ValidReward f)
    {c : Agent → ℝ} (hc : ∀ i, 0 ≤ c i) : TransparencyLean.statelessValue f c ≤ statelessValue f c := by
  apply TransparencyLean.statelessValue_le hc
  intro α T hα hT
  have h := utility_le_statelessValue hf hα (pureProfile_valid T) ((pure_equilibrium_iff f c α T).mpr hT)
  simpa using h

theorem statelessValue_nonneg {f : Finset Agent → ℝ} (hf : ValidReward f)
    {c : Agent → ℝ} (hc : ∀ i, 0 ≤ c i) : 0 ≤ statelessValue f c :=
  (TransparencyLean.statelessValue_nonneg hf hc).trans (pure_le_mixed hf hc)

theorem statelessValue_le_one {f : Finset Agent → ℝ} (hf : ValidReward f)
    {c : Agent → ℝ} (hc : ∀ i, 0 ≤ c i) : statelessValue f c ≤ 1 :=
  statelessValue_le hc (fun _ _ hα hx _ => utility_le_one hf hα hx)

end

end TransparencyLean.Mixed
