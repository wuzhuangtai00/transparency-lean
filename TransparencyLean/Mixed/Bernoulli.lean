import TransparencyLean.Information.Contracts
import TransparencyLean.Model.Additive
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! Independent Bernoulli effort, represented by exact finite sums over teams. -/

namespace TransparencyLean.Mixed

open scoped BigOperators

noncomputable section

variable {Agent : Type*} [DecidableEq Agent]

def ValidProfile (x : Agent → ℝ) : Prop := ∀ i, 0 ≤ x i ∧ x i ≤ 1

def sampleWeight (x : Agent → ℝ) (A R : Finset Agent) : ℝ :=
  (∏ i ∈ R, x i) * ∏ i ∈ A \ R, (1 - x i)

/-- Each member of A is included independently with its own effort probability. -/
def sample (x : Agent → ℝ) (A : Finset Agent) (f : Finset Agent → ℝ) : ℝ :=
  ∑ R ∈ A.powerset, sampleWeight x A R * f R

@[simp] theorem sample_empty (x : Agent → ℝ) (f : Finset Agent → ℝ) :
    sample x ∅ f = f ∅ := by simp [sample, sampleWeight]

theorem sample_congr (x : Agent → ℝ) (A : Finset Agent) {f g : Finset Agent → ℝ}
    (h : ∀ R ⊆ A, f R = g R) : sample x A f = sample x A g := by
  apply Finset.sum_congr rfl
  intro R hR
  rw [h R (Finset.mem_powerset.mp hR)]

theorem sample_insert (x : Agent → ℝ) (A : Finset Agent) (i : Agent) (hi : i ∉ A)
    (f : Finset Agent → ℝ) :
    sample x (insert i A) f = (1 - x i) * sample x A f +
      x i * sample x A (fun R => f (insert i R)) := by
  unfold sample
  rw [Finset.sum_powerset_insert hi, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro R hR
    have hiR : i ∉ R := fun h => hi (Finset.mem_powerset.mp hR h)
    have hdiff : insert i A \ R = insert i (A \ R) := by
      ext j
      by_cases hj : j = i
      · subst j; simp [hiR]
      · simp [hj]
    have hiD : i ∉ A \ R := fun h => hi (Finset.mem_sdiff.mp h).1
    simp only [sampleWeight, hdiff, Finset.prod_insert hiD]
    ring
  · apply Finset.sum_congr rfl
    intro R hR
    have hiR : i ∉ R := fun h => hi (Finset.mem_powerset.mp hR h)
    have hdiff : insert i A \ insert i R = A \ R := by
      ext j
      by_cases hj : j = i
      · subst j; simp [hi]
      · simp [hj]
    simp only [sampleWeight, hdiff, Finset.prod_insert hiR]
    ring

@[simp] theorem sample_const (x : Agent → ℝ) (A : Finset Agent) (r : ℝ) :
    sample x A (fun _ => r) = r := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert i A hi ih => rw [sample_insert x A i hi, ih]; ring

theorem sample_add (x : Agent → ℝ) (A : Finset Agent) (f g : Finset Agent → ℝ) :
    sample x A (fun R => f R + g R) = sample x A f + sample x A g := by
  simp [sample, mul_add, Finset.sum_add_distrib]

theorem sample_sub (x : Agent → ℝ) (A : Finset Agent) (f g : Finset Agent → ℝ) :
    sample x A (fun R => f R - g R) = sample x A f - sample x A g := by
  simp [sample, mul_sub, Finset.sum_sub_distrib]

theorem sample_mul (x : Agent → ℝ) (A : Finset Agent) (r : ℝ) (f : Finset Agent → ℝ) :
    sample x A (fun R => r * f R) = r * sample x A f := by
  simp only [sample, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro R _
  ring

theorem sample_mono {x : Agent → ℝ} (hx : ValidProfile x) (A : Finset Agent)
    {f g : Finset Agent → ℝ} (h : ∀ R ⊆ A, f R ≤ g R) : sample x A f ≤ sample x A g := by
  apply Finset.sum_le_sum
  intro R hR
  apply mul_le_mul_of_nonneg_left (h R (Finset.mem_powerset.mp hR))
  exact mul_nonneg (Finset.prod_nonneg (fun i _ => (hx i).1))
    (Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (hx i).2))

theorem sample_bounds {x : Agent → ℝ} (hx : ValidProfile x) (A : Finset Agent)
    {f : Finset Agent → ℝ} (hf : ValidReward f) : 0 ≤ sample x A f ∧ sample x A f ≤ 1 := by
  constructor
  · simpa using sample_mono hx A (f := fun _ => 0) (fun R _ => (hf R).1)
  · simpa using sample_mono hx A (g := fun _ => 1) (fun R _ => (hf R).2)

theorem sample_profile_congr {x y : Agent → ℝ} (A : Finset Agent)
    (h : ∀ i ∈ A, x i = y i) (f : Finset Agent → ℝ) : sample x A f = sample y A f := by
  apply Finset.sum_congr rfl
  intro R hR
  unfold sampleWeight
  congr 2
  · exact Finset.prod_congr rfl (fun i hi => h i (Finset.mem_powerset.mp hR hi))
  · exact Finset.prod_congr rfl (fun i hi => congrArg (1 - ·) (h i (Finset.mem_sdiff.mp hi).1))

theorem sample_update_away (x : Agent → ℝ) (A : Finset Agent) {i : Agent}
    (hi : i ∉ A) (t : ℝ) (f : Finset Agent → ℝ) :
    sample (Function.update x i t) A f = sample x A f := by
  apply sample_profile_congr
  intro j hj
  exact Function.update_of_ne (ne_of_mem_of_not_mem hj hi) t x

@[simp] theorem sample_one (A : Finset Agent) (f : Finset Agent → ℝ) :
    sample (fun _ => 1) A f = f A := by
  induction A using Finset.induction_on generalizing f with
  | empty => simp
  | @insert i A hi ih => simp [sample_insert _ A i hi, ih]

theorem sample_additive (x w : Agent → ℝ) (A : Finset Agent) :
    sample x A (additiveReward w) = ∑ i ∈ A, x i * w i := by
  induction A using Finset.induction_on with
  | empty => simp [additiveReward]
  | @insert i A hi ih =>
    rw [sample_insert x A i hi, Finset.sum_insert hi]
    have heq : sample x A (fun R => additiveReward w (insert i R)) =
        sample x A (fun R => w i + additiveReward w R) := by
      apply sample_congr
      intro R hR
      exact Finset.sum_insert (fun h => hi (hR h))
    rw [heq, sample_add, sample_const, ih]
    ring

theorem sample_inter (x : Agent → ℝ) (A T : Finset Agent) (f : Finset Agent → ℝ) :
    sample x A (fun R => f (R ∩ T)) = sample x (A ∩ T) f := by
  induction A using Finset.induction_on generalizing f with
  | empty => simp
  | @insert i A hi ih =>
    rw [sample_insert x A i hi]
    by_cases hiT : i ∈ T
    · have heq : ∀ R : Finset Agent, insert i R ∩ T = insert i (R ∩ T) := by
        intro R; ext j
        by_cases hj : j = i
        · subst j; simp [hiT]
        · simp [hj]
      simp_rw [heq]
      rw [ih f, ih (fun R => f (insert i R)), sample_insert x (A ∩ T) i (by simp [hi])]
    · have heq : ∀ R : Finset Agent, insert i R ∩ T = R ∩ T := by
        intro R; ext j
        by_cases hj : j = i
        · subst j; simp [hiT]
        · simp [hj]
      simp_rw [heq, ih]
      ring

def mask (x : Agent → ℝ) (T : Finset Agent) (i : Agent) : ℝ := if i ∈ T then x i else 0

theorem mask_valid {x : Agent → ℝ} (hx : ValidProfile x) (T : Finset Agent) :
    ValidProfile (mask x T) := by
  intro i
  by_cases hi : i ∈ T <;> simp [mask, hi, hx i]

theorem sample_mask (x : Agent → ℝ) (A T : Finset Agent) (f : Finset Agent → ℝ) :
    sample (mask x T) A f = sample x (A ∩ T) f := by
  induction A using Finset.induction_on generalizing f with
  | empty => simp
  | @insert i A hi ih =>
    rw [sample_insert _ A i hi]
    by_cases hiT : i ∈ T
    · have heq : insert i A ∩ T = insert i (A ∩ T) := by
        ext j
        by_cases hj : j = i
        · subst j; simp [hiT]
        · simp [hj]
      rw [heq, sample_insert x (A ∩ T) i (by simp [hi])]
      simp [mask, hiT, ih]
    · have heq : insert i A ∩ T = A ∩ T := by
        ext j
        by_cases hj : j = i
        · subst j; simp [hiT]
        · simp [hj]
      simp [mask, hiT, heq, ih]

variable [Fintype Agent]

def extension (f : Finset Agent → ℝ) (x : Agent → ℝ) : ℝ := sample x Finset.univ f
def auxiliary (f : Finset Agent → ℝ) (x : Agent → ℝ) (T : Finset Agent) : ℝ := sample x T f
def marginal (f : Finset Agent → ℝ) (x : Agent → ℝ) (i : Agent) : ℝ :=
  sample x (Finset.univ.erase i) (fun R => f (insert i R) - f R)

@[simp] theorem extension_mask (f : Finset Agent → ℝ) (x : Agent → ℝ) (T : Finset Agent) :
    extension f (mask x T) = auxiliary f x T := by simp [extension, auxiliary, sample_mask]

theorem auxiliary_eq_inter (f : Finset Agent → ℝ) (x : Agent → ℝ) (T : Finset Agent) :
    auxiliary f x T = sample x Finset.univ (fun R => f (R ∩ T)) := by
  simp [auxiliary, sample_inter]

theorem marginal_mask (f : Finset Agent → ℝ) (x : Agent → ℝ) (T : Finset Agent)
    (i : Agent) :
    marginal f (mask x T) i = sample x (T.erase i) (fun R => f (insert i R) - f R) := by
  have heq : Finset.univ.erase i ∩ T = T.erase i := by ext j; simp [and_comm]
  simp [marginal, sample_mask, heq]

theorem auxiliary_marginal (f : Finset Agent → ℝ) (x : Agent → ℝ) (T : Finset Agent)
    {i : Agent} (hi : i ∈ T) :
    auxiliary f x T - auxiliary f x (T.erase i) = x i * marginal f (mask x T) i := by
  rw [marginal_mask, sample_sub]
  have h := sample_insert x (T.erase i) i (Finset.not_mem_erase i T) f
  rw [Finset.insert_erase hi] at h
  unfold auxiliary
  linarith

@[simp] theorem mask_univ (x : Agent → ℝ) : mask x Finset.univ = x := by ext i; simp [mask]

def pureProfile (T : Finset Agent) : Agent → ℝ := mask (fun _ => 1) T

omit [Fintype Agent] in
theorem pureProfile_valid (T : Finset Agent) : ValidProfile (pureProfile T) :=
  mask_valid (fun _ => by norm_num) T

@[simp] theorem extension_pure (f : Finset Agent → ℝ) (T : Finset Agent) :
    extension f (pureProfile T) = f T := by simp [pureProfile, auxiliary]

theorem marginal_pure (f : Finset Agent → ℝ) (T : Finset Agent) (i : Agent) :
    marginal f (pureProfile T) i = f (insert i (T.erase i)) - f (T.erase i) := by
  simp [pureProfile, marginal_mask]

theorem extension_deviation (f : Finset Agent → ℝ) (x : Agent → ℝ) (i : Agent) (t : ℝ) :
    extension f (Function.update x i t) - extension f x = (t - x i) * marginal f x i := by
  have h₁ := sample_insert x (Finset.univ.erase i) i (Finset.not_mem_erase _ _) f
  have h₂ := sample_insert (Function.update x i t) (Finset.univ.erase i) i
    (Finset.not_mem_erase _ _) f
  simp only [Finset.insert_erase (Finset.mem_univ i), Function.update_self,
    sample_update_away x _ (Finset.not_mem_erase _ _)] at h₁ h₂
  unfold extension marginal
  rw [h₁, h₂, sample_sub]
  ring

omit [Fintype Agent] in
theorem auxiliary_additive {f : Finset Agent → ℝ} (hf : IsAdditiveReward f)
    (x : Agent → ℝ) : IsAdditiveReward (auxiliary f x) := by
  obtain ⟨w, rfl⟩ := hf
  exact ⟨fun i => x i * w i, funext (sample_additive x w)⟩

omit [Fintype Agent] in
theorem auxiliary_valid {f : Finset Agent → ℝ} (hf : ValidReward f)
    {x : Agent → ℝ} (hx : ValidProfile x) : ValidReward (auxiliary f x) :=
  fun T => sample_bounds hx T hf

theorem auxiliary_monotone {f : Finset Agent → ℝ} (hf : Monotone f)
    {x : Agent → ℝ} (hx : ValidProfile x) : Monotone (auxiliary f x) := by
  intro S T hST
  rw [auxiliary_eq_inter, auxiliary_eq_inter]
  apply sample_mono hx
  intro R _
  exact hf (Finset.inter_subset_inter (Finset.Subset.refl R) hST)

theorem auxiliary_submodular {f : Finset Agent → ℝ} (hf : Submodular f)
    {x : Agent → ℝ} (hx : ValidProfile x) : Submodular (auxiliary f x) := by
  intro S T
  rw [auxiliary_eq_inter f x (S ∪ T), auxiliary_eq_inter f x (S ∩ T),
    auxiliary_eq_inter f x S, auxiliary_eq_inter f x T, ← sample_add, ← sample_add]
  apply sample_mono hx
  intro R _
  rw [Finset.inter_union_distrib_left, Finset.inter_inter_distrib_left]
  exact hf (R ∩ S) (R ∩ T)

theorem auxiliary_supermodular {f : Finset Agent → ℝ} (hf : Supermodular f)
    {x : Agent → ℝ} (hx : ValidProfile x) : Supermodular (auxiliary f x) := by
  intro S T
  rw [auxiliary_eq_inter f x (S ∪ T), auxiliary_eq_inter f x (S ∩ T),
    auxiliary_eq_inter f x S, auxiliary_eq_inter f x T, ← sample_add, ← sample_add]
  apply sample_mono hx
  intro R _
  rw [Finset.inter_union_distrib_left, Finset.inter_inter_distrib_left]
  exact hf (R ∩ S) (R ∩ T)

end

end TransparencyLean.Mixed
