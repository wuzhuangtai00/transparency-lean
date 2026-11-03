import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic

/-! Finite-dimensional compact convex hulls, with an explicit finite mixture.
This supplies the compactness step needed for joint-scheme attainment. -/

namespace TransparencyLean

open scoped BigOperators
open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem convexHull_fixed_mixture {K : Set E} {x : E} (hx : x ∈ convexHull ℝ K) :
    ∃ (w : Fin (Module.finrank ℝ E + 1) → ℝ)
      (z : Fin (Module.finrank ℝ E + 1) → E),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ (∀ i, z i ∈ K) ∧
      ∑ i, w i • z i = x := by
  classical
  obtain ⟨ι, inst, z, w, hz, hind, hw, hsum, hxsum⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx
  letI := inst
  have hcard : Fintype.card ι ≤ Module.finrank ℝ E + 1 :=
    hind.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  let e : ι ↪ Fin (Module.finrank ℝ E + 1) :=
    (Fintype.equivFin ι).toEmbedding.trans (Fin.castLEEmb hcard)
  have hne : Nonempty ι := by
    cases isEmpty_or_nonempty ι with
    | inl h => haveI := h; simp at hsum
    | inr h => exact h
  let i₀ : ι := Classical.choice hne
  let w' := Function.extend e w (fun _ => 0)
  let z' := Function.extend e z (fun _ => z i₀)
  have hw' : ∀ i, 0 ≤ w' i := by
    intro i
    by_cases hi : ∃ j, e j = i
    · obtain ⟨j, rfl⟩ := hi
      simpa [w', e.injective.extend_apply] using le_of_lt (hw j)
    · simp [w', Function.extend_apply' _ _ _ hi]
  have hws : ∑ i, w' i = ∑ i, w i := by
    symm
    apply Fintype.sum_of_injective e e.injective
    · intro i hi
      exact Function.extend_apply' _ _ _ hi
    · intro i
      simp [w', e.injective.extend_apply]
  have hzs : ∑ i, w' i • z' i = ∑ i, w i • z i := by
    symm
    apply Fintype.sum_of_injective e e.injective
    · intro i hi
      simp [w', Function.extend_apply' _ _ _ hi]
    · intro i
      simp [w', z', e.injective.extend_apply]
  refine ⟨w', z', hw', hws.trans hsum, ?_, hzs.trans hxsum⟩
  intro i
  by_cases hi : ∃ j, e j = i
  · obtain ⟨j, rfl⟩ := hi
    simpa [z', e.injective.extend_apply] using hz (mem_range_self j)
  · simpa [z', Function.extend_apply' _ _ _ hi] using hz (mem_range_self i₀)

/-- A compact subset of a finite-dimensional real space has compact convex
hull. The proof pads Carathéodory mixtures to a fixed finite length. -/
theorem compact_convexHull {K : Set E} (hK : IsCompact K) : IsCompact (convexHull ℝ K) := by
  classical
  let I := Fin (Module.finrank ℝ E + 1)
  let W : Set (I → ℝ) := Icc (fun _ => 0) (fun _ => 1) ∩ {w | ∑ i, w i = 1}
  let Z : Set (I → E) := {z | ∀ i, z i ∈ K}
  have hW : IsCompact W := isCompact_Icc.inter_right (isClosed_eq (by fun_prop) continuous_const)
  have hZ : IsCompact Z := isCompact_pi_infinite (fun _ => hK)
  let mix : (I → ℝ) × (I → E) → E := fun a => ∑ i, a.1 i • a.2 i
  have hmix : Continuous mix := by fun_prop
  have heq : convexHull ℝ K = mix '' (W ×ˢ Z) := by
    ext x
    constructor
    · intro hx
      obtain ⟨w, z, hw, hsum, hz, hx⟩ := convexHull_fixed_mixture hx
      refine ⟨(w, z), ⟨⟨⟨hw, ?_⟩, hsum⟩, ?_⟩, hx⟩
      · intro i
        exact (Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ i)).trans_eq hsum
      · exact hz
    · rintro ⟨⟨w, z⟩, ⟨⟨⟨hw, _⟩, hsum⟩, hz⟩, rfl⟩
      exact mem_convexHull_of_exists_fintype w z hw hsum hz rfl
  rw [heq]
  exact (hW.prod hZ).image hmix

end

end TransparencyLean
