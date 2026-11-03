import TransparencyLean.Mixed.Rounding
import TransparencyLean.Mixed.KernelSignals
import TransparencyLean.Submodular.Tightness
import TransparencyLean.Supermodular.Counterexample

/-! Sharpness of the mixed 4/3 bound, and unbounded loss for supermodular rewards. -/

namespace TransparencyLean.Mixed

open scoped Topology
open Filter

noncomputable section

theorem tightness_noDisclosure_eq (n : ℕ) (hn : 2 ≤ n) :
    noDisclosureValue (Tightness.prior n hn) (Tightness.reward n) (Tightness.costs n) =
      TransparencyLean.noDisclosureValue (Tightness.prior n hn) (Tightness.reward n) (Tightness.costs n) := by
  apply additive_value_eq_pure (posteriorReward_valid _ (Tightness.reward_valid n hn))
    _ (fun i => le_of_lt (Tightness.costs_pos n hn i))
  rw [Tightness.mean_reward]
  exact ⟨_, rfl⟩

theorem tightness_fullDisclosure_eq (n : ℕ) (hn : 2 ≤ n) :
    fullDisclosureValue (Tightness.prior n hn) (Tightness.reward n) (Tightness.costs n) =
      TransparencyLean.fullDisclosureValue (Tightness.prior n hn) (Tightness.reward n) (Tightness.costs n) :=
  additive_fullDisclosure_eq_pure _ (Tightness.reward_valid n hn) (Tightness.reward_additive n)
    (fun i => le_of_lt (Tightness.costs_pos n hn i))

theorem tightness_ratio_exact (n : ℕ) (hn : 2 ≤ n) (heven : Even n) :
    noDisclosureValue (Tightness.prior n hn) (Tightness.reward n) (Tightness.costs n) /
      fullDisclosureValue (Tightness.prior n hn) (Tightness.reward n) (Tightness.costs n) =
        4 * (3 * (n : ℝ) ^ 3 + n - 1) / (3 * (n : ℝ) ^ 2 * (3 * n + 2)) := by
  rw [tightness_noDisclosure_eq, tightness_fullDisclosure_eq]
  exact Tightness.ratio_exact n hn heven

def familyRatio (m : ℕ) : ℝ :=
  noDisclosureValue (Tightness.prior (Tightness.evenSize m) (Tightness.evenSize_two_le m))
      (Tightness.reward (Tightness.evenSize m)) (Tightness.costs (Tightness.evenSize m)) /
    fullDisclosureValue (Tightness.prior (Tightness.evenSize m) (Tightness.evenSize_two_le m))
      (Tightness.reward (Tightness.evenSize m)) (Tightness.costs (Tightness.evenSize m))

theorem family_ratio_tendsto : Tendsto familyRatio atTop (𝓝 (4 / 3)) := by
  have heq : familyRatio = Tightness.familyRatio := by
    funext m
    unfold familyRatio Tightness.familyRatio
    rw [tightness_noDisclosure_eq, tightness_fullDisclosure_eq]
  rw [heq]
  exact Tightness.family_ratio_tendsto

/-- No factor smaller than 4/3 can compare all mixed schemes to mixed full disclosure. -/
theorem no_better_factor (β : ℝ) (hβ : β < 4 / 3) :
    ∃ (n : ℕ) (hn : 2 ≤ n), Even n ∧
      (∀ ω : Fin n, IsAdditiveReward (Tightness.reward n ω) ∧ ValidReward (Tightness.reward n ω) ∧
        Monotone (Tightness.reward n ω)) ∧
      (∀ i : Fin n, 0 ≤ Tightness.costs n i) ∧
      ∃ hidden : KernelContractScheme (Tightness.prior n hn) (Tightness.reward n) (Tightness.costs n) Unit,
        hidden.kernel = (PosteriorScheme.uninformative (Tightness.prior n hn)).toSignalKernel ∧
        0 < fullDisclosureValue (Tightness.prior n hn) (Tightness.reward n) (Tightness.costs n) ∧
        β * fullDisclosureValue (Tightness.prior n hn) (Tightness.reward n) (Tightness.costs n) < hidden.utility := by
  obtain ⟨n, hn, heven, hf, hc, hidden, hkernel, hpos, hstrict⟩ := Tightness.no_better_factor β hβ
  refine ⟨n, hn, heven, hf, hc, KernelContractScheme.ofPure hidden, hkernel, ?_, ?_⟩
  · rwa [tightness_fullDisclosure_eq]
  · rwa [tightness_fullDisclosure_eq, KernelContractScheme.ofPure_utility]

/-- The paper's normalized complementary-tasks example remains a separation
when both information benchmarks optimize over mixed equilibria. -/
theorem supermodular_separation :
    fullDisclosureValue SupermodularExample.prior SupermodularExample.reward SupermodularExample.cost = 0 ∧
    0 < noDisclosureValue SupermodularExample.prior SupermodularExample.reward SupermodularExample.cost := by
  rw [supermodular_fullDisclosure_eq_pure _ SupermodularExample.reward_valid
    SupermodularExample.reward_monotone SupermodularExample.reward_supermodular SupermodularExample.cost_nonneg,
    supermodular_noDisclosure_eq_pure _ SupermodularExample.reward_valid
    SupermodularExample.reward_monotone SupermodularExample.reward_supermodular SupermodularExample.cost_nonneg]
  exact ⟨SupermodularExample.fullDisclosure_zero, SupermodularExample.noDisclosure_positive⟩

theorem supermodular_no_finite_factor (β : ℝ) :
    ¬ noDisclosureValue SupermodularExample.prior SupermodularExample.reward SupermodularExample.cost ≤
      β * fullDisclosureValue SupermodularExample.prior SupermodularExample.reward SupermodularExample.cost := by
  rw [supermodular_separation.1, mul_zero]
  exact not_le.mpr supermodular_separation.2

end

end TransparencyLean.Mixed
