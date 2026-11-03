import TransparencyLean.Submodular.TightnessInstance
import TransparencyLean.Information.KernelRealization

/-! Paper Proposition 4.3: the exact additive family, convergence of its ratio,
and failure of every approximation factor strictly smaller than 4/3. -/

namespace TransparencyLean.Tightness

open scoped Topology
open Filter

noncomputable section

/-- The exact finite-n ratio displayed in Proposition 4.3. -/
theorem ratio_exact (n : ℕ) (hn : 2 ≤ n) (heven : Even n) :
    noDisclosureValue (prior n hn) (reward n) (costs n) /
      fullDisclosureValue (prior n hn) (reward n) (costs n) =
      4 * (3 * (n : ℝ) ^ 3 + n - 1) / (3 * (n : ℝ) ^ 2 * (3 * n + 2)) := by
  rw [no_disclosure_value n hn, full_disclosure_value n hn heven]
  exact ratio_identity (by exact_mod_cast hn)

/-- Quantitative convergence, proved before any claim of asymptotic sharpness. -/
theorem ratio_tendsto : Tendsto (fun n : ℕ => ratio n) atTop (𝓝 (4 / 3)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
  refine ⟨k + 2, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := by omega
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hkn : (k : ℝ) < n := by exact_mod_cast (show k < n by omega)
  have hscale : 1 < (n : ℝ) * ε := (div_lt_iff₀ hε).mp (hk.trans hkn)
  have hinv : 1 / (n : ℝ) < ε := (div_lt_iff₀ (by linarith : (0 : ℝ) < n)).mpr (by linarith)
  obtain ⟨hlower, hupper⟩ := ratio_gap_bounds hnr
  rw [Real.dist_eq, abs_of_nonpos (by linarith : ratio n - 4 / 3 ≤ 0)]
  linarith

def evenSize (m : ℕ) : ℕ := 2 * (m + 1)

theorem evenSize_two_le (m : ℕ) : 2 ≤ evenSize m := by unfold evenSize; omega
theorem evenSize_even (m : ℕ) : Even (evenSize m) := ⟨m + 1, by unfold evenSize; omega⟩

def familyRatio (m : ℕ) : ℝ :=
  noDisclosureValue (prior (evenSize m) (evenSize_two_le m)) (reward (evenSize m)) (costs (evenSize m)) /
    fullDisclosureValue (prior (evenSize m) (evenSize_two_le m)) (reward (evenSize m)) (costs (evenSize m))

theorem familyRatio_eq (m : ℕ) : familyRatio m = ratio (evenSize m) :=
  ratio_exact (evenSize m) (evenSize_two_le m) (evenSize_even m)

/-- Convergence of the actual utility ratio along the even-sized family. -/
theorem family_ratio_tendsto : Tendsto familyRatio atTop (𝓝 (4 / 3)) := by
  have heq : familyRatio = fun m => ratio (evenSize m) := funext familyRatio_eq
  rw [heq]
  exact ratio_tendsto.comp (tendsto_atTop_mono (fun m =>
    show m ≤ evenSize m by unfold evenSize; omega) tendsto_id)

theorem exists_even_ratio_gt (β : ℝ) (hβ : β < 4 / 3) :
    ∃ n : ℕ, 2 ≤ n ∧ Even n ∧ β < ratio n := by
  let ε := 4 / 3 - β
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
  let n := 2 * (k + 1)
  have hn : 2 ≤ n := by dsimp [n]; omega
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hkn : (k : ℝ) < n := by exact_mod_cast (show k < n by dsimp [n]; omega)
  have hscale : 1 < (n : ℝ) * ε := (div_lt_iff₀ hε).mp (hk.trans hkn)
  have hinv : 1 / (n : ℝ) < ε := (div_lt_iff₀ (by linarith : (0 : ℝ) < n)).mpr (by linarith)
  have hgap := (ratio_gap_bounds hnr).2
  refine ⟨n, hn, ⟨k + 1, by dsimp [n]; omega⟩, ?_⟩
  dsimp [ε] at hinv
  linarith

/-- No disclosure is realized by an actual one-signal public kernel. -/
theorem opaque_scheme (n : ℕ) (hn : 2 ≤ n) :
    ∃ hidden : KernelContractScheme (prior n hn) (reward n) (costs n) Unit,
      hidden.kernel = (PosteriorScheme.uninformative (prior n hn)).toSignalKernel ∧
      hidden.utility = noValue n := by
  obtain ⟨finite, hinfo, hvalue⟩ := noDisclosure_attained (prior n hn) (reward n) (costs n)
    (reward_valid n hn) (reward_monotone n hn) (fun i => le_of_lt (costs_pos n hn i))
  refine ⟨finite.toKernelContract, ?_, ?_⟩
  · change finite.information.toSignalKernel = _
    rw [hinfo]
  · rw [ContractScheme.toKernelContract_utility, hvalue, no_disclosure_value n hn]

/-- The unrestricted joint optimum attains at least the displayed finite-n
ratio. This uses the checked existence theorem, not an assumed optimizer. -/
theorem optimal_ratio_lower_bound (n : ℕ) (hn : 2 ≤ n) (heven : Even n) :
    ∃ optimal : KernelContractScheme (prior n hn) (reward n) (costs n)
        (Fin (supportBound (Fin n))),
      (∀ (Signal : Type*) [MeasurableSpace Signal]
        (scheme : KernelContractScheme (prior n hn) (reward n) (costs n) Signal),
          scheme.utility ≤ optimal.utility) ∧
      ratio n ≤ optimal.utility / fullDisclosureValue (prior n hn) (reward n) (costs n) := by
  obtain ⟨optimal, hopt⟩ := finite_optimal_scheme (prior n hn) (reward n) (costs n)
    (fun i => le_of_lt (costs_pos n hn i))
  refine ⟨optimal.toKernelContract, ?_, ?_⟩
  · intro Signal _ scheme
    obtain ⟨finite, hfinite⟩ := scheme.finite_equivalent
    rw [ContractScheme.toKernelContract_utility, ← hfinite]
    exact hopt _ finite
  · obtain ⟨hidden, _, hhidden⟩ := noDisclosure_attained (prior n hn) (reward n) (costs n)
      (reward_valid n hn) (reward_monotone n hn) (fun i => le_of_lt (costs_pos n hn i))
    have h := hopt Unit hidden
    rw [hhidden, no_disclosure_value n hn] at h
    rw [ContractScheme.toKernelContract_utility, full_disclosure_value n hn heven,
      ← ratio_identity (by exact_mod_cast hn)]
    exact div_le_div_of_nonneg_right h (le_of_lt (fullValue_pos (by exact_mod_cast hn)))

/-- Sharpness of 4/3, even for additive rewards, witnessed by a no-disclosure
kernel. Every smaller factor fails on one finite member of the paper's family. -/
theorem no_better_factor (β : ℝ) (hβ : β < 4 / 3) :
    ∃ (n : ℕ) (hn : 2 ≤ n), Even n ∧
      (∀ ω : Fin n, IsAdditiveReward (reward n ω) ∧ ValidReward (reward n ω) ∧
        Monotone (reward n ω)) ∧
      (∀ i : Fin n, 0 ≤ costs n i) ∧
      ∃ hidden : KernelContractScheme (prior n hn) (reward n) (costs n) Unit,
        hidden.kernel = (PosteriorScheme.uninformative (prior n hn)).toSignalKernel ∧
        0 < fullDisclosureValue (prior n hn) (reward n) (costs n) ∧
        β * fullDisclosureValue (prior n hn) (reward n) (costs n) < hidden.utility := by
  obtain ⟨n, hn, heven, hratio⟩ := exists_even_ratio_gt β hβ
  obtain ⟨hidden, hkernel, hvalue⟩ := opaque_scheme n hn
  refine ⟨n, hn, heven,
    fun ω => ⟨reward_additive n ω, reward_valid n hn ω, reward_monotone n hn ω⟩,
    fun i => le_of_lt (costs_pos n hn i), hidden, hkernel, ?_, ?_⟩
  · rw [full_disclosure_value n hn heven]
    exact fullValue_pos (by exact_mod_cast hn)
  · rw [full_disclosure_value n hn heven, hvalue]
    rw [← ratio_identity (by exact_mod_cast hn)] at hratio
    exact (lt_div_iff₀ (fullValue_pos (by exact_mod_cast hn))).mp hratio

end

end TransparencyLean.Tightness
