import TransparencyLean.Information.AllOrNothing

/-!
# Finite signals and Bayes-plausible posterior schemes

Both directions of the finite representation theorem, with zero-probability
states and signals allowed. Finite-support attainment for arbitrary measurable
signal spaces is proved separately in `KernelRealization.lean`.
-/

namespace TransparencyLean

open scoped BigOperators

noncomputable section

variable {Ω Signal : Type*} [Fintype Ω] [Fintype Signal]

abbrev FiniteKernel (Ω Signal : Type*) [Fintype Signal] := Ω → FiniteDist Signal

namespace FiniteKernel

variable (prior : FiniteDist Ω) (kernel : FiniteKernel Ω Signal)

def signalMass (s : Signal) : ℝ := prior.expect (fun ω => (kernel ω).prob s)

theorem signalMass_nonneg (s : Signal) : 0 ≤ signalMass prior kernel s :=
  prior.expect_nonneg (fun ω => (kernel ω).nonneg s)

theorem signalMass_sum : ∑ s, signalMass prior kernel s = 1 := by
  unfold signalMass FiniteDist.expect
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, FiniteDist.sum_eq_one, mul_one]
  exact prior.sum_eq_one

def signalDistribution : FiniteDist Signal where
  prob := signalMass prior kernel
  nonneg := signalMass_nonneg prior kernel
  sum_eq_one := signalMass_sum prior kernel

def posterior (s : Signal) : FiniteDist Ω :=
  if h : signalMass prior kernel s = 0 then prior
  else {
    prob := fun ω => prior.prob ω * (kernel ω).prob s / signalMass prior kernel s
    nonneg := fun ω => div_nonneg (mul_nonneg (prior.nonneg ω) ((kernel ω).nonneg s))
      (signalMass_nonneg prior kernel s)
    sum_eq_one := by
      rw [← Finset.sum_div]
      exact div_self h
  }

theorem joint_eq (ω : Ω) (s : Signal) :
    signalMass prior kernel s * (posterior prior kernel s).prob ω =
      prior.prob ω * (kernel ω).prob s := by
  classical
  by_cases h : signalMass prior kernel s = 0
  · have hle : prior.prob ω * (kernel ω).prob s ≤ signalMass prior kernel s := by
      exact Finset.single_le_sum
        (fun η _ => mul_nonneg (prior.nonneg η) ((kernel η).nonneg s)) (Finset.mem_univ ω)
    have hz : prior.prob ω * (kernel ω).prob s = 0 := by
      have hn := mul_nonneg (prior.nonneg ω) ((kernel ω).nonneg s)
      linarith
    simp [h, hz]
  · simp only [posterior, h, dif_neg, FiniteDist.prob]
    field_simp

def toPosteriorScheme : PosteriorScheme prior Signal where
  weights := signalDistribution prior kernel
  posterior := posterior prior kernel
  plausible ω := by
    change (∑ s, signalMass prior kernel s * (posterior prior kernel s).prob ω) = prior.prob ω
    simp_rw [joint_eq, ← Finset.mul_sum, FiniteDist.sum_eq_one, mul_one]

end FiniteKernel

namespace PosteriorScheme

variable {prior : FiniteDist Ω} (scheme : PosteriorScheme prior Signal)

/-- Implements a Bayes-plausible finite scheme as an actual randomized signal
kernel. On a zero-prior state the kernel uses the unconditional signal law. -/
def toKernel (ω : Ω) : FiniteDist Signal :=
  if h : prior.prob ω = 0 then scheme.weights
  else {
    prob := fun s => scheme.weights.prob s * (scheme.posterior s).prob ω / prior.prob ω
    nonneg := fun s => div_nonneg
      (mul_nonneg (scheme.weights.nonneg s) ((scheme.posterior s).nonneg ω)) (prior.nonneg ω)
    sum_eq_one := by
      rw [← Finset.sum_div]
      change scheme.weights.expect (fun s => (scheme.posterior s).prob ω) / prior.prob ω = 1
      rw [scheme.plausible, div_self h]
  }

theorem kernel_joint_eq (ω : Ω) (s : Signal) :
    prior.prob ω * (scheme.toKernel ω).prob s =
      scheme.weights.prob s * (scheme.posterior s).prob ω := by
  classical
  by_cases h : prior.prob ω = 0
  · have hle : scheme.weights.prob s * (scheme.posterior s).prob ω ≤ prior.prob ω := by
      rw [← scheme.plausible ω]
      exact Finset.single_le_sum
        (fun t _ => mul_nonneg (scheme.weights.nonneg t) ((scheme.posterior t).nonneg ω))
        (Finset.mem_univ s)
    have hz : scheme.weights.prob s * (scheme.posterior s).prob ω = 0 := by
      have hn := mul_nonneg (scheme.weights.nonneg s) ((scheme.posterior s).nonneg ω)
      linarith
    simp [h, hz]
  · simp only [toKernel, h, dif_neg, FiniteDist.prob]
    field_simp

theorem kernel_signalMass (s : Signal) :
    FiniteKernel.signalMass prior scheme.toKernel s = scheme.weights.prob s := by
  change (∑ ω, prior.prob ω * (scheme.toKernel ω).prob s) = scheme.weights.prob s
  simp_rw [scheme.kernel_joint_eq, ← Finset.mul_sum, FiniteDist.sum_eq_one, mul_one]

/-- Bayes' formula recovers the specified posterior on every positive-mass
signal; the law on a null signal has no effect on any expected payoff. -/
theorem kernel_bayes (s : Signal) (hs : scheme.weights.prob s ≠ 0) (ω : Ω) :
    prior.prob ω * (scheme.toKernel ω).prob s /
      FiniteKernel.signalMass prior scheme.toKernel s = (scheme.posterior s).prob ω := by
  rw [scheme.kernel_joint_eq, scheme.kernel_signalMass]
  field_simp

end PosteriorScheme

end

end TransparencyLean
