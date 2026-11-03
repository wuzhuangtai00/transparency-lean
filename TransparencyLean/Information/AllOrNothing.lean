import TransparencyLean.Model.FiniteProbability

/-!
# Bayes plausibility and the finite-signal All-or-Nothing lemma

Paper: `lem:approximation_extension` (Lemma 3.1).
The theorem here quantifies over finite posterior schemes. The extensions to
arbitrary measurable signals and finite attainment are proved in
`MeasurableSignals.lean`, `KernelContracts.lean`, and `KernelRealization.lean`.
-/

namespace TransparencyLean

open scoped BigOperators

structure PosteriorScheme {Ω : Type*} [Fintype Ω]
    (prior : FiniteDist Ω) (Signal : Type*) [Fintype Signal] where
  weights : FiniteDist Signal
  posterior : Signal → FiniteDist Ω
  plausible : ∀ ω, weights.expect (fun s => (posterior s).prob ω) = prior.prob ω

namespace PosteriorScheme

variable {Ω Signal : Type*} [Fintype Ω] [Fintype Signal]

def uninformative (prior : FiniteDist Ω) : PosteriorScheme prior Unit where
  weights := FiniteDist.pointMass ()
  posterior := fun _ => prior
  plausible ω := by simp

def full [DecidableEq Ω] (prior : FiniteDist Ω) : PosteriorScheme prior Ω where
  weights := prior
  posterior := FiniteDist.pointMass
  plausible ω := by
    simp [FiniteDist.expect, FiniteDist.pointMass]

variable {prior : FiniteDist Ω} (scheme : PosteriorScheme prior Signal)

/-- Finite law of iterated expectations, derived from Bayes plausibility. -/
theorem expect_expect (v : Ω → ℝ) :
    scheme.weights.expect (fun s => (scheme.posterior s).expect v) = prior.expect v := by
  unfold FiniteDist.expect
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [← Finset.sum_mul]
  exact congrArg (fun x => x * v ω) (scheme.plausible ω)

/-- An affine majorant valid at every posterior bounds every finite scheme.
No attainment assumption and no division by a possibly zero value is used. -/
theorem all_or_nothing (v : Ω → ℝ) (noDisclosure : FiniteDist Ω → ℝ)
    (β : ℝ) (hbound : ∀ μ, noDisclosure μ ≤ β * μ.expect v) :
    scheme.weights.expect (fun s => noDisclosure (scheme.posterior s)) ≤
      β * prior.expect v := by
  calc
    _ ≤ scheme.weights.expect (fun s => β * (scheme.posterior s).expect v) :=
      scheme.weights.expect_mono (fun s => hbound (scheme.posterior s))
    _ = β * scheme.weights.expect (fun s => (scheme.posterior s).expect v) :=
      scheme.weights.expect_mul β _
    _ = β * prior.expect v := by rw [scheme.expect_expect]

/-- The same bound for a scheme whose signalwise payoffs are below the
optimal no-disclosure value at that posterior. -/
theorem payoff_le_of_all_or_nothing (v : Ω → ℝ)
    (noDisclosure : FiniteDist Ω → ℝ) (payoff : Signal → ℝ) (β : ℝ)
    (hpayoff : ∀ s, payoff s ≤ noDisclosure (scheme.posterior s))
    (hbound : ∀ μ, noDisclosure μ ≤ β * μ.expect v) :
    scheme.weights.expect payoff ≤ β * prior.expect v := by
  exact (scheme.weights.expect_mono hpayoff).trans
    (scheme.all_or_nothing v noDisclosure β hbound)

end PosteriorScheme

end TransparencyLean
