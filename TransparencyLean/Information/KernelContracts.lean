import TransparencyLean.Information.KernelPosterior

namespace TransparencyLean

open MeasureTheory

noncomputable section

variable {Ω Agent : Type*} [Fintype Ω] [Fintype Agent] [DecidableEq Agent]

/-- A public signal kernel together with its contract and selected equilibrium.
The posterior is constructed from the kernel, rather than supplied with a
Bayes-plausibility hypothesis. Payoff measurability is the usual condition for
the expected-utility objective to be defined. -/
structure KernelContractScheme (prior : FiniteDist Ω) (f : Ω → Finset Agent → ℝ)
    (c : Agent → ℝ) (Signal : Type*) [MeasurableSpace Signal] where
  kernel : SignalKernel Ω Signal
  contract : Signal → Agent → ℝ
  team : Signal → Finset Agent
  feasible : ∀ᵐ s ∂kernel.signalLaw prior, FeasibleContract (contract s)
  equilibrium : ∀ᵐ s ∂kernel.signalLaw prior,
    IsEquilibrium (posteriorReward (kernel.posterior prior s) f) c (contract s) (team s)
  measurable_payoff : AEStronglyMeasurable (fun s => principalUtility
    (posteriorReward (kernel.posterior prior s) f) (contract s) (team s)) (kernel.signalLaw prior)

namespace KernelContractScheme

variable {Signal : Type*} [MeasurableSpace Signal]
variable {prior : FiniteDist Ω} {f : Ω → Finset Agent → ℝ} {c : Agent → ℝ}

def utility (scheme : KernelContractScheme prior f c Signal) : ℝ :=
  ∫ s, principalUtility (posteriorReward (scheme.kernel.posterior prior s) f)
    (scheme.contract s) (scheme.team s) ∂scheme.kernel.signalLaw prior

def toPosteriorScheme (scheme : KernelContractScheme prior f c Signal) :
    MeasurableContractScheme prior f c Signal where
  weights := scheme.kernel.signalLaw prior
  probability := inferInstance
  posterior := scheme.kernel.posterior prior
  contract := scheme.contract
  team := scheme.team
  feasible := scheme.feasible
  equilibrium := scheme.equilibrium
  measurable_outcome := (scheme.kernel.posterior_measurable prior).aestronglyMeasurable.prodMk
    scheme.measurable_payoff
  plausible := scheme.kernel.posterior_plausible prior

@[simp] theorem toPosteriorScheme_utility (scheme : KernelContractScheme prior f c Signal) :
    scheme.toPosteriorScheme.utility = scheme.utility := rfl

/-- Exact finite reduction from an arbitrary measurable signal kernel, with
all posterior existence and Bayes-plausibility obligations discharged. -/
theorem finite_equivalent (scheme : KernelContractScheme prior f c Signal) :
    ∃ finite : ContractScheme prior f c (Fin (supportBound Ω)), finite.utility = scheme.utility :=
  scheme.toPosteriorScheme.finite_equivalent

theorem all_or_nothing (scheme : KernelContractScheme prior f c Signal)
    (hf : ∀ ω, ValidReward (f ω)) (β : ℝ)
    (hbound : ∀ μ, noDisclosureValue μ f c ≤ β * fullDisclosureValue μ f c) :
    scheme.utility ≤ β * fullDisclosureValue prior f c := by
  obtain ⟨finite, hfinite⟩ := scheme.finite_equivalent
  rw [← hfinite]
  exact finite.all_or_nothing hf β hbound

theorem submodular_four_thirds (scheme : KernelContractScheme prior f c Signal)
    (hf : ∀ ω, ValidReward (f ω)) (hmono : ∀ ω, Monotone (f ω))
    (hsub : ∀ ω, Submodular (f ω)) (hc : ∀ i, 0 ≤ c i) :
    scheme.utility ≤ (4 / 3) * fullDisclosureValue prior f c :=
  scheme.toPosteriorScheme.submodular_four_thirds hf hmono hsub hc

end KernelContractScheme

/-- Finite attainment for the original kernel representation of public
signals. The finite output is implementable by `PosteriorScheme.toKernel`. -/
theorem optimal_finite_for_kernels (prior : FiniteDist Ω) (f : Ω → Finset Agent → ℝ)
    (c : Agent → ℝ) (hc : ∀ i, 0 ≤ c i) :
    ∃ optimal : ContractScheme prior f c (Fin (supportBound Ω)),
      ∀ (Signal : Type*) [MeasurableSpace Signal]
        (scheme : KernelContractScheme prior f c Signal), scheme.utility ≤ optimal.utility := by
  obtain ⟨optimal, hopt⟩ := optimal_finite_for_measurable prior f c hc
  exact ⟨optimal, fun Signal _ scheme => hopt Signal scheme.toPosteriorScheme⟩

end

end TransparencyLean
