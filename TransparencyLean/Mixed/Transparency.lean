import TransparencyLean.Mixed.Reduction
import TransparencyLean.Mixed.Attainment
import TransparencyLean.Submodular.Transparency

/-! The mixed 4/3 guarantee and attained information benchmarks. -/

namespace TransparencyLean.Mixed

noncomputable section

variable {Ω Agent : Type*} [Fintype Ω] [Fintype Agent] [DecidableEq Agent]

def noDisclosureValue (p : FiniteDist Ω) (f : Ω → Finset Agent → ℝ) (c : Agent → ℝ) : ℝ :=
  statelessValue (posteriorReward p f) c

def fullDisclosureValue (p : FiniteDist Ω) (f : Ω → Finset Agent → ℝ) (c : Agent → ℝ) : ℝ :=
  p.expect (fun ω => statelessValue (f ω) c)

/-- The mixed no-disclosure comparison, obtained from the checked pure theorem. -/
theorem noDisclosure_le_four_thirds (prior : FiniteDist Ω)
    {f : Ω → Finset Agent → ℝ} {c : Agent → ℝ}
    (hf : ∀ ω, ValidReward (f ω)) (hmono : ∀ ω, Monotone (f ω))
    (hsub : ∀ ω, Submodular (f ω)) (hc : ∀ i, 0 ≤ c i) :
    noDisclosureValue prior f c ≤ (4 / 3) * fullDisclosureValue prior f c := by
  apply statelessValue_le hc
  intro α x hα hx heq
  obtain ⟨hgrand, hutility⟩ := posterior_grand_equilibrium prior f hx heq
  have hN := TransparencyLean.utility_le_statelessValue
    (posteriorReward_valid prior (fun ω => auxiliary_valid (hf ω) hx)) hα hgrand
  rw [hutility] at hN
  have hupper := TransparencyLean.noDisclosure_le_four_thirds prior
    (fun ω => auxiliary_valid (hf ω) hx) (fun ω => auxiliary_monotone (hmono ω) hx)
    (fun ω => auxiliary_submodular (hsub ω) hx) (auxiliaryCost_nonneg hx hc)
  have hF : TransparencyLean.fullDisclosureValue prior (fun ω => auxiliary (f ω) x)
      (auxiliaryCost x c) ≤ fullDisclosureValue prior f c :=
    prior.expect_mono (fun ω => statewise_comparison (hf ω) (hmono ω) hc hx)
  change utility (posteriorReward prior f) α x ≤
    TransparencyLean.noDisclosureValue prior (fun ω => auxiliary (f ω) x) (auxiliaryCost x c) at hN
  linarith

structure ContractScheme (prior : FiniteDist Ω) (f : Ω → Finset Agent → ℝ)
    (c : Agent → ℝ) (Signal : Type*) [Fintype Signal] where
  information : PosteriorScheme prior Signal
  contract : Signal → Agent → ℝ
  profile : Signal → Agent → ℝ
  feasible : ∀ s, FeasibleContract (contract s)
  valid : ∀ s, ValidProfile (profile s)
  equilibrium : ∀ s, IsMixedEquilibrium (posteriorReward (information.posterior s) f)
    c (contract s) (profile s)

namespace ContractScheme

variable {Signal : Type*} [Fintype Signal]
variable {prior : FiniteDist Ω} {f : Ω → Finset Agent → ℝ} {c : Agent → ℝ}

def utility (scheme : ContractScheme prior f c Signal) : ℝ :=
  scheme.information.weights.expect (fun s => Mixed.utility
    (posteriorReward (scheme.information.posterior s) f) (scheme.contract s) (scheme.profile s))

def ofPure (scheme : TransparencyLean.ContractScheme prior f c Signal) : ContractScheme prior f c Signal where
  information := scheme.information
  contract := scheme.contract
  profile s := pureProfile (scheme.team s)
  feasible := scheme.feasible
  valid _ := pureProfile_valid _
  equilibrium s := (pure_equilibrium_iff _ _ _ _).mpr (scheme.equilibrium s)

@[simp] theorem ofPure_utility (scheme : TransparencyLean.ContractScheme prior f c Signal) :
    (ofPure scheme).utility = scheme.utility := by
  simp [utility, ofPure, TransparencyLean.ContractScheme.utility]

theorem all_or_nothing (scheme : ContractScheme prior f c Signal)
    (hf : ∀ ω, ValidReward (f ω)) (β : ℝ)
    (hbound : ∀ μ, noDisclosureValue μ f c ≤ β * fullDisclosureValue μ f c) :
    scheme.utility ≤ β * fullDisclosureValue prior f c := by
  apply scheme.information.payoff_le_of_all_or_nothing
    (fun ω => statelessValue (f ω) c) (fun μ => noDisclosureValue μ f c)
  · intro s
    exact utility_le_statelessValue (posteriorReward_valid _ hf)
      (scheme.feasible s) (scheme.valid s) (scheme.equilibrium s)
  · exact hbound

/-- Theorem A.2 for finite public signals, with mixed equilibria at both benchmarks. -/
theorem submodular_four_thirds (scheme : ContractScheme prior f c Signal)
    (hf : ∀ ω, ValidReward (f ω)) (hmono : ∀ ω, Monotone (f ω))
    (hsub : ∀ ω, Submodular (f ω)) (hc : ∀ i, 0 ≤ c i) :
    scheme.utility ≤ (4 / 3) * fullDisclosureValue prior f c :=
  scheme.all_or_nothing hf (4 / 3) (fun μ => noDisclosure_le_four_thirds μ hf hmono hsub hc)

end ContractScheme

/-- Full disclosure's mixed benchmark is attained by a finite scheme. -/
theorem fullDisclosure_attained [DecidableEq Ω] (prior : FiniteDist Ω)
    (f : Ω → Finset Agent → ℝ) (c : Agent → ℝ)
    (hf : ∀ ω, ValidReward (f ω)) (hc : ∀ i, 0 ≤ c i) :
    ∃ full : ContractScheme prior f c Ω,
      full.information = PosteriorScheme.full prior ∧ full.utility = fullDisclosureValue prior f c := by
  choose α x hα hx heq hu using fun ω => statelessValue_attained (hf ω) hc
  let scheme : ContractScheme prior f c Ω := {
    information := PosteriorScheme.full prior
    contract := α
    profile := x
    feasible := hα
    valid := hx
    equilibrium := fun ω => by simpa [PosteriorScheme.full] using heq ω
  }
  refine ⟨scheme, rfl, ?_⟩
  change prior.expect (fun ω => utility (posteriorReward (FiniteDist.pointMass ω) f) (α ω) (x ω)) = _
  simp_rw [posteriorReward_pointMass, hu]
  rfl

theorem noDisclosure_attained (prior : FiniteDist Ω) (f : Ω → Finset Agent → ℝ) (c : Agent → ℝ)
    (hf : ∀ ω, ValidReward (f ω)) (hc : ∀ i, 0 ≤ c i) :
    ∃ hidden : ContractScheme prior f c Unit,
      hidden.information = PosteriorScheme.uninformative prior ∧
      hidden.utility = noDisclosureValue prior f c := by
  obtain ⟨α, x, hα, hx, heq, hu⟩ := statelessValue_attained (posteriorReward_valid prior hf) hc
  let scheme : ContractScheme prior f c Unit := {
    information := PosteriorScheme.uninformative prior
    contract := fun _ => α
    profile := fun _ => x
    feasible := fun _ => hα
    valid := fun _ => hx
    equilibrium := fun _ => heq
  }
  refine ⟨scheme, rfl, ?_⟩
  simpa [scheme, ContractScheme.utility, PosteriorScheme.uninformative, noDisclosureValue] using hu

end

end TransparencyLean.Mixed
