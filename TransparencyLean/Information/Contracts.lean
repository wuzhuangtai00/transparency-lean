import TransparencyLean.Model.MinimumPayments
import TransparencyLean.Information.AllOrNothing

namespace TransparencyLean

variable {Ω Signal Agent : Type*} [Fintype Ω] [Fintype Signal]
  [Fintype Agent] [DecidableEq Agent]

def posteriorReward (p : FiniteDist Ω) (f : Ω → Finset Agent → ℝ)
    (S : Finset Agent) : ℝ := p.expect (fun ω => f ω S)

omit [Fintype Agent] [DecidableEq Agent] in
@[simp] theorem posteriorReward_pointMass [DecidableEq Ω] (ω : Ω)
    (f : Ω → Finset Agent → ℝ) : posteriorReward (FiniteDist.pointMass ω) f = f ω := by
  funext S
  simp [posteriorReward]

omit [Fintype Agent] [DecidableEq Agent] in
theorem posteriorReward_valid (p : FiniteDist Ω) {f : Ω → Finset Agent → ℝ}
    (hf : ∀ ω, ValidReward (f ω)) : ValidReward (posteriorReward p f) := by
  intro S
  constructor
  · exact p.expect_nonneg (fun ω => (hf ω S).1)
  · have h := p.expect_mono (fun ω => (hf ω S).2)
    simpa [posteriorReward] using h

omit [Fintype Agent] [DecidableEq Agent] in
theorem posteriorReward_monotone (p : FiniteDist Ω) {f : Ω → Finset Agent → ℝ}
    (hf : ∀ ω, Monotone (f ω)) : Monotone (posteriorReward p f) := by
  intro S T hST
  exact p.expect_mono (fun ω => hf ω hST)

omit [Fintype Agent] in
theorem posteriorReward_submodular (p : FiniteDist Ω) {f : Ω → Finset Agent → ℝ}
    (hf : ∀ ω, Submodular (f ω)) : Submodular (posteriorReward p f) := by
  intro S T
  have h := p.expect_mono (fun ω => hf ω S T)
  simpa only [FiniteDist.expect_add, posteriorReward] using h

omit [Fintype Agent] in
theorem posteriorReward_supermodular (p : FiniteDist Ω) {f : Ω → Finset Agent → ℝ}
    (hf : ∀ ω, Supermodular (f ω)) : Supermodular (posteriorReward p f) := by
  intro S T
  have h := p.expect_mono (fun ω => hf ω S T)
  simpa only [FiniteDist.expect_add, posteriorReward] using h

noncomputable def fullDisclosureValue (p : FiniteDist Ω)
    (f : Ω → Finset Agent → ℝ) (c : Agent → ℝ) : ℝ :=
  p.expect (fun ω => statelessValue (f ω) c)

noncomputable def noDisclosureValue (p : FiniteDist Ω)
    (f : Ω → Finset Agent → ℝ) (c : Agent → ℝ) : ℝ :=
  statelessValue (posteriorReward p f) c

/-- A finite public scheme, including the principal's chosen equilibrium. -/
structure ContractScheme (prior : FiniteDist Ω) (f : Ω → Finset Agent → ℝ)
    (c : Agent → ℝ) (Signal : Type*) [Fintype Signal] where
  information : PosteriorScheme prior Signal
  contract : Signal → Agent → ℝ
  team : Signal → Finset Agent
  feasible : ∀ s, FeasibleContract (contract s)
  equilibrium : ∀ s, IsEquilibrium (posteriorReward (information.posterior s) f)
    c (contract s) (team s)

namespace ContractScheme

variable {prior : FiniteDist Ω} {f : Ω → Finset Agent → ℝ} {c : Agent → ℝ}

def utility (scheme : ContractScheme prior f c Signal) : ℝ :=
  scheme.information.weights.expect (fun s =>
    principalUtility (posteriorReward (scheme.information.posterior s) f)
      (scheme.contract s) (scheme.team s))

/-- Paper Lemma 3.1, specialized to the actual contract model and finite signals. -/
theorem all_or_nothing (scheme : ContractScheme prior f c Signal)
    (hf : ∀ ω, ValidReward (f ω)) (β : ℝ)
    (hbound : ∀ μ, noDisclosureValue μ f c ≤ β * fullDisclosureValue μ f c) :
    scheme.utility ≤ β * fullDisclosureValue prior f c := by
  apply scheme.information.payoff_le_of_all_or_nothing
    (fun ω => statelessValue (f ω) c) (fun μ => noDisclosureValue μ f c)
  · intro s
    exact utility_le_statelessValue (posteriorReward_valid _ hf)
      (scheme.feasible s) (scheme.equilibrium s)
  · exact hbound

end ContractScheme

/-- Full disclosure's expected stateless values are jointly attained by one
finite public contract scheme. -/
theorem fullDisclosure_attained [DecidableEq Ω] (prior : FiniteDist Ω)
    (f : Ω → Finset Agent → ℝ) (c : Agent → ℝ)
    (hf : ∀ ω, ValidReward (f ω)) (hmono : ∀ ω, Monotone (f ω))
    (hc : ∀ i, 0 ≤ c i) :
    ∃ scheme : ContractScheme prior f c Ω,
      scheme.information = PosteriorScheme.full prior ∧
      scheme.utility = fullDisclosureValue prior f c := by
  classical
  choose S hteam hcontract hNE hvalue using
    (fun ω => statelessValue_attained (hf ω) (hmono ω) hc)
  let scheme : ContractScheme prior f c Ω := {
    information := PosteriorScheme.full prior
    contract := fun ω => minimumContract (f ω) c (S ω)
    team := S
    feasible := hcontract
    equilibrium := by
      intro ω
      simpa [PosteriorScheme.full] using hNE ω
  }
  refine ⟨scheme, rfl, ?_⟩
  change prior.expect (fun ω => principalUtility
    (posteriorReward (FiniteDist.pointMass ω) f) (minimumContract (f ω) c (S ω)) (S ω)) =
      prior.expect (fun ω => statelessValue (f ω) c)
  simp only [posteriorReward_pointMass, hvalue]

/-- No disclosure is implemented by a single public signal. -/
theorem noDisclosure_attained (prior : FiniteDist Ω)
    (f : Ω → Finset Agent → ℝ) (c : Agent → ℝ)
    (hf : ∀ ω, ValidReward (f ω)) (hmono : ∀ ω, Monotone (f ω))
    (hc : ∀ i, 0 ≤ c i) :
    ∃ scheme : ContractScheme prior f c Unit,
      scheme.information = PosteriorScheme.uninformative prior ∧
      scheme.utility = noDisclosureValue prior f c := by
  obtain ⟨S, _, hcontract, hNE, hvalue⟩ := statelessValue_attained
    (posteriorReward_valid prior hf) (posteriorReward_monotone prior hmono) hc
  let scheme : ContractScheme prior f c Unit := {
    information := PosteriorScheme.uninformative prior
    contract := fun _ => minimumContract (posteriorReward prior f) c S
    team := fun _ => S
    feasible := fun _ => hcontract
    equilibrium := fun _ => hNE
  }
  refine ⟨scheme, rfl, ?_⟩
  simpa [scheme, ContractScheme.utility, PosteriorScheme.uninformative, noDisclosureValue] using hvalue

end TransparencyLean
