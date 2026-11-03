# Mathematical model and proof architecture

This document describes the representation and proof structure of the Lean
formalization. Start with [README.md](README.md) for scope and verification,
and [THEOREMS.md](THEOREMS.md) for the paper-to-Lean correspondence.

## Mathematical representation

Agents are an arbitrary finite type and teams are `Finset Agent`. Probabilities
are arbitrary real-valued finite distributions with nonnegativity and a sum
of one. Contract shares are individually constrained to `[0,1]`; total shares
are not silently constrained to be at most one.

An equilibrium uses weak inequalities and the principal may select the best
equilibrium. The stateless benchmark is initially defined as a supremum over
feasible contract/equilibrium pairs; `statelessValue_attained` proves this is
an attained maximum using a finite optimization over teams.

The `Mixed` namespace adds independent effort probabilities in `[0,1]`.
`Mixed.isMixedEquilibrium_iff_bestResponse` checks that its support conditions
are equivalent to every unilateral change of effort probability. Its
stateless supremum is also proved to be a maximum, using compactness of the
closed contract/profile domain. The mixed results compare mixed optima on
both sides, with principal-favorable equilibrium selection.

`SingleAgent` specializes the agent type to `Unit`, retaining the same
contract and signaling definitions. [SINGLE_AGENT_PROOF.md](SINGLE_AGENT_PROOF.md)
explains its direct moment proof of 9/8, the exact connection to the paper's
tightness family, and which intermediate manuscript lemmas it bypasses.

`MultiAction` models one agent with an arbitrary nonempty finite action type,
nonnegative real expected rewards, action costs, and a linear share in `[0,1]`.
Rewards need not be bounded by one. Costs have minimum zero, as in the paper;
`cost_normalization` proves that subtracting the minimum cost leaves the
stateless value unchanged. Mixed responses are finite distributions, and their
support conditions are proved equivalent to all mixed utility comparisons.
[MULTI_ACTION_PROOF.md](MULTI_ACTION_PROOF.md) explains the checked welfare
argument, the exact lower-bound parameters, and finite attainment.

Finite public schemes retain the selected contract and equilibrium at each
posterior. The general `KernelContractScheme` instead starts with a probability
measure on signals for each state. It constructs the posterior, and requires
feasibility and equilibrium only almost everywhere. The selected payoff must
be almost everywhere strongly measurable, the regularity condition used for
expected utility. Integrability is proved from the compact feasible graph.
No compactness or finiteness assumption is imposed on the measurable signal
space. `KernelContractScheme` concerns selected pure equilibria;
`Mixed.KernelContractScheme` concerns selected mixed equilibria and imposes
the same regularity conventions, including almost-everywhere valid profiles.

Finite state space does **not** force every signal space to be finite. The
paper's footnote asserts existence of a finite optimal joint scheme, and
`kernel_optimum_attained`, `Mixed.kernel_optimum_attained`, and
`MultiAction.pure_kernel_optimum_attained` prove that claim for their respective
models. The reduction preserves the given prior and payoff exactly. Both the finite
replacement and the optimal scheme are realized as actual signal kernels;
no finite-support or posterior-existence claim is assumed as an axiom.

## Finite-support proof architecture

`CompactConvex.lean` obtains fixed-length mixtures from Carathéodory's theorem
and proves compactness of the convex hull of a compact finite-dimensional set.
`FeasiblePayoffs.lean` builds that compact set from posterior probabilities,
contract shares, and the closed incentive constraints for each possible team.
`FiniteSupport.lean` maximizes the payoff coordinate at a fixed prior and
turns every point in the convex hull into a finite contract scheme.

`MeasurableSignals.lean` integrates the posterior/payoff pair in the closed
convex hull, proving exact finite reduction for measurable posterior processes.
`KernelPosterior.lean` constructs those processes from arbitrary signal
kernels, proves almost-everywhere normalization and Bayes' rule, and handles
null events. `KernelContracts.lean` applies the reduction to kernel schemes.
`FiniteMeasure.lean` and `KernelRealization.lean` embed the finite replacements
back into the measurable/kernel models with unchanged expected utility. The
last file exports finite attainment and the complete general-signal upper bound.

`Mixed/FiniteSupport.lean` repeats the compact-image construction with effort
probabilities as an additional continuous coordinate. Multiplying the two
best-response inequalities by `x_i` and `1-x_i` describes equilibrium by
closed polynomial inequalities, including boundary probabilities. Thus the
continuum of mixed profiles does not invalidate the finite-support argument.

`MultiAction/FiniteSupport.lean` uses a posterior, a scalar share, and a
probability vector on actions. Multiplying every utility difference by the
selected action's probability gives closed equilibrium inequalities. This
again yields exact finite replacement and an attained joint optimum. A final
finite purification selects a supported pure best response at each signal.

## Pruning proof architecture

`Submodular/SetFunctions.lean` proves the diminishing-returns and marginal-sum
bounds. `Pruning.lean` tracks a kept team, an unprocessed team, reserved shares,
secured surplus, and residual budget. The invariant for each kept agent is
`saving i + c i ≤ reserved i * removalMarginal f team i`. It covers high and
low agents in one statement and permits free agents to be kept from the start.
This is the certificate's version of the paper's zero-cost folding argument.

`Completion.lean` chooses a remaining agent with maximum current marginal to
benchmark ratio, invokes the checked scalar inequalities, and inducts on the
number of remaining agents. At termination, reducing reserved shares to the
minimum incentive-compatible payments realizes the guaranteed utility.
`Potential.lean` instantiates the initial configuration, and `Transparency.lean`
derives the statewise expectation and public-scheme guarantees. These proofs
certify existence and utility; they make no running-time or numerical-precision
claim about an implementation of the pruning algorithm.

## Additive tightness proof architecture

`Model/Additive.lean` reduces the stateless optimum to a maximization over
finite teams using minimum-payment contracts. This proves upper bounds for
every feasible contract and selected equilibrium, as well as attainment by
the exhibited team.

`Submodular/TightnessInstance.lean` uses `Fin n` for both agents and states,
the uniform prior, and the paper's exact rewards and costs. It proves
normalization, monotonicity, additivity, and the two benchmark optimum values.
For a revealed state, an optimal team contains the high agent and `n/2`
others. `TightnessAlgebra.lean` proves the integer maximization without a
continuous relaxation: `(s-m)*(s-m-1) >= 0` for natural `s,m` handles the
rounding when `n=2m`.

`Submodular/Tightness.lean` proves

\[
\frac{U^N}{U^F}=\frac{4(3n^3+n-1)}{3n^2(3n+2)},\qquad
0\le\frac43-\frac{U^N}{U^F}\le\frac1n.
\]

`family_ratio_tendsto` states convergence of the actual benchmark ratio
along the even-sized family. `optimal_ratio_lower_bound` gives an attained
joint optimum whose ratio is at least this value. `no_better_factor` states
sharpness directly: for each real `beta < 4/3`, there is a finite additive
instance and a no-disclosure kernel with utility strictly greater than
`beta * fullDisclosureValue`, with strictly positive full-disclosure value.
