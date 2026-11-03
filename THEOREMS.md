# Paper-to-Lean correspondence

All declaration names below begin with `TransparencyLean.`. "Checked" means
the implementation is complete for its stated scope and passes the Lean build.

| Paper claim / label | Declaration or module | Status and scope |
| --- | --- | --- |
| Pure equilibrium definition | `isEquilibrium_iff_bestResponse` | Checked: both work/shirk deviations, weak inequalities. |
| Minimum-payment contracts | `Model/MinimumPayments.lean` | Checked: feasibility, implementation, componentwise minimality, and utility dominance. |
| Stateless optimum | `statelessValue_attained` | Checked: an optimal feasible team and minimum-payment contract exist. |
| Full / no disclosure benchmarks | `fullDisclosure_attained`, `noDisclosure_attained` | Checked: their values are implemented by finite public schemes. |
| Finite signals and posteriors | `Information/FiniteSignals.lean` | Checked in both directions, allowing zero prior masses and zero signal masses. |
| Iterated expectations | `PosteriorScheme.expect_expect` | Checked for arbitrary finite Bayes-plausible posterior schemes. |
| Lemma 3.1, `lem:approximation_extension` | `ContractScheme.all_or_nothing`, `KernelContractScheme.all_or_nothing` | Checked for finite schemes and arbitrary admissible measurable public signal kernels. |
| Lemma 4.2, `lem:pruning` | `potential_lemma`, `potential_with_free_team`, `Pruning.Config.completion` | Checked: full invariant, maximum-ratio ordering, all branches, terminating induction, and terminal equilibrium utility. Also supports a fixed team of zero-cost agents. |
| Theorem 4.1, `thm:submodular` | `noDisclosure_le_four_thirds`, `KernelContractScheme.submodular_four_thirds`, `submodular_full_transparency`, `Tightness.no_better_factor` | Checked in both directions for pure equilibria. Upper bound allows arbitrary admissible measurable public signal kernels, real probabilities, nonnegative costs, and positive baseline rewards. Includes an actual full revelation kernel. |
| Proposition 4.3, `prop:submodular-tight` | `Tightness.ratio_exact`, `optimal_ratio_lower_bound`, `family_ratio_tendsto`, `no_better_factor` | Checked: the paper's additive family for every even n >= 2; exact benchmark optima, finite-n ratio, and asymptotic sharpness. An actual finite joint optimizer attains at least the displayed ratio. |
| Theorem 5.1, `thm:supermodular` | `SupermodularExample.separation`, `no_finite_factor` | Checked, pure equilibria, exactly normalized instance. |
| Bayesian posterior existence for general signal kernels | `SignalKernel.posterior_measurable`, `posterior_joint`, `posterior_plausible` | Checked via Radon-Nikodym derivatives; normalization and Bayes' rule include null events and zero-prior states. |
| Exact finite-support reduction | `KernelContractScheme.finite_equivalent`, `Mixed.KernelContractScheme.finite_equivalent` and the respective `ContractScheme.toKernelContract_utility` | Checked for pure and mixed selection: finite replacement preserves the prior and payoff and is implementable as a signal kernel. |
| Finite-signal attainment footnote | `kernel_optimum_attained`, `Mixed.kernel_optimum_attained`, `supportBound_eq` | Checked in both equilibrium models: a finite joint kernel/contract scheme dominates every admissible measurable scheme. At most `|Ω| + 2` signals; this bound is not claimed sharp. |
| Mixed Nash definition and attained stateless benchmark | `Mixed.isMixedEquilibrium_iff_bestResponse`, `Mixed.statelessValue_attained` | Checked for independent effort probabilities, including zero/one probabilities, zero costs, ties, and positive baseline rewards. |
| Lemma A.1, `lem:mixing-reduction` | `Mixed/Bernoulli.lean`, `Mixed/Reduction.lean` | Checked: all three parts, preservation of all stated structural properties, posterior compatibility, and minimum-payment implementation including degenerate agents. |
| Theorem A.2, `thm:mixed-transparency` | `Mixed.submodular_full_transparency`, `Mixed.no_better_factor`, `Mixed.family_ratio_tendsto` | Checked: sharp 4/3 for arbitrary admissible measurable signal kernels, with mixed equilibria on both sides and an attained full-revelation benchmark. |
| Appendix A, supermodular extension | `Mixed.supermodular_value_eq_pure`, `Mixed.supermodular_separation`, `Mixed.supermodular_no_finite_factor` | Checked for monotone supermodular binary-action rewards; the exact two-state example retains zero revealed value and positive no-disclosure value. |
| Theorem B.1, `thm:approx_fully_revealing_binary` | `SingleAgent.full_transparency`, `mixed_full_transparency`, `SingleAgent.Tightness.no_better_factor`, `mixed_no_better_factor` | Checked: sharp 9/8 for arbitrary admissible measurable public signals, in both equilibrium models. Upper bound uses the direct moment proof in `SINGLE_AGENT_PROOF.md`. |
| Theorem B.1, zero-baseline clause | `SingleAgent.full_optimal_of_zero_baseline`, `mixed_full_optimal_of_zero_baseline` | Checked: an actual full-revelation kernel is jointly optimal if every baseline reward is zero. Includes zero costs and zero benchmark value. |
| Stateless single-agent payoff, `obs:optimal-utility` | `SingleAgent.value_formula`, `value_zero_cost`, `value_high_cost` | Checked: exact payoff formula and cost edge cases. The square-root cutoff and concavity claims are not formalized. |
| Single-agent support reduction and calculus, `lem:worst_case_single`, `lem:R-monotone`, `lem:limit_approx` | Replaced by `SingleAgent/Moments.lean` for the main theorem | These intermediate manuscript claims are not certified; the direct proof establishes the sharp bound without them. The actual `k = X = 2` family and its limit are checked. |
| Theorem C.1, `thm:multi_action` | `MultiAction.full_transparency`, `MultiAction.LowerBound.linear_separation`, `no_constant_factor` | Checked: upper factor N for N actions, arbitrary admissible measurable signals, pure or mixed responses; two-state lower-bound family has N=2n-1 actions and actual hidden/full ratio (N+1)/4. |
| Welfare theorem cited in Theorem C.1 | `MultiAction.welfare_le_card_value` | Checked by finite induction inside Lean; no external theorem is assumed. |
| Appendix A, single-agent multi-action mixing observation | `MultiAction.mixedBestResponse_iff`, `mixed_dominated`, `pure_kernel_optimum_attained` | Checked: equivalence to all mixed deviations, pure domination at a fixed share, and an attained pure-response joint optimum against mixed competitors. |
| Finite-signal footnote for the multi-action extension | `MultiAction.KernelContractScheme.finite_equivalent`, `kernel_optimum_attained`, `pure_kernel_optimum_attained` | Checked: exact finite replacement and optimal kernel with at most |Omega|+2 signals; an optimum can use pure responses. |
| Theorem 4.4, `thm:computation` | Separate computational scope | Not claimed by this information-theoretic checkpoint. |

## Scope remaining outside the certificate

The main information-theoretic results in the selected scope are implemented.
The computational theorem remains outside that scope. The intermediate
single-agent cutoff, concavity, two-state reduction, and derivative arguments
are not independently certified; Theorem B.1 uses the checked direct moment
proof instead. The multi-action module concerns linear contracts, as specified
in its definitions, and does not introduce a general nonlinear-payment model.

## Checked multi-action theorem

All names in this table have prefix `MultiAction.`.

| Claim | Declaration |
| --- | --- |
| Stateless linear-contract supremum is attained | `value_attained` |
| Minimum-cost normalization preserves value | `cost_normalization` |
| Mixed support condition equals best response against all mixed deviations | `mixedBestResponse_iff` |
| Same-share pure response weakly improves revenue | `mixed_dominated` |
| Each action's welfare is at most N times stateless value | `welfare_le_card_value` |
| Full revelation attains an N-approximation against all measurable signals | `full_transparency` |
| Actual two-outcome distributions realize the lower-bound expected rewards | `LowerBound.expected_outcome` |
| Exact revealed value and full-disclosure value are one | `LowerBound.revealed_value`, `full_disclosure_value` |
| No disclosure induces the top action and earns n/2 | `LowerBound.hidden_equilibrium`, `hidden_scheme_utility` |
| Total count N=2n-1 and witnessed ratio (N+1)/4 | `LowerBound.action_count`, `linear_separation` |
| Every action-independent constant fails | `LowerBound.no_constant_factor` |
| Exact finite replacement; attained finite and pure joint optimum | `KernelContractScheme.finite_equivalent`, `pure_kernel_optimum_attained` |

The lower family uses every integer n>=2, encoded by n=m+2, and fixes
gamma=1/(4n). This specialization suffices for the theorem's linear lower
bound; the full gamma-parameterized family is not asserted. The exhibited
no-disclosure contract need not be optimal. See
[MULTI_ACTION_PROOF.md](MULTI_ACTION_PROOF.md) for the complete proof map.

## Checked dependency chain for the 4/3 upper bound

1. Submodularity implies increasing removal marginals as the team shrinks,
   and bounds the sum of terminal marginals by the team's reward minus the
   empty-team reward.
2. `Pruning.Config` maintains disjoint kept/remaining teams, nonnegative
   residual budget, a payment balance, lower bounds on remaining marginals,
   and an incentive inequality for each kept agent's reserved share/surplus.
3. `Config.completion` inducts on the number of remaining agents. The
   maximum-ratio rule supplies the unaffordable branch's nonpositive correction.
   Its terminal case uses an actual minimum-payment equilibrium contract.
4. `potential_with_free_team` initializes the invariant with zero-cost agents
   already kept. `potential_lemma` recovers the paper's benchmark `d_i=c_i/k_i`.
5. `noDisclosure_le_four_thirds` chooses an attained optimum at the prior,
   averages the statewise bound, and cancels the centered correction. It
   explicitly covers zero no-disclosure value and positive baseline reward.
6. `ContractScheme.submodular_four_thirds` applies the contract-specific
   All-or-Nothing lemma to every finite posterior scheme. Full-disclosure
   attainment was proved separately, so the benchmark is implementable.
7. `KernelContractScheme.finite_equivalent` reduces any admissible measurable
   signal kernel to a finite scheme with exactly the same payoff. This gives
   the general-signal upper bound. `submodular_full_transparency` realizes the
   full-disclosure benchmark as a kernel and states the comparison without
   dividing by either scheme's utility.

## Checked additive lower bound

For every even `n >= 2`, agents and states are `Fin n`, the prior is uniform,
`M = 2*n^2+n+1`, and `D = (2*n-1)*M`. Each agent costs `n/D`.
In state `omega`, that agent's additive weight is `n/(2*n-1)` and every
other agent's weight is `1/(2*n-1)`. All weights are positive and their sum
is one.

| Claim | Declaration under `Tightness.` |
| --- | --- |
| No-disclosure optimum `(3*n^3+n-1)/D` | `no_disclosure_value` |
| Each revealed-state optimum `3*n^2*(3*n+2)/(4*D)` | `revealed_value` |
| Full-disclosure expected optimum has the same value | `full_disclosure_value` |
| Exact ratio `4*(3*n^3+n-1)/(3*n^2*(3*n+2))` | `ratio_exact` |
| Gap from 4/3 lies between zero and `1/n` | `ratio_gap_bounds` |
| Actual benchmark ratios converge to 4/3 along `n=2*(m+1)` | `family_ratio_tendsto` |
| An attained joint optimum dominates the no-disclosure ratio | `optimal_ratio_lower_bound` |
| Every real factor below 4/3 fails on a finite additive instance | `no_better_factor` |

The benchmark proofs bound every team and exhibit a maximizing team; they
do not assume optimality of a proposed contract. The high-agent branch uses
the integer inequality `(s-m)*(s-m-1) >= 0`. For teams without the high
agent, the certificate bounds the payoff over the larger interval `0 <= s <= n`.
This slightly different bound still proves the paper's exact revealed-state
optimum. `opaque_scheme` realizes the lower-bound payoff by an actual
one-signal public kernel. Full-disclosure value is proved positive before
using division or interpreting a ratio.

## Scope of the finite-attainment theorem

The state and agent spaces are finite. The signal space is any measurable
space; it need not be finite, countable, or compact. Each state has a
probability measure on signals. Posterior probabilities are constructed from
the prior-weighted component measures using Radon-Nikodym derivatives, with
the prior substituted on the exceptional null set. Contracts and selected
pure or mixed equilibria satisfy their constraints almost everywhere. The selected
payoff is almost everywhere strongly measurable; integrability follows from
the compact feasible graph. These are the formal model's expected-utility
regularity conventions, not a finite-support assumption.

The compact graph records the original shares and equilibrium constraints,
so no continuity of the optimized stateless value function is assumed. Its
posterior/payoff image has compact convex hull. Every scheme's mean belongs
to this hull, and its slice at a fixed prior has a maximizing payoff. A
Carathéodory representation implements that payoff using at most `|Ω| + 2`
signals. `kernel_optimum_attained` includes realization in the original
kernel model, not just existence of a posterior lottery.

For mixed equilibria, the graph has an additional effort-probability vector.
`Mixed.equilibrium_complementarity` proves that the support conditions are
equivalent to closed polynomial inequalities on the probability cube. This
proves compactness despite the continuum of profiles. The same ambient
posterior/payoff space gives the same conservative `|Ω| + 2` support bound.
`Mixed.kernel_optimum_attained` includes kernel realization and quantifies
over competitors on arbitrary measurable signal spaces.

## Checked mixed reduction and transparency chain

All declarations in this section begin with `TransparencyLean.Mixed.`.

1. `Bernoulli.lean` defines independent sampling by the exact finite sum
   `sum_R (prod_{i in R} x_i) * (prod_{i in A \\ R} (1-x_i)) * f(R)`.
   Its weights normalize to one. Masking probabilities outside a team is
   equivalent to intersecting the sampled random team with that team.
2. `isMixedEquilibrium_iff_bestResponse` identifies the incentive conditions
   with all unilateral mixed deviations. `pure_equilibrium_iff` embeds the
   original pure model with identical utility.
3. The auxiliary reward `auxiliary f x T` is the expected reward when agents
   in `T` independently work with probabilities `x`; auxiliary costs are
   `x_i*c_i`. The construction preserves reward validity, monotonicity,
   submodularity, supermodularity, and additivity. It commutes with posterior
   averaging.
4. `posterior_grand_equilibrium` proves A.1(ii) with exact utility equality.
   `minimum_implementation` proves A.1(iii), explicitly separating zero
   probabilities and zero costs before cancelling a denominator.
   `statewise_comparison` compares attained auxiliary pure optima to mixed
   stateless values in the original instance.
5. `noDisclosure_le_four_thirds` applies the existing pure theorem to the
   auxiliary instance. The finite and kernel versions of `all_or_nothing`
   transfer this comparison to public signaling. In the general kernel
   model, posterior integrability and the law of iterated expectations are
   proved directly, and selected-payoff integrability follows from boundedness.
6. `statelessValue_attained`, `fullDisclosure_attained`, and
   `submodular_full_transparency` ensure that the mixed full-disclosure
   benchmark is implemented by an actual full-revelation kernel.
7. `supermodular_value_eq_pure` rounds positive effort probabilities to a
   pure team and zeros payments outside that team. The proof separately
   covers contracts whose total share exceeds one. Additive rewards are a
   special case, so `tightness_ratio_exact`, `family_ratio_tendsto`, and
   `no_better_factor` retain the paper's exact additive family under mixing.
8. `FiniteSupport.lean` proves exact finite replacement and existence of a
   finite joint optimizer for mixed schemes. No continuity of the optimized
   stateless value function is assumed.

## Checked single-agent theorem

The agent type is `Unit`; rewards are arbitrary monotone maps from its two
teams to `[0,1]`. Costs are arbitrary nonnegative real numbers. The
implementation uses the existing contract and signaling models, not a
separate scalar problem whose connection to contracts is assumed.

All declarations in this table begin with `TransparencyLean.SingleAgent.`.

| Claim | Declaration |
| --- | --- |
| Exact stateless payoff with an effort-feasibility guard | `value_formula` |
| Statewise loss `r = p₁ - value` satisfies `r² <= c*(p₀+r)` | `loss_square_bound` |
| Finite variance inequality and sum-of-squares certificate | `square_expect_le_expect_square`, `nine_eighths_from_moments` |
| No-disclosure value is at most 9/8 of full disclosure | `noDisclosure_le_nine_eighths` |
| Arbitrary measurable public signals satisfy the same guarantee | `kernel_nine_eighths`, `mixed_kernel_nine_eighths` |
| Full-revelation benchmark is attained | `full_transparency`, `mixed_full_transparency` |
| Full revelation is optimal at zero baseline | `full_optimal_of_zero_baseline`, `mixed_full_optimal_of_zero_baseline` |
| Exact two-state family with `k = X = 2` | `Tightness.no_disclosure_value`, `full_disclosure_value`, `ratio_exact` |
| Actual family ratios converge to 9/8 | `Tightness.family_ratio_tendsto`, `mixed_family_ratio_tendsto` |
| Every smaller factor fails on an actual one-signal kernel | `Tightness.no_better_factor`, `mixed_no_better_factor` |

For `0 < c <= 1/4`, the family puts mass `2c` on `(p₀,p₁)=(0,1)` and mass
`1-2c` on `(2c,4c)`. Its exact ratio is
`(3-4c)^2 / (4*(1-c)*(2-3c))`. The gap from 9/8 is between zero and `c`.
Convergence uses the valid sequence `c=1/(n+4)`; no zero-cost or zero-payoff
instance is used in a denominator.

The upper-bound proof is an alternate mathematical argument, fully checked
in Lean. See [SINGLE_AGENT_PROOF.md](SINGLE_AGENT_PROOF.md) for the stateless
loss inequality, averaging step, and explicit polynomial identity. The
manuscript's reduction to two states and derivative analysis are not used or
asserted as hypotheses.

## Exact supermodular instance

The two states have probability 1/2. Agent costs are 1/4 and 1/2.

| Team | State false | State true |
| --- | ---: | ---: |
| Empty | 0 | 0 |
| Agent 0 only | 1/4 | 5/42 |
| Agent 1 only | 1/4 | 0 |
| Both | 1 | 5/6 |

The opaque contract pays shares 6/19 and 28/41. Their sum is 778/779, the
expected success probability with both agents working is 11/12, and the
principal's utility is 11/9348. Every feasible equilibrium under either
revealed state has utility at most zero; the zero contract attains zero.
