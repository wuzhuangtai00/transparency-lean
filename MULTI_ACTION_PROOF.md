# Checked proof of the multi-action result

This module certifies Theorem C.1 of the reference manuscript, including the
welfare bound that its proof cites externally. It also extends the finite
optimal-signal existence argument to the multi-action model.

## Model and scope

There is one agent, a nonempty finite action set A, a finite state set, and
nonnegative real expected rewards r(omega,i). Costs c(i) are state independent.
A linear contract has share alpha in [0,1]. The agent maximizes
alpha*r(i)-c(i); the principal receives (1-alpha)*r(i). Weak comparisons permit
ties, with the response selected by the principal. Expected rewards can exceed
one. In the lower family they arise from checked two-outcome distributions.

`value` is a supremum over feasible shares and selected pure best responses.
Compactness proves attainment. A mixed response is a distribution on actions;
`mixedBestResponse_iff` proves that support on pure best responses is equivalent
to optimality against every alternative mixed distribution. `mixed_dominated`
selects a supported pure action with at least the mixed principal payoff.
Consequently the full-disclosure benchmark is optimal even when mixing is
allowed. The module does not model general nonlinear payment schedules.

The upper transparency theorem assumes nonnegative costs with a zero-cost
action, matching the manuscript's normalization. `cost_normalization` obtains
this by subtracting the minimum cost and proves that the stateless value is
unchanged. Incentive comparisons are invariant under this common shift.

## Welfare bound without an external assumption

For N actions, `welfare_le_card_value` proves, for every action i,

\[
r_i-c_i\le N\,\mathrm{value}(r,c).
\]

The stronger induction lemma allows any finite action subset S and any
nonnegative bound M on all its feasible equilibrium payoffs. Remove an action
j of maximum reward, leaving T. Every equilibrium of T either remains an
equilibrium of S or is displaced by j at the same share. In the latter case
the principal's payoff weakly increases. The induction hypothesis therefore
bounds each action's welfare in T by |T|M.

If j's welfare is no larger than another action's, that bound suffices.
Otherwise define its first inducing share by

\[
\alpha=\max_{k\in S}\max\left(0,\frac{c_j-c_k}{r_j-r_k}\right).
\]

The Lean proof handles equal rewards separately; division by zero contributes
zero to this maximum and is never used in a division inequality. Strict welfare
dominance proves alpha is in [0,1] and j is a best response. If alpha=0, j's
welfare is at most its revenue, hence at most M. Otherwise a maximizing
competitor k has strictly smaller reward and is in T. Its binding comparison
gives

\[
r_j-c_j=(r_k-c_k)+(1-\alpha)(r_j-r_k)
\le |T|M+(1-\alpha)r_j\le |S|M.
\]

This proves the cited welfare approximation directly in Lean.

## From welfare to arbitrary public signals

At any posterior, a zero-cost action gives the agent nonnegative utility.
Thus the principal's payoff from a best response i is at most its posterior
welfare. The statewise welfare bound gives

\[
U_P\le \mathbb E[r_i-c_i\mid s]
\le N\,\mathbb E[\mathrm{value}(r_\omega,c)\mid s].
\]

Pure domination gives the same inequality for mixed responses. Integrating
over signals and using the checked Bayesian posterior construction gives
U_P <= N*U_F. `full_transparency` returns an actual full-revelation kernel with
payoff U_F and quantifies over every admissible measurable public signal space.
Selected payoffs must be almost everywhere strongly measurable; feasibility
and incentives hold almost everywhere. Integrability is proved, not assumed.

## Exact lower-bound specialization

For every n=m+2, set B=4n and gamma=1/B. The actions consist of one top action
and two copies of each lower level k=0,...,n-2, so N=2n-1. In each of two equally
likely states, exactly one copy of each lower level has expected reward B^k;
the other has reward zero. The top reward is B^(n-1) in both states. Level k
has cost

\[
c_k=B^k-(k+1)+k/B.
\]

These are exactly the paper's costs with zero-based indexing. They are
nonnegative and c_0=0. `outcomeDist` realizes every expected reward using the
two common outcomes zero and B^(n-1).

At a revealed state, comparing an active level k+1 to its predecessor forces
its principal revenue to be at most one. An inactive action earns zero, and
the active level-zero action earns at most one. Share zero with the active
level-zero action attains one. Hence every revealed-state optimum and U_F
equal one, including mixed best responses.

Without disclosure, offer alpha=1-n/(2*B^(n-1)). Its feasibility is checked.
The top action gives agent utility n/2-(n-1)/B > 1/2, while every lower action
gives at most 1/2. The top action is therefore a best response, and the
principal earns exactly n/2. `linear_separation` packages this as an actual
one-signal kernel and states 4*U_hidden=N+1. The proof makes no claim that
this no-disclosure contract is optimal. `no_constant_factor` produces an
instance defeating every real constant independent of N.

## Finite optimum and pure selection

The feasible posterior/payoff set is the continuous image of a compact domain
of posterior probabilities, a share in [0,1], and a probability vector p on
actions. The equilibrium inequalities

\[
p_i\bigl[\alpha r_j-c_j-(\alpha r_i-c_i)\bigr]\le0
\quad\text{for all }i,j
\]

are closed and equivalent to the mixed support condition. The existing
Caratheodory and integration machinery gives an exact finite replacement
using at most |Omega|+2 signals. Maximizing the payoff coordinate at the fixed
prior gives an attained joint optimum. Purifying each of its finitely many
responses weakly improves revenue and preserves the signal scheme.
`pure_kernel_optimum_attained` thus gives a finite, pure-response optimum
against all measurable mixed-response competitors. No finite-signal assumption
is imposed on those competitors, and the support bound is not claimed sharp.
