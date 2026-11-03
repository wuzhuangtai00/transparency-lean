# A direct certificate of the single-agent 9/8 bound

This is the proof implemented in `SingleAgent/Moments.lean` and
`SingleAgent/Transparency.lean`. It establishes Theorem B.1 by a different
route from the manuscript's two-state reduction and calculus argument.
Those intermediate reduction and derivative claims are not certified here.
The tightness construction is the manuscript's own family with `k = X = 2`.
The manuscript has not been edited.

## Stateless loss inequality

In one state, write `a = p₀`, `b = p₁`, `d = b-a`, and let `v` be the
optimal principal utility. The formal model represents the single agent by
`Unit`, with the same feasible shares and equilibrium definitions used by
the multi-agent certificate.

The exact stateless optimum is

\[
v=\begin{cases}
\max\{a,(1-c/d)b\},&c\le d,\\
a,&c>d.
\end{cases}
\]

Lean's totalized division gives `0/0 = 0`; in the feasible zero-marginal case
we also have `c = 0` and `a = b`, so this formula still gives the correct value.
The feasibility guard excludes costly effort at zero marginal.

Define the loss `r = b-v`. Since `a <= v <= b`, we have `0 <= r <= d`.
The crucial bound, `loss_square_bound`, is

\[
r^2\le c(a+r).
\]

If `r <= c`, this follows from `a,r,c >= 0`. Otherwise `d >= r > c`, so
effort is feasible and `v >= (1-c/d)b`, implying `rd <= cb = c(a+d)`.
Together with `(d-r)(r-c) >= 0`, this proves the displayed bound.

## Averaging and the constant 9/8

For any finite prior, define

\[
A=\mathbb E[a],\qquad F=\mathbb E[v],\qquad
R=\mathbb E[r],\qquad L=F-A,\qquad D=L+R.
\]

Here `F` is the full-disclosure value, `F+R = E[b]`, and `D = E[b-a]`.
All of `A,L,R` are nonnegative. Nonnegativity of
`E[(r-E[r])²]` and the stateless loss inequality give

\[
R^2\le\mathbb E[r^2]\le c(A+R).
\]

For any no-disclosure contract that induces effort, let its share be
`alpha`. Incentive compatibility gives `c <= alpha*D`, and its utility is
`(1-alpha)(F+R)`. The checked polynomial identity is

\[
\begin{aligned}
&[9F-8(1-\alpha)(F+R)]D(A+R)\\
&\quad=A(L-R)^2+L(A-R)^2+R(A-L)^2\\
&\qquad\quad+8(F+R)[\alpha D(A+R)-R^2].
\end{aligned}
\]

Every term on the right is nonnegative. If `R > 0`, then `D(A+R) > 0`,
proving the 9/8 comparison. If `R = 0`, nonnegative shares already give
utility at most `F`. A no-effort contract gives utility at most `A <= F`.
This proves the no-disclosure comparison for every prior and every cost
`c >= 0`, with no positive-value assumption. The checked All-or-Nothing
lemma then transfers it to arbitrary measurable public signal kernels.

## Tightness and zero baseline

For `0 < c <= 1/4`, the two states have success pairs `(0,1)` and `(2c,4c)`
with probabilities `2c` and `1-2c`. The certificate proves the exact optima

\[
U^N=\frac{c(3-4c)^2}{2(1-c)},\qquad U^F=2c(2-3c),\qquad
\frac{U^N}{U^F}=\frac{(3-4c)^2}{4(1-c)(2-3c)}.
\]

The gap from `9/8` equals

\[
\frac98-\frac{U^N}{U^F}
=\frac{c(3-5c)}{8(1-c)(2-3c)}\in[0,c].
\]

Taking `c = 1/(n+4)` proves convergence of actual benchmark ratios and
provides a valid two-state counterexample to every factor below `9/8`.
The witnesses are actual one-signal public kernels.

When `a = 0` in every state, the exact value is `max(0,b-c)`. Averaging this
maximum dominates the maximum evaluated at the averages. All-or-Nothing
then proves full revelation is an attained joint optimum. Since every
single-agent binary reward function is supermodular, the previously checked
mixed-to-pure result transfers the entire theorem, tightness, and zero-baseline
optimality to mixed equilibria as well.
