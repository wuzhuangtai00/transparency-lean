# Lean formalization of *Transparency in Team Contracts*

Supplementary formal proofs for the manuscript **Transparency in Team
Contracts**, by **Paul Dütting, Yingkai Li, Inbal Talgam-Cohen, and Jinzhao Wu**
(2026). See [CITATION.bib](CITATION.bib) for the manuscript citation and
[PROVENANCE.md](PROVENANCE.md) for the exact reference snapshot and development
provenance.

Artifact version **0.7.1**. This package verifies formal versions of the main
information-theoretic results listed below. It does not certify every claim
or proof in the manuscript. Theorem numbering follows the reference snapshot;
[THEOREMS.md](THEOREMS.md) records stable LaTeX labels, exact Lean declarations,
assumptions, and exclusions.

## Results covered

| Manuscript result | Formalized guarantee |
| --- | --- |
| Lemma 3.1 | All-or-Nothing reduction, including arbitrary measurable public signal kernels. |
| Lemma 4.2, Theorem 4.1, Proposition 4.3 | Potential Lemma and sharp 4/3 bound for submodular rewards, with the additive tightness family. |
| Theorem 5.1 | Supermodular instance with zero full-disclosure value and strictly positive no-disclosure value. |
| Lemma A.1 and Theorem A.2 | Mixed-equilibrium reduction and sharp 4/3 bound; the supermodular separation also persists under mixing. |
| Theorem B.1 | Sharp single-agent 9/8 bound and zero-baseline optimality, for pure and mixed responses. |
| Theorem C.1 | Multi-action upper factor N and a lower family with ratio (N+1)/4 for N=2n-1 total actions, for linear contracts. |
| Finite-signal existence | Exact finite replacement and an attained joint optimum with at most $\lvert\Omega\rvert+2$ signals in the stated models. |

The formalization constructs Bayesian posteriors for general signal kernels
and proves existence of the benchmarks used in these comparisons. Shares,
probabilities, and costs are real valued; rationality and positive probability
of every state are not assumed.

## Verify the artifact

Prerequisites: Git, Bash, Python 3, and [elan / Lean](https://leanprover-community.github.io/get_started.html).
From the repository root, run:

```sh
lake exe cache get
bash scripts/check.sh
```

The toolchain is pinned to **Lean 4.19.0** in [lean-toolchain](lean-toolchain).
The mathlib revision is pinned to
`c44e0c8ee63ca166450922a373c7409c5d26b00b` (v4.19.0); retain
[lake-manifest.json](lake-manifest.json) to reproduce the transitive dependency
versions. The initial dependency download requires internet access.

The check script builds the package, runs Lean with `--trust=0` on
[Certificate.lean](TransparencyLean/Certificate.lean), and audits the transitive
axiom dependencies of its 162 listed declarations. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted. It also scans the project
Lean sources for proof placeholders and specified proof escape mechanisms.
Successful execution ends with:

```text
PASS: 162 public declarations audited; only standard Lean axioms; no proof placeholders.
```

Logs are written to [validation/](validation/). The script exits unsuccessfully
if the build, kernel check, or audit fails. The committed logs record local
verification; [checkpoint.json](validation/checkpoint.json) includes hashes of
all Lean sources. A [GitHub Actions workflow](.github/workflows/verify.yml) runs
the same script from a fresh checkout. A hosted CI run must be confirmed after
the repository is created; the included workflow is not itself evidence of a
successful GitHub run.

## Scope and interpretation

- Binary-action teams use the paper's pure or independent mixed equilibrium
  models, with principal-favorable selection. The multi-action extension has
  one agent and linear contracts.
- Public signal spaces may be arbitrary measurable spaces. Feasibility and
  equilibrium hold almost everywhere, and selected payoffs must be measurable.
- Finite states do **not** imply that every signal space is finite. The checked
  claim is existence of a finite optimal scheme under the formalized model's
  assumptions. The support bound of $\lvert\Omega\rvert+2$ is not asserted sharp.
- The 9/8 upper bound uses the alternative moment proof documented in
  [SINGLE_AGENT_PROOF.md](SINGLE_AGENT_PROOF.md). The manuscript's intermediate
  cutoff, concavity, two-state reduction, and derivative lemmas are not
  independently certified. The multi-action welfare bound is proved inside
  Lean; see [MULTI_ACTION_PROOF.md](MULTI_ACTION_PROOF.md).
- The computational theorem, running-time bounds, and numerical-precision
  guarantees are outside this artifact's scope.

Lean checks the formal statements and their proofs. Whether those statements
faithfully capture the intended manuscript claims remains a mathematical
review task. The theorem map makes that correspondence explicit; the audit
logs do not substitute for reviewing it.

## Reading and citing

Start with [THEOREMS.md](THEOREMS.md), then follow its declarations into the
Lean files. [ARCHITECTURE.md](ARCHITECTURE.md) explains the model and dependency
structure. [PROVENANCE.md](PROVENANCE.md) records AI assistance and local
verification details.

For the mathematical results, cite the manuscript using
[CITATION.bib](CITATION.bib). For a reproducibility claim, also identify the
exact artifact release or Git commit used. This repository is supplementary
material; it does not replace the manuscript's mathematical exposition.
