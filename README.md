# Majority dynamics on sparse random graphs, in Lean 4

A complete, machine-checked formalization of the main theorems of

> Gopal Goel and Ashwin Sah, *Majority Dynamics on sparse random graphs*.

Every theorem below is a closed Lean proof whose transitive axioms are exactly
Lean's standard foundations: `propext`, `Classical.choice`, `Quot.sound`. There
are no `sorry`s and no project axioms.

## The theorems

Majority dynamics: each vertex of a graph holds an opinion in `{+1, -1}`; every
day, every vertex simultaneously adopts the strict majority opinion of its
neighbours, keeping its own opinion on a tie. The graph is `G(N, p)`; the
initial opinions are an arbitrary fixed coloring in which exactly
`N/2 + ⌊τ√N⌋` vertices hold `+1`.

| Statement | Lean declaration | Gate |
| --- | --- | --- |
| Sparse range `T⁻¹N^{-θ} < p < TN^{-θ}`, `1/2 < θ < 1`: with probability at least `1 - ε`, every vertex holds `+1` on day `2⌊1/(1-θ)⌋ + 3` | `MajorityDynamics.Paper.main : MainTheorem` ([`Paper/Problem.lean`](MajorityDynamics/Paper/Problem.lean), [`Paper/Main.lean`](MajorityDynamics/Paper/Main.lean)) | `PaperCompletion.lean` |
| Full uniform range `T⁻¹N^{-θ} ≤ p ≤ 1`, same day, same bound | `MajorityDynamics.Paper.uniform_main : UniformMainTheorem` ([`Paper/UniformProblem.lean`](MajorityDynamics/Paper/UniformProblem.lean), [`Paper/UniformMain.lean`](MajorityDynamics/Paper/UniformMain.lean)) | `UniformCompletion.lean` |
| Uniformly random initial opinions | `MajorityDynamics.Paper.random_opinions : RandomOpinionsTheorem` ([`Paper/Final/Main.lean`](MajorityDynamics/Paper/Final/Main.lean)) | `Paper/Final/Checks.lean` (default build) |

The probability bound is uniform over the density `p`, the bias parameter `τ`,
and the initial coloring `c`: the threshold `N₀` depends only on `(θ, T, ε)`.
The statements are made on the canonical vertex set `Fin N` with Mathlib's
`SimpleGraph.binomialRandom` graph law; `Paper/Problem.lean` is the file to
read to check that the formal statement is the intended one.

Eleven results from the literature are also proved from foundations rather
than assumed. They are listed with their contracts in
[`LiteratureGoals.lean`](LiteratureGoals.lean) and checked by
`LiteratureCompletion.lean`: Bernoulli and binomial tail bounds, the
Erdős–Gallai and Gale–Ryser criteria, Brouwer's fixed-point theorem on a
closed ball, random-graph jumbledness, the Liebenau–Wormald degree-sequence
enumeration and edge-probability theorems (graph and bipartite), and the
Fountoulakis–Kang–Makai theorem on dense majority dynamics. The literature
tree imports nothing from the paper's own proof; `scripts/check_literature_boundary.py`
enforces this.

## Building and checking

Requires [elan](https://github.com/leanprover/elan). The toolchain
(`lean-toolchain`, Lean `v4.33.0`) and every dependency (`lake-manifest.json`,
Mathlib `db584cd6`) are pinned.

```sh
lake exe cache get                     # Mathlib's precompiled cache
lake build --wfail                     # all default targets; warnings are errors
lake env lean PaperCompletion.lean     # sparse-range main theorem
lake env lean UniformCompletion.lean   # full uniform theorem, including p = 1
lake build --wfail LiteratureGoals
lake env lean LiteratureCompletion.lean  # all eleven literature goals
```

Each completion file compiles silently and exits `0` exactly when its theorem
has the exact expected type and `#print axioms` reports only the three
standard foundational axioms. `AxiomCheck.lean`, `PaperAxiomAudit.lean`, and
`UniformProofChecks.lean` guard the same property for the intermediate
endpoints and are part of the default build. `autoImplicit` is off and
`warningAsError` is on for the whole project (`lakefile.toml`).

The same commands run in CI (`.github/workflows/lean.yml`). A cold build takes
roughly 75 minutes on a standard GitHub runner; incremental builds recompile
only invalidated modules.

## Layout

| Path | Contents |
| --- | --- |
| `MajorityDynamics/Paper/` | The theorem statements (`Problem.lean`, `UniformProblem.lean`), the top-level proofs, and their assembly from the parts below. |
| `MajorityDynamics/GraphProcess/` | The fine and coarse state spaces of the graph process, the universal transition kernel, fiber transference, the local one-day theorem, and the faithful-trajectory induction. |
| `MajorityDynamics/Idealized/` | The idealized (deterministic) evolution, its perturbation theory, and the critical-day analysis. |
| `MajorityDynamics/Universal/` | The Gaussian universal recursion of the paper's Section 4. |
| `MajorityDynamics/Analysis/`, `Probability/`, `Combinatorics/`, `Binomial/`, `Local/` | Supporting analysis, probability, and combinatorics. |
| `MajorityDynamics/Literature/` | The eleven literature results and their adapters; see [`THIRD_PARTY.md`](THIRD_PARTY.md) for the two vendored formalizations and the ported Brouwer proof. |
| `LiteratureGoals.lean`, `*Completion.lean`, `*Check*.lean`, `PaperAxiomAudit.lean` | Statement-and-axiom gates. |
| `scripts/` | The literature import-boundary check, the CI report generator, and their tests. |

Module docstrings cite the paper by its LaTeX labels (for example
`thm:local-coarse-transition`, `lem:nice_deg`) and refer to its source file as
`latest/main.tex`.
