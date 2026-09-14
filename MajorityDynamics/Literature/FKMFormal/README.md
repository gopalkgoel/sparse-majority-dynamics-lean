# Supplied Fountoulakis–Kang–Makai formalization

Source: user-supplied `MajorityDyn-Theorem11.zip`; exact archive and module SHA256
hashes are recorded in `source-manifest.json`. The ten Lean source modules retain
the original `MD` namespace. Git history, compiled products and the included paper
PDF are not vendored.

Citation: Nikolaos Fountoulakis, Mihyun Kang and Tamás Makai,
*Resolution of a conjecture on majority dynamics: rapid stabilisation in dense
random graphs*, [arXiv:1910.05820v2](https://arxiv.org/abs/1910.05820v2), Theorem 1.1.
`MD.theorem_1_1 : MD.Theorem11` proves the random-graph/random-initial-opinions
statement uniformly for λ/√n ≤ p ≤ 1. Initial ties count as failure.

Integration preserves the repository's Lean 4.33.0 and Mathlib pins. Imports are
relocated; the broad `Mathlib` import is replaced with explicit dependency roots
to reuse the existing upstream cache. Source `autoImplicit = true` is restored
locally. The unused-section-variable style linter is disabled locally to preserve
the supplied theorem types; warning-as-error, kernel checking and axiom audits
remain enabled. Three compatibility edits rename unused binders or remove a
redundant `push_cast`. No mathematical definition or theorem statement changes.

`../FKMAdapters/FixedInitial.lean` derives the fixed-coloring dense bound directly
from `Pr_many_false_le`, `final_rounds`, `Pr_not_P1_le` and `Pr_not_P2_le`.
This is a consequence of the formalized proof, not an assertion that the random
initial-opinions theorem directly quantifies over deterministic colorings.
`../FKMAdapters/GraphLaw.lean` identifies the finite Bernoulli weights with
Mathlib's actual Erdős–Rényi law, without dividing by p or 1-p.
