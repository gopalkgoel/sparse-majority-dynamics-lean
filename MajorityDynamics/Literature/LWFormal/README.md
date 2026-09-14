# Supplied Liebenau–Wormald formalization

This directory contains the 48 Lean source modules from the user-supplied
`LWFormal_checkpoint4(1).zip`. The original mathematical namespace is `LW`.
`source-manifest.json` records the archive digest and original/integrated module hashes.

The integration changes import paths to `MajorityDynamics.Literature.LWFormal.*`
and restores the source project's `autoImplicit = true` locally in each module.
The repository's Lean 4.33.0 and Mathlib pins are unchanged; the supplied project
used 4.33.1. Nine small lint compatibility edits remove redundant tactics/simp
arguments or prefix unused binders with `_`. Warnings remain errors. No theorem
statement, mathematical definition, proof argument, axiom or compiler is changed.

| Source result | Closed declaration |
| --- | --- |
| Graph degree enumeration, Theorem 1.4 | `LW.theorem_1_4` |
| Corrected graph-edge expansion on the full degree domain | `LW.theorem_1_6` |
| Printed graph-edge formula on the narrower Theorem 6.3 domain | `LW.theorem_1_6'` |
| Bipartite degree enumeration, Theorem 1.1 | `LW.Bip.theorem_1_1` |
| Bipartite edge probability, Theorem 1.5 | `LW.Bip.theorem_1_5` |

Every listed endpoint is a closed proof using only `propext`, `Classical.choice`
and `Quot.sound`. The source `Sanity.lean` files are retained but not imported by
the literature endpoints. The source project wrapper, build caches, Git history,
PDFs and exploratory Python scripts are not part of the proof dependency closure.

`../LWAdapters/` identifies the actual finite probability laws, relabels arbitrary
finite carriers, converts the two forms of growth assumptions, and connects the
source proofs to the repository's four public literature endpoints.
