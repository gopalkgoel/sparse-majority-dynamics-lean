# Third-party and vendored Lean sources

Three subtrees under `MajorityDynamics/Literature/` were not written as part of
this project's own proof. They are recompiled here against this project's pinned
Lean `v4.33.0` and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`; no
compiled objects are imported from elsewhere. Each subtree's README records the
exact provenance and the compatibility edits that were made, none of which
changes a theorem statement, definition, proof argument, or axiom.

| Subtree | Content | Provenance | Notes |
| --- | --- | --- | --- |
| [`FixedPoint/`](MajorityDynamics/Literature/FixedPoint/README.md) | Brouwer's fixed-point theorem for compact convex sets, via cubical Sperner (namespace `MajorityDynamics.Literature.FixedPoint`). | harfe, [fixed-point-theorems-lean4](https://github.com/harfe/fixed-point-theorems-lean4), revision `770940ddf9878cf61952ed53d910b92bca841838`. | MIT licence, retained in full in [`FixedPoint/LICENSE`](MajorityDynamics/Literature/FixedPoint/LICENSE). Five modules ported; source attribution headers retained. |
| [`LWFormal/`](MajorityDynamics/Literature/LWFormal/README.md) | Liebenau–Wormald degree-sequence enumeration and edge-probability theorems for graphs and bipartite graphs (namespace `LW`). | Supplied Lean project; archive and per-module SHA-256 digests in [`LWFormal/source-manifest.json`](MajorityDynamics/Literature/LWFormal/source-manifest.json). | `LW.theorem_1_6` states a corrected form of the printed graph-edge expansion; `LW.theorem_1_6'` is the printed formula on its narrower domain. |
| [`FKMFormal/`](MajorityDynamics/Literature/FKMFormal/README.md) | Fountoulakis–Kang–Makai, *Resolution of a conjecture on majority dynamics: rapid stabilisation in dense random graphs*, [arXiv:1910.05820](https://arxiv.org/abs/1910.05820), Theorem 1.1 (namespace `MD`). | Supplied Lean project; archive and per-module SHA-256 digests in [`FKMFormal/source-manifest.json`](MajorityDynamics/Literature/FKMFormal/source-manifest.json). | Used only for the dense end of the uniform theorem, through the adapters in `FKMAdapters/`. |

Everything else in this repository depends on [Mathlib](https://github.com/leanprover-community/mathlib4)
(Apache 2.0) and the Lean 4 core library (Apache 2.0), at the revisions pinned
in `lake-manifest.json` and `lean-toolchain`.
