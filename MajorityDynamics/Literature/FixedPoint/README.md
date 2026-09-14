# Attributed Brouwer proof

This directory contains a source port of **harfe's existing Lean proof** of
Brouwer's fixed-point theorem. It is literature formalization for completeness,
separate from the original majority-dynamics argument.

## Source and citation

- Author: **harfe**; copyright (c) 2026 harfe.
- Repository: [fixed-point-theorems-lean4](https://github.com/harfe/fixed-point-theorems-lean4).
- Exact source revision: [`770940ddf9878cf61952ed53d910b92bca841838`](https://github.com/harfe/fixed-point-theorems-lean4/tree/770940ddf9878cf61952ed53d910b92bca841838).
- License: **MIT**, retained in full in [LICENSE](LICENSE).
- Mathematical reference used by the paper: Allen Hatcher, *Algebraic Topology*
  (2002), Corollary 2.15, printed p. 114
  ([book](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf#page=123)).

When presenting or reusing this formal proof, cite both the mathematical result
and harfe's Lean formalization at the revision above. The formal proof uses
cubical Sperner's lemma and compact-convex domain transport; it is not a port of
Hatcher's homology proof. The closed-ball adapter in
[Goals/Brouwer/Main.lean](../Goals/Brouwer/Main.lean) is local integration work.

## Imported proof closure

All source links below are pinned to the same revision.

| Local file | Original file | Role |
| --- | --- | --- |
| [CubicalSpernerPrep.lean](CubicalSpernerPrep.lean) | [cubical_sperner_prep.lean](https://github.com/harfe/fixed-point-theorems-lean4/blob/770940ddf9878cf61952ed53d910b92bca841838/FixedPointTheorems/cubical_sperner_prep.lean) | Finite cubical triangulation and face counts |
| [CubicalSperner.lean](CubicalSperner.lean) | [cubical_sperner.lean](https://github.com/harfe/fixed-point-theorems-lean4/blob/770940ddf9878cf61952ed53d910b92bca841838/FixedPointTheorems/cubical_sperner.lean) | Cubical Sperner parity argument |
| [ApplyCubicalSperner.lean](ApplyCubicalSperner.lean) | [apply_cubical_sperner.lean](https://github.com/harfe/fixed-point-theorems-lean4/blob/770940ddf9878cf61952ed53d910b92bca841838/FixedPointTheorems/apply_cubical_sperner.lean) | Fixed point on the unit cube |
| [ConvexHomeos.lean](ConvexHomeos.lean) | [convex_homeos.lean](https://github.com/harfe/fixed-point-theorems-lean4/blob/770940ddf9878cf61952ed53d910b92bca841838/FixedPointTheorems/convex_homeos.lean) | Transport from compact convex subsets |
| [Brouwer.lean](Brouwer.lean) | [brouwer.lean](https://github.com/harfe/fixed-point-theorems-lean4/blob/770940ddf9878cf61952ed53d910b92bca841838/FixedPointTheorems/brouwer.lean) | General compact-convex fixed-point theorem |

Only these five upstream modules are included. Their imports stay inside this
subtree and Mathlib. Each file retains its source attribution header.

## Port record

Upstream pins Lean/Mathlib **4.32.0** at this revision. This repository retains
Lean **4.33.0** and Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`, with `autoImplicit=false` and warnings
as errors. The source is recompiled against these pins; no upstream compiled
objects are imported.

The port relocates the five imports and wraps their declarations in
`MajorityDynamics.Literature.FixedPoint`. Compatibility edits are limited to:

- Marking the classical finite-count definitions `coord_change_count` and
  `ccc_fun` as `noncomputable`, as required by the newer compiler.
- Updating deprecated set-predicate lemma names and replacing a proof-only
  `haveI` with `have` to satisfy the current lint settings.
- Replacing the occurrence-number rewrite in `ccc_fun_case_D_iff` with the
  direct equivalence between full cardinality and membership of every index.
- Making the child-cube dimension explicit in the Sperner induction, adding
  its local classical instance, and adapting the finite-set membership proof
  to the current simplifier. These changes retain the original induction and
  cardinality bijection.

The public source theorem is
`MajorityDynamics.Literature.FixedPoint.brouwer_fixed_point`; the paper continues
to consume `MajorityDynamics.Literature.brouwer_closedBall` with its unchanged
closed contract. The adapter creates a continuous map of the closed-ball subtype
from `ContinuousOn` and `MapsTo`, then projects the fixed point back to Euclidean
space. Compactness, convexity and nonemptiness also hold in dimension zero.

Completion is checked by the existing `LiteratureGoals` transitive axiom audit,
which requires L05 to have only `propext`, `Classical.choice`, and `Quot.sound`.
The source revision's [successful upstream check](https://github.com/harfe/fixed-point-theorems-lean4/actions/runs/30372352086/job/90319206465)
records provenance; the local port and its consumers are checked independently.
