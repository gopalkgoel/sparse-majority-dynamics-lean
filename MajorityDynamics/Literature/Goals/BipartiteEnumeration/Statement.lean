import MajorityDynamics.Literature.DegreeEnumeration.Statements

/-!
External input: *Asymptotic enumeration of digraphs and bipartite graphs by
degree sequence*, arXiv:2006.15797v1 (29 June 2020), Theorem 1.1, page 3,
bipartite case (the source's digraph indicator is zero).
https://arxiv.org/pdf/2006.15797v1

`BipartiteEnumerationTheorem` uses sequences ell(n), m(n), retaining both
little-o assumptions, the actual side averages, variance-product correction,
and three-term relative-error envelope. The eventual quantifier precedes both
degree vectors. The laws are the independently sampled binomials conditioned
on both totals, and the degrees of a uniform labeled cross-edge set.
No sparse-window or residual applicability claim is included in this import.
-/
namespace MajorityDynamics.Literature.DegreeEnumeration

-- Exact declarative goal: `BipartiteEnumerationTheorem` in DegreeEnumeration/Statements.lean.
-- Its definition and all law/normalization definitions are shared source infrastructure.

end MajorityDynamics.Literature.DegreeEnumeration
