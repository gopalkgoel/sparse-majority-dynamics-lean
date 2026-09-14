import MajorityDynamics.Literature.DegreeEnumeration.Statements

/-!
External input: Anita Liebenau and Nick Wormald, *Asymptotic enumeration of
graphs by degree sequence, and the degree sequence of a random graph*,
arXiv:1702.08373v3 (26 August 2019), Theorem 1.4, page 5.
https://arxiv.org/pdf/1702.08373v3

`GraphEnumerationTheorem` uses n as the sequence index and m(n) as the edge
total. Its eventual quantifier precedes every degree vector. The real-exponent
little-o assumptions preserve the source's "for all fixed K > 0" requirement.
The concrete laws and their atom formulas are constructed without this axiom.
No application to original/residual degree data is included in this import.
-/
namespace MajorityDynamics.Literature.DegreeEnumeration

-- Exact declarative goal: `GraphEnumerationTheorem` in DegreeEnumeration/Statements.lean.
-- Its definition and all law/normalization definitions are shared source infrastructure.

end MajorityDynamics.Literature.DegreeEnumeration
