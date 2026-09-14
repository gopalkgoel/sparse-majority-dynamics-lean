import MajorityDynamics.Literature.Goals.ErdosGallai.Statement
import MajorityDynamics.Literature.Graphicality.ErdosGallai

/-! L03 — Erdős–Gallai criterion.
The exact existing contract is proved via the constructive subrealization proof
of Tripathi, Venugopalan and West, Discrete Mathematics 310 (2010), 843–844,
Theorem 1; author preprint https://dwest.web.illinois.edu/pubs/tripathi.pdf.
All finite graph constructions and counting steps are checked under Graphicality.
-/
namespace MajorityDynamics.Combinatorics.SufficientGraphicality

theorem erdos_gallai : ErdosGallaiCriterion := by
  intro n _ d hsort heven hineq
  exact ErdosGallai.sufficient n d hsort heven hineq

/-- info: 'MajorityDynamics.Combinatorics.SufficientGraphicality.erdos_gallai' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms erdos_gallai

end MajorityDynamics.Combinatorics.SufficientGraphicality
