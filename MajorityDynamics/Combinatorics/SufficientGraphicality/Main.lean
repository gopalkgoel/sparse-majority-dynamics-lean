import MajorityDynamics.Combinatorics.SufficientGraphicality.Imports
import MajorityDynamics.Combinatorics.SufficientGraphicality.Integer

/-! Closed endpoints for all of A.8/A.9, modulo precisely the two named criteria. -/
namespace MajorityDynamics.Combinatorics.SufficientGraphicality

theorem graphical_sufficient : GraphicalSufficientTheorem :=
  graphical_sufficient_of_erdos_gallai erdos_gallai

theorem bipartite_graphical_sufficient : BipartiteGraphicalSufficientTheorem :=
  bipartite_graphical_sufficient_of_gale_ryser gale_ryser

theorem graphical_sufficient_integer : IntegerGraphicalSufficientTheorem :=
  graphical_integer_of_natural graphical_sufficient

theorem bipartite_graphical_sufficient_integer : IntegerBipartiteGraphicalSufficientTheorem :=
  bipartite_integer_of_natural bipartite_graphical_sufficient

end MajorityDynamics.Combinatorics.SufficientGraphicality
