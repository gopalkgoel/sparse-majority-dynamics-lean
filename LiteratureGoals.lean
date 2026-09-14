import MajorityDynamics.Literature.Goals.FKMMajority.Main
import MajorityDynamics.Literature.GoalAudit
import MajorityDynamics.Literature.Goals.BernoulliLowerTail.Main
import MajorityDynamics.Literature.Goals.BinomialChernoff.Main
import MajorityDynamics.Literature.Goals.ErdosGallai.Main
import MajorityDynamics.Literature.Goals.GaleRyser.Main
import MajorityDynamics.Literature.Goals.Brouwer.Main
import MajorityDynamics.Literature.Goals.RandomGraphJumbledness.Main
import MajorityDynamics.Literature.Goals.GraphEnumeration.Main
import MajorityDynamics.Literature.Goals.BipartiteEnumeration.Main
import MajorityDynamics.Literature.Goals.GraphEdgeProbability.Main
import MajorityDynamics.Literature.Goals.BipartiteEdgeProbability.Main

/-! The eleven literature goals. Build this target independently of all paper proof
modules. Defining a contract or importing an axiom does not complete a goal. -/
namespace MajorityDynamics.Literature
open GoalAudit

def goals : Array Goal := #[
  { id := "L01", title := "Bernoulli subset lower tail",
    declaration := ``MajorityDynamics.Literature.bernoulli_lower_tail,
    contract := ``MajorityDynamics.Literature.BernoulliLowerTail, wave := "active" },
  { id := "L02", title := "Scalar binomial Chernoff bounds",
    declaration := ``MajorityDynamics.Literature.binomial_chernoff,
    contract := ``MajorityDynamics.Literature.BinomialChernoff, wave := "active" },
  { id := "L03", title := "Erdős–Gallai criterion",
    declaration := ``MajorityDynamics.Combinatorics.SufficientGraphicality.erdos_gallai,
    contract := ``MajorityDynamics.Combinatorics.SufficientGraphicality.ErdosGallaiCriterion, wave := "active" },
  { id := "L04", title := "Gale–Ryser criterion",
    declaration := ``MajorityDynamics.Combinatorics.SufficientGraphicality.gale_ryser,
    contract := ``MajorityDynamics.Combinatorics.SufficientGraphicality.GaleRyserCriterion, wave := "active" },
  { id := "L05", title := "Brouwer fixed point on a closed ball",
    declaration := ``MajorityDynamics.Literature.brouwer_closedBall,
    contract := ``MajorityDynamics.Literature.BrouwerClosedBall, wave := "active" },
  { id := "L06", title := "Random-graph jumbledness",
    declaration := ``MajorityDynamics.Literature.random_graph_jumbledness,
    contract := ``MajorityDynamics.Literature.RandomGraphJumbledness, wave := "active" },
  { id := "L07", title := "Liebenau–Wormald graph enumeration",
    declaration := ``MajorityDynamics.Literature.DegreeEnumeration.liebenau_wormald_graph,
    contract := ``MajorityDynamics.Literature.DegreeEnumeration.GraphEnumerationTheorem, wave := "complete" },
  { id := "L08", title := "Liebenau–Wormald bipartite enumeration",
    declaration := ``MajorityDynamics.Literature.DegreeEnumeration.liebenau_wormald_bipartite,
    contract := ``MajorityDynamics.Literature.DegreeEnumeration.BipartiteEnumerationTheorem, wave := "complete" },
  { id := "L09", title := "Liebenau–Wormald graph edge probability",
    declaration := ``MajorityDynamics.Literature.EdgeProbabilities.graph_edge_probability,
    contract := ``MajorityDynamics.Literature.EdgeProbabilities.GraphEdgeProbabilityTheorem, wave := "complete" },
  { id := "L10", title := "Liebenau–Wormald bipartite edge probability",
    declaration := ``MajorityDynamics.Literature.EdgeProbabilities.bipartite_edge_probability,
    contract := ``MajorityDynamics.Literature.EdgeProbabilities.BipartiteEdgeProbabilityTheorem, wave := "complete" },
  { id := "L11", title := "Fountoulakis–Kang–Makai dense majority dynamics",
    declaration := ``MajorityDynamics.Literature.fkm_majority,
    contract := ``MajorityDynamics.Literature.FKMMajorityTheorem, wave := "complete" }
]

run_cmd do
  unless goals.size == 11 do
    throwError "The literature inventory must contain exactly eleven goals"
  GoalAudit.audit goals

end MajorityDynamics.Literature
