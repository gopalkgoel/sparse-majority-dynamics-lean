import MajorityDynamics.Literature.Goals.GraphEdgeProbability.Statement
import MajorityDynamics.Literature.LWAdapters.GraphEdge

/-! Checked Liebenau–Wormald edge estimate on the actual fixed-degree law. -/
namespace MajorityDynamics.Literature.EdgeProbabilities

theorem graph_edge_probability : GraphEdgeProbabilityTheorem := LWAdapters.graph_edge_probability

end MajorityDynamics.Literature.EdgeProbabilities
