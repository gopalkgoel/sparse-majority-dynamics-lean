import MajorityDynamics.Probability.NeighborhoodBulk.FiniteChecks
import MajorityDynamics.Probability.NeighborhoodBulk.CorrectionBounds
import MajorityDynamics.Probability.NeighborhoodBulk.Relabel
import MajorityDynamics.Probability.NeighborhoodBulk.SparseEnumeration
import MajorityDynamics.Probability.NeighborhoodBulk.BipartiteSparse
import MajorityDynamics.Probability.NeighborhoodBulk.ResidualCorrections
import MajorityDynamics.Probability.NeighborhoodBulk.WeightBridges

/-! Audits of uniform source applications, original and residual correction bounds,
and the literal neighborhood weights. Imported by the closed C.4 `Checks` target. -/

/--
info: 'MajorityDynamics.Literature.DegreeEnumeration.graphFamily_nonempty_of_enumeration' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Literature.DegreeEnumeration.graphFamily_nonempty_of_enumeration

/--
info: 'MajorityDynamics.Literature.DegreeEnumeration.bipartiteFamily_nonempty_of_enumeration' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Literature.DegreeEnumeration.bipartiteFamily_nonempty_of_enumeration

/--
info: 'MajorityDynamics.Probability.NeighborhoodBulk.eventually_graph_source_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodBulk.eventually_graph_source_data

/--
info: 'MajorityDynamics.Probability.NeighborhoodBulk.eventually_bipartite_source_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodBulk.eventually_bipartite_source_data

/--
info: 'MajorityDynamics.Probability.NeighborhoodBulk.eventually_graph_correction_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodBulk.eventually_graph_correction_bounds

/--
info: 'MajorityDynamics.Probability.NeighborhoodBulk.eventually_bipartite_correction_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodBulk.eventually_bipartite_correction_bounds

/--
info: 'MajorityDynamics.Probability.NeighborhoodBulk.fixedDegreeLaw_relabel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodBulk.fixedDegreeLaw_relabel

/--
info: 'MajorityDynamics.Probability.NeighborhoodBulk.bipartiteFixedDegreeLaw_relabel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodBulk.bipartiteFixedDegreeLaw_relabel

/--
info: 'MajorityDynamics.Literature.DegreeEnumeration.uniform_relativeApproximation_of_sequences' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Literature.DegreeEnumeration.uniform_relativeApproximation_of_sequences

/--
info: 'MajorityDynamics.Literature.DegreeEnumeration.graph_enumeration_uniform_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Literature.DegreeEnumeration.graph_enumeration_uniform_finite

/--
info: 'MajorityDynamics.Literature.DegreeEnumeration.bipartite_enumeration_uniform_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Literature.DegreeEnumeration.bipartite_enumeration_uniform_finite

/--
info: 'MajorityDynamics.Probability.NeighborhoodBulk.eventually_graph_input_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.NeighborhoodBulk.eventually_graph_input_nonempty

/--
info: 'MajorityDynamics.Probability.NeighborhoodBulk.eventually_bipartite_input_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.NeighborhoodBulk.eventually_bipartite_input_nonempty

/--
info: 'MajorityDynamics.Probability.NeighborhoodBulk.graph_enumeration_sparse' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.NeighborhoodBulk.graph_enumeration_sparse

/--
info: 'MajorityDynamics.Probability.NeighborhoodBulk.bipartite_enumeration_sparse' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.NeighborhoodBulk.bipartite_enumeration_sparse

/--
info: 'MajorityDynamics.Probability.NeighborhoodBulk.eventually_graph_residual_enumeration' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.NeighborhoodBulk.eventually_graph_residual_enumeration

/--
info: 'MajorityDynamics.Probability.NeighborhoodBulk.eventually_bipartite_residual_enumeration' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.NeighborhoodBulk.eventually_bipartite_residual_enumeration

/--
info: 'MajorityDynamics.Probability.NeighborhoodBulk.eventually_graph_residual_correction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodBulk.eventually_graph_residual_correction

/--
info: 'MajorityDynamics.Probability.NeighborhoodBulk.eventually_bipartite_residual_correction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodBulk.eventually_bipartite_residual_correction

/--
info: 'MajorityDynamics.Probability.NeighborhoodBulk.eventually_graph_profile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodBulk.eventually_graph_profile

/--
info: 'MajorityDynamics.Probability.NeighborhoodBulk.eventually_bipartite_profile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Probability.NeighborhoodBulk.eventually_bipartite_profile
