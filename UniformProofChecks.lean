import MajorityDynamics.Binomial.GaussianComparisonNoBalance
import MajorityDynamics.Binomial.GaussianComparisonSparse
import MajorityDynamics.Binomial.TiltedExpansionSparse
import MajorityDynamics.Binomial.SparseLogBudget
import MajorityDynamics.Idealized.LinearResponse.UniformBudget
import MajorityDynamics.Idealized.CriticalDay.TemplateGainUnbounded
import MajorityDynamics.Idealized.CriticalDay.GaussianGainPolynomial
import MajorityDynamics.Idealized.CriticalDay.TemplateGainLinear
import MajorityDynamics.Idealized.CriticalDay.UniformStopping
import MajorityDynamics.Idealized.CriticalDay.StoppingBudgets
import MajorityDynamics.Idealized.CriticalDay.FiniteCenteredTarget
import MajorityDynamics.Idealized.RowLimits.RowsSparse
import MajorityDynamics.Idealized.RowLimits.MassSparseUnbounded
import MajorityDynamics.Analysis.GaussianRegularity.UniformEvents
import MajorityDynamics.Analysis.GaussianRegularity.UniformThresholds
import MajorityDynamics.Probability.NeighborhoodBulk.BipartiteBandEnumeration
import MajorityDynamics.GraphProcess.EnumerationComparison.BandMain
import MajorityDynamics.GraphProcess.FiberTransference.SparseDenominator
import MajorityDynamics.GraphProcess.RowGamma.Sparse
import MajorityDynamics.GraphProcess.LocalTheorem.SparseTerminalSizes
import MajorityDynamics.Probability.NeighborhoodBulk.SparseMain
import MajorityDynamics.GraphProcess.KernelSplitting.SparseRegularity
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.SparseMain
import MajorityDynamics.GraphProcess.LocalTheorem.SparseMain
import MajorityDynamics.Idealized.Process.SparseMain
import MajorityDynamics.Idealized.CriticalDay.FlexibleScales
import MajorityDynamics.Idealized.LinearResponse.SparseMain
import MajorityDynamics.Idealized.CriticalDay.HistorySparseChecks
import SparseEvolutionChecks
import SparseTerminalChecks
import SparseTerminalBudgetChecks
import SparseStoppedChecks
import UniformCompletion
import MajorityDynamics.Paper.UniformAssembly
import MajorityDynamics.GraphProcess.LocalTheorem.TerminalSizes
import MajorityDynamics.GraphProcess.FaithfulTrajectory.TerminalCriticalGain

/-! Ingredient audits and the strict completion gate for the separate
uniform-density theorem. Existing paper completion policies are unchanged. -/

/-- info: 'MajorityDynamics.Binomial.Approximation.gaussian_comparison_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Binomial.Approximation.gaussian_comparison_sparse

/-- info: 'MajorityDynamics.Binomial.Approximation.tilted_expansion_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Binomial.Approximation.tilted_expansion_sparse

/-- info: 'MajorityDynamics.Idealized.CriticalDay.gaussian_gain_linear_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.CriticalDay.gaussian_gain_linear_stable

/-- info: 'MajorityDynamics.Idealized.CriticalDay.template_gain_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.CriticalDay.template_gain_linear

/-- info: 'MajorityDynamics.Idealized.CriticalDay.first_geometric_crossing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.CriticalDay.first_geometric_crossing

/-- info: 'MajorityDynamics.Idealized.CriticalDay.stopping_window_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.CriticalDay.stopping_window_error

/-- info: 'MajorityDynamics.GraphProcess.LocalTheorem.terminal_size_transition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.LocalTheorem.terminal_size_transition

/-- info: 'MajorityDynamics.Idealized.RowLimits.row_normalized_comparison_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.RowLimits.row_normalized_comparison_sparse

/-- info: 'MajorityDynamics.Analysis.GaussianRegularity.gaussian_mass_uniform_events' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Analysis.GaussianRegularity.gaussian_mass_uniform_events

/-- info: 'MajorityDynamics.Probability.NeighborhoodBulk.graph_enumeration_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.NeighborhoodBulk.graph_enumeration_band

/-- info: 'MajorityDynamics.Probability.NeighborhoodBulk.bipartite_enumeration_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.NeighborhoodBulk.bipartite_enumeration_band

/-- info: 'MajorityDynamics.GraphProcess.EnumerationComparison.uniform_band_strong_comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.EnumerationComparison.uniform_band_strong_comparison

/-- info: 'MajorityDynamics.Idealized.CriticalDay.uniform_stopping_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.CriticalDay.uniform_stopping_index

/-- info: 'MajorityDynamics.Idealized.CriticalDay.uniform_terminal_error_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.CriticalDay.uniform_terminal_error_budget

/-- info: 'MajorityDynamics.Analysis.GaussianRegularity.gaussian_mass_unbounded_threshold_parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Analysis.GaussianRegularity.gaussian_mass_unbounded_threshold_parameters

/-- info: 'MajorityDynamics.Idealized.CriticalDay.faithful_target_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.CriticalDay.faithful_target_budget

/-- info: 'MajorityDynamics.Idealized.CriticalDay.centered_target_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.CriticalDay.centered_target_budget

/-- info: 'MajorityDynamics.Idealized.RowLimits.row_split_sparse_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.RowLimits.row_split_sparse_unbounded

/-- info: 'MajorityDynamics.Paper.uniform_cleanup_at_stopping_day' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Paper.uniform_cleanup_at_stopping_day

/-- info: 'MajorityDynamics.Paper.pseudorandomness_lower_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Paper.pseudorandomness_lower_only

/-- info: 'MajorityDynamics.Paper.uniform_main_of_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Paper.uniform_main_of_expansion

/-- info: 'MajorityDynamics.GraphProcess.FiberTransference.uniform_denominator_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.FiberTransference.uniform_denominator_sparse

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialLocalCLT.uniform_local_clt_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialLocalCLT.uniform_local_clt_sparse

/-- info: 'MajorityDynamics.GraphProcess.RowExactTotals.uniform_exact_totals_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowExactTotals.uniform_exact_totals_sparse

/-- info: 'MajorityDynamics.GraphProcess.RowExactTotals.uniform_conditioned_concentration_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowExactTotals.uniform_conditioned_concentration_sparse

/-- info: 'MajorityDynamics.GraphProcess.RowGamma.uniform_shared_constant_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowGamma.uniform_shared_constant_sparse

/-- info: 'MajorityDynamics.GraphProcess.FiberTransference.uniform_transfer_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.FiberTransference.uniform_transfer_sparse

/-- info: 'MajorityDynamics.GraphProcess.LocalTheorem.terminal_size_transition_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.LocalTheorem.terminal_size_transition_sparse

/-- info: 'MajorityDynamics.Combinatorics.DegreeRatios.degree_ratios_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Combinatorics.DegreeRatios.degree_ratios_sparse

/-- info: 'MajorityDynamics.Probability.NeighborhoodBulk.neighborhood_bulk_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.NeighborhoodBulk.neighborhood_bulk_sparse

/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.uniform_factor_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.uniform_factor_sparse

/-- info: 'MajorityDynamics.Probability.NeighborhoodTail.carrier_neighborhood_tail_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.NeighborhoodTail.carrier_neighborhood_tail_sparse

/-- info: 'MajorityDynamics.GraphProcess.KernelSplitting.uniform_regularity_failure_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelSplitting.uniform_regularity_failure_sparse

/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.c1_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.c1_sparse

/-- info: 'MajorityDynamics.GraphProcess.KernelSplitting.kernel_splitting_estimates_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelSplitting.kernel_splitting_estimates_sparse

/-- info: 'MajorityDynamics.GraphProcess.LocalTheorem.local_coarse_transition_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.LocalTheorem.local_coarse_transition_sparse

/-- info: 'MajorityDynamics.Idealized.RowLimits.row_limits_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.RowLimits.row_limits_sparse

/-- info: 'MajorityDynamics.Idealized.Process.idealized_process_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.Process.idealized_process_sparse

/-- info: 'MajorityDynamics.Idealized.CriticalDay.uniform_flexible_stopping_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.CriticalDay.uniform_flexible_stopping_index

/-- info: 'MajorityDynamics.Idealized.CriticalDay.uniform_flexible_stopping_index_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.CriticalDay.uniform_flexible_stopping_index_at

/-- info: 'MajorityDynamics.Idealized.CriticalDay.uniform_flexible_terminal_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.CriticalDay.uniform_flexible_terminal_budget

/-- info: 'MajorityDynamics.Idealized.LinearResponse.linear_response_spec_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.LinearResponse.linear_response_spec_sparse
