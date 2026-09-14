import MajorityDynamics.Idealized.CriticalDay.HistorySolverSparse
import MajorityDynamics.Idealized.RowLimits.ParameterBudget

/-! Ingredient audits only: the complete uniform expansion theorem is still open. -/

/-- info: 'MajorityDynamics.Idealized.RowLimits.row_history_mean_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.RowLimits.row_history_mean_sparse

/-- info: 'MajorityDynamics.Idealized.RowLimits.normalized_parameter_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.RowLimits.normalized_parameter_budget

/-- info: 'MajorityDynamics.Idealized.CriticalDay.solve_of_history_parameters_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.CriticalDay.solve_of_history_parameters_sparse
