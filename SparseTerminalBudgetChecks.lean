import MajorityDynamics.Idealized.CriticalDay.CoreAdmissibilityBudget
import MajorityDynamics.Idealized.CriticalDay.SparseTiltBound
import MajorityDynamics.Idealized.CriticalDay.ReferenceLogBudget
import MajorityDynamics.Idealized.CriticalDay.TerminalFaithfulBudget
import MajorityDynamics.Idealized.CriticalDay.TerminalRowsSmallError

/-! Ingredient checks; the full uniform expansion phase remains open. -/

/-- info: 'MajorityDynamics.Idealized.CriticalDay.core_admissible_of_centered_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.CriticalDay.core_admissible_of_centered_budget

/-- info: 'MajorityDynamics.Idealized.CriticalDay.row_tilt_bound_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.CriticalDay.row_tilt_bound_sparse

/-- info: 'MajorityDynamics.Idealized.CriticalDay.reference_coordinates_log_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.CriticalDay.reference_coordinates_log_budget

/-- info: 'MajorityDynamics.Idealized.CriticalDay.faithful_centered_terminal_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.CriticalDay.faithful_centered_terminal_budget

/-- info: 'MajorityDynamics.Idealized.CriticalDay.terminal_rows_small_error_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.CriticalDay.terminal_rows_small_error_sparse

