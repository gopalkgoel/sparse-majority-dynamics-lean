import MajorityDynamics.GraphProcess.FaithfulTrajectory.SparseStopped
import MajorityDynamics.Idealized.CriticalDay.TerminalAsymptotics
import MajorityDynamics.Idealized.CriticalDay.SparseFaithfulRows
import MajorityDynamics.Idealized.CriticalDay.SparseCore
import MajorityDynamics.GraphProcess.FaithfulTrajectory.SparseTerminalStep

/-! Stopped trajectory and terminal graph transition audits. -/

/-- info: 'MajorityDynamics.GraphProcess.FaithfulTrajectory.uniform_faithful_step_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.FaithfulTrajectory.uniform_faithful_step_sparse

/-- info: 'MajorityDynamics.GraphProcess.FaithfulTrajectory.uniform_sparse_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.FaithfulTrajectory.uniform_sparse_prefix

/-- info: 'MajorityDynamics.GraphProcess.FaithfulTrajectory.uniform_stopped_faithfulness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.FaithfulTrajectory.uniform_stopped_faithfulness

/-- info: 'MajorityDynamics.Idealized.CriticalDay.terminal_error_small_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.CriticalDay.terminal_error_small_uniform

/-- info: 'MajorityDynamics.Idealized.CriticalDay.terminal_faithful_rows_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.CriticalDay.terminal_faithful_rows_sparse

/-- info: 'MajorityDynamics.Idealized.CriticalDay.terminal_faithful_core_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.CriticalDay.terminal_faithful_core_sparse

/-- info: 'MajorityDynamics.Idealized.CriticalDay.terminal_lead_budget_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.CriticalDay.terminal_lead_budget_sparse

/-- info: 'MajorityDynamics.GraphProcess.FaithfulTrajectory.uniform_terminal_step_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.FaithfulTrajectory.uniform_terminal_step_sparse
