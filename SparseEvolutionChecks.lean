import MajorityDynamics.Idealized.PerturbedEvolution.SparseMain
import MajorityDynamics.GraphProcess.DayOne.SparseMain
import MajorityDynamics.Idealized.CriticalDay.PreStoppingResponse

/-! Ingredient audits; the uniform expansion endpoint is still open. -/

/-- info: 'MajorityDynamics.Idealized.LinearResponse.linear_response_spec_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.LinearResponse.linear_response_spec_sparse

/-- info: 'MajorityDynamics.Idealized.PerturbedEvolution.perturbed_evolution_spec_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.PerturbedEvolution.perturbed_evolution_spec_sparse

/-- info: 'MajorityDynamics.GraphProcess.DayOne.day_one_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.DayOne.day_one_sparse

/-- info: 'MajorityDynamics.Idealized.CriticalDay.pre_stopping_response_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.CriticalDay.pre_stopping_response_small

