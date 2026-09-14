import MajorityDynamics.Paper.Final.Checks

/-! The closed main theorem and finite-vertex corollary use only Lean foundations.
The unchanged `PaperCompletion.lean` independently enforces this requirement.
-/

example (expansion : MajorityDynamics.Paper.ExpansionPhase)
    (pseudo : MajorityDynamics.Paper.Pseudorandomness) :
    MajorityDynamics.Paper.MainTheorem :=
  MajorityDynamics.Paper.main_of_expansion_and_pseudorandomness expansion pseudo

example : MajorityDynamics.Paper.DeterministicCleanup :=
  MajorityDynamics.Paper.deterministic_cleanup

/-- info: 'MajorityDynamics.Paper.deterministic_cleanup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Paper.deterministic_cleanup

/--
info: 'MajorityDynamics.Paper.main_of_expansion_and_pseudorandomness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Paper.main_of_expansion_and_pseudorandomness

/-- info: 'MajorityDynamics.Paper.main_of_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Paper.main_of_inputs

/-- info: 'MajorityDynamics.Paper.main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Paper.main

example : MajorityDynamics.Paper.Pseudorandomness :=
  MajorityDynamics.Paper.pseudorandomness

example (expansion : MajorityDynamics.Paper.ExpansionPhase) :
    MajorityDynamics.Paper.MainTheorem :=
  MajorityDynamics.Paper.main_of_expansion expansion

/-- info: 'MajorityDynamics.Paper.pseudorandomness_of_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Paper.pseudorandomness_of_inputs

/--
info: 'MajorityDynamics.Paper.minimumDegree_highProbability_of_chernoff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Paper.minimumDegree_highProbability_of_chernoff

/-- info: 'MajorityDynamics.Paper.degreeFailureEnvelope_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Paper.degreeFailureEnvelope_tendsto

/-- info: 'MajorityDynamics.Paper.minimumDegree_highProbability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Paper.minimumDegree_highProbability

/--
info: 'MajorityDynamics.Paper.pseudorandomness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Paper.pseudorandomness

/--
info: 'MajorityDynamics.Paper.main_of_expansion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Paper.main_of_expansion
