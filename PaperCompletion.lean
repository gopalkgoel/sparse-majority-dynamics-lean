import MajorityDynamics.Paper.Main

/-!
# Whole-paper completion gate

Run `lake env lean PaperCompletion.lean` after `lake build`.
This file is deliberately excluded from the default build: it FAILS until the
main theorem has no mathematical axioms beyond Lean's standard foundations.
Do not change the expected axiom list to make unfinished work pass.

The exact type check additionally rejects a replacement theorem that takes
unresolved mathematical hypotheses as extra arguments. Statement fidelity still
requires human review of `Problem.lean` and the canonical-vertex-set scope.
-/

example : MajorityDynamics.Paper.MainTheorem := MajorityDynamics.Paper.main

/-- info: 'MajorityDynamics.Paper.main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Paper.main
