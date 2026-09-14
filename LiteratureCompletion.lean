import LiteratureGoals

/-! Strict independent completion gate. Intentionally outside the default build:
all eleven public literature endpoints must have their exact closed contracts and
only the standard foundational axioms. Reports every goal before failing.
Run after `lake build --wfail LiteratureGoals`.
This complements, and never replaces or relaxes, `PaperCompletion.lean`. -/
run_cmd do
  MajorityDynamics.Literature.GoalAudit.audit
    MajorityDynamics.Literature.goals (requireComplete := true)
