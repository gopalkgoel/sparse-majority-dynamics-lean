import Lean

/-! Dependency-based completion checks for literature contracts. This module
contains no mathematical assumptions and can be tested without loading the paper. -/
namespace MajorityDynamics.Literature.GoalAudit
open Lean Elab Command Meta

structure Goal where
  id : String
  title : String
  declaration : Name
  contract : Name
  wave : String

private def foundations : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- Check the closed contract, including every universe parameter, before inspecting
transitive dependencies. An extra mathematical premise is a type error here. -/
def inspect (goal : Goal) : CommandElabM (Array Name) := do
  let info ← getConstInfo goal.declaration
  unless info.isTheorem || (match info with | .axiomInfo _ => true | _ => false) do
    throwError "{goal.id}: the public endpoint must be a theorem or its existing open axiom"
  let contractInfo ← getConstInfo goal.contract
  unless info.levelParams.length == contractInfo.levelParams.length do
    throwError "{goal.id}: universe parameters changed for {goal.declaration}"
  let expected := mkConst goal.contract (info.levelParams.map Level.param)
  let typeMatches ← liftTermElabM do isDefEq info.type expected
  unless typeMatches do
    throwError "{goal.id}: {goal.declaration} does not have its frozen closed contract {goal.contract}"
  return (← collectAxioms goal.declaration).filter (!foundations.contains ·)

/-- Report every goal. A valid open goal may use the existing ten assumptions;
completion requires none. Unknown axioms (including sorryAx) always fail. -/
def audit (goals : Array Goal) (requireComplete : Bool := false) : CommandElabM Unit := do
  unless (goals.map (·.id)).toList.eraseDups.length == goals.size &&
      (goals.map (·.declaration)).toList.eraseDups.length == goals.size do
    throwError "Duplicate literature goal ID or declaration"
  let allowed := goals.map (·.declaration)
  let mut complete := 0
  let mut invalid := false
  for goal in goals do
    let axioms ← inspect goal
    let unexpected := axioms.filter (!allowed.contains ·)
    let status := if !unexpected.isEmpty then "invalid"
      else if axioms.isEmpty then "complete" else "open"
    if axioms.isEmpty then complete := complete + 1
    if !unexpected.isEmpty then invalid := true
    let row := Json.mkObj [
      ("id", toJson goal.id), ("title", toJson goal.title),
      ("declaration", toJson goal.declaration.toString),
      ("contract", toJson goal.contract.toString), ("wave", toJson goal.wave),
      ("status", toJson status), ("axioms", toJson (axioms.map (·.toString))),
      ("unexpected_axioms", toJson (unexpected.map (·.toString)))]
    logInfo m!"LITERATURE_GOAL {row.compress}"
  let summary := Json.mkObj [("complete", toJson complete), ("total", toJson goals.size),
    ("invalid", toJson invalid)]
  logInfo m!"LITERATURE_SUMMARY {summary.compress}"
  if invalid then
    throwError "Literature audit rejected unlisted mathematical axioms or proof placeholders"
  if requireComplete && complete != goals.size then
    throwError "Literature completion: {complete}/{goals.size} goals proved from foundations; unresolved literature inputs remain"

end MajorityDynamics.Literature.GoalAudit
