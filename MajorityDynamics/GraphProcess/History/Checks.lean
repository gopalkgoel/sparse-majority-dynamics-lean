import MajorityDynamics.GraphProcess.History.Main

/-! Expanded endpoints on the actual paper dynamics and foundational axiom audits. -/
noncomputable section
open scoped BigOperators
namespace MajorityDynamics.GraphProcess.History
open Universal

example (N k : ℕ) (G : Paper.Graph N) (c : Paper.Coloring N) (v : Fin N) (r : Fin k) :
    bits k (actualHistory G c k v) r = Paper.coloringOnDay G c (r.val + 1) v :=
  bits_actualHistory G c k v r

example (N k : ℕ) (G : Paper.Graph N) (c : Paper.Coloring N) (v : Fin N)
    (s : Universal.History k) :
    v ∈ block (actualHistory G c k) s ↔ ∀ r : ℕ, (hr : 1 ≤ r ∧ r ≤ k) →
      Paper.opinion (Paper.coloringOnDay G c r v) =
        Paper.opinion (bits k s ⟨r - 1, by omega⟩) :=
  mem_actualBlock_days G c k v s

example (N k : ℕ) (G : Paper.Graph N) (c : Paper.Coloring N) :
    ∑ s, (block (actualHistory G c k) s).card = N := by
  simpa using sum_block_card (actualHistory G c k)

example (N n : ℕ) (G : Paper.Graph N) (c : Paper.Coloring N) (v : Fin N) :
    ∀ r : Fin n,
      decision (Paper.coloringOnDay G c (r.val + 1) v)
        (Paper.coloringOnDay G c (r.val + 2) v)
        (∑ t, sign (bits (n + 1) t r.castSucc) *
          (degreeArray (actualHistory G c (n + 1)) G v t : ℝ)) := by
  simpa only [historyEvent, Set.mem_ofPred_eq, bits_actualHistory, Fin.val_castSucc,
    Fin.val_succ, imbalance, character, actualRow_apply, Nat.add_assoc,
    Probability.RandomOpinionsReduction.coloringOnDay_fin] using actualRow_historyEvent G c n v

example (N n : ℕ) (G : Paper.Graph N) (c : Paper.Coloring N) (v : Fin N)
    (s : Universal.History (n + 1)) (b : Bool) :
    actualHistory G c (n + 2) v = append s b ↔
      actualHistory G c (n + 1) v = s ∧
        WithLp.toLp 2 (fun t => (degreeArray (actualHistory G c (n + 1)) G v t : ℝ)) ∈
          childEvent s b := by
  simpa only [mem_block, actualRow] using child_block_event G c n v s b

example (V : Type*) [Fintype V] (n : ℕ) (π : V → Universal.History (n + 1))
    (G : SimpleGraph V) (flag : Bool) : Local.CoarseData V n := toCoarseData π G flag

example (N : ℕ) (G : Paper.Graph N) (c : Paper.Coloring N) (v : Fin N) (b : Bool) :
    actualRow G c 1 v ∈ childEvent (actualHistory G c 1 v) b ↔
      Paper.coloringOnDay G c 2 v = b := actualRow_childEvent_iff G c 0 v _ b rfl

/-- info: 'MajorityDynamics.GraphProcess.History.mem_actualBlock_days' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mem_actualBlock_days
/-- info: 'MajorityDynamics.GraphProcess.History.actualHistory_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms actualHistory_succ
/-- info: 'MajorityDynamics.GraphProcess.History.degreeArray_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms degreeArray_upper
/-- info: 'MajorityDynamics.GraphProcess.History.edgeTotals_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edgeTotals_diagonal
/-- info: 'MajorityDynamics.GraphProcess.History.toCoarseData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms toCoarseData
/-- info: 'MajorityDynamics.GraphProcess.History.neighborSum_of_fiber_coloring' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms neighborSum_of_fiber_coloring
/-- info: 'MajorityDynamics.GraphProcess.History.actualRow_historyEvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms actualRow_historyEvent
/-- info: 'MajorityDynamics.GraphProcess.History.child_block_event_set' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms child_block_event_set
/-- info: 'MajorityDynamics.GraphProcess.History.degreeArray_coarsen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms degreeArray_coarsen
/-- info: 'MajorityDynamics.GraphProcess.History.edgeTotals_coarsen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edgeTotals_coarsen
/-- info: 'MajorityDynamics.GraphProcess.History.edgeTotals_parent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edgeTotals_parent
end MajorityDynamics.GraphProcess.History
