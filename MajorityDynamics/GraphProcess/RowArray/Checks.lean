import MajorityDynamics.GraphProcess.RowArray.Main

/-! Independent expanded contracts and exact dependency audits for the ambient row model. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace MajorityDynamics.GraphProcess.RowArray.Checks
open Universal
variable {V : Type*} [Fintype V] {n : ℕ}

example (π : V → History (n + 1)) :
    Ambient π ≃ {d : V → History (n + 1) → ℤ // ∀ v t, 0 ≤ d v t ∧
      d v t ≤ (Local.partSizes π t : ℤ) - if π v = t then 1 else 0} := literalEquiv π

example (π : V → History (n + 1)) (d : Ambient π) (v : V) (t : History (n + 1)) :
    0 ≤ values d v t ∧
      values d v t ≤ (Local.partSizes π t : ℤ) - if π v = t then 1 else 0 :=
  values_bounds d v t

example (π : V → History (n + 1)) (v : V) (t : History (n + 1)) :
    ((Local.partSizes π t - if π v = t then 1 else 0 : ℕ) : ℤ) =
      (Local.partSizes π t : ℤ) - if π v = t then 1 else 0 := trials_int π v t

example (π : V → History (n + 1)) (G : SimpleGraph V) (v : V) (t : History (n + 1)) :
    values (graphArray π G) v t = ∑ w ∈ History.block π t, if G.Adj v w then 1 else 0 := by
  rw [values_graphArray]
  rfl

example (π : V → History (n + 1)) (d : Ambient π) (v : V) (t : History (n + 1)) :
    (naturalRows d v t : ℤ) = values d v t ∧
      realRow d v t = (values d v t : ℝ) := ⟨rfl, realRow_apply d v t⟩

example (π : V → History (n + 1)) (q : Local.Tilt n) :
    (law π q).map naturalRows = Measure.pi (fun v =>
      Binomial.law (Local.trials (Local.partSizes π) (π v)) (q (π v))) := naturalRows_law π q

example (π : V → History (n + 1)) (q : Local.Tilt n) (v : V) :
    (law π q).map (fun d => naturalRows d v) = Measure.pi (fun t =>
      binomial (Local.trials (Local.partSizes π) (π v) t)
        (Binomial.closedProbability (q (π v) t))) := row_law π q v

example (π : V → History (n + 1)) (q : Local.Tilt n) (v : V) (t : History (n + 1)) :
    (law π q).map (fun d => naturalRows d v t) =
      binomial (Local.partSizes π t - if π v = t then 1 else 0)
        (Binomial.closedProbability (q (π v) t)) := coordinate_law π q v t

example (π : V → History (n + 1)) (q : Local.Tilt n)
    (E : V → History (n + 1) → Set ℕ) :
    law π q {d | ∀ v t, naturalRows d v t ∈ E v t} =
      ∏ v, ∏ t, binomial (Local.partSizes π t - if π v = t then 1 else 0)
        (Binomial.closedProbability (q (π v) t)) (E v t) := entry_rectangle π q E

example (π : V → History (n + 1)) (q : Local.Tilt n)
    (E : V → Set (History (n + 1) → ℕ)) :
    law π q {d | ∀ v, naturalRows d v ∈ E v} =
      ∏ v, Local.rowLaw (Local.partSizes π) q (π v) (E v) := joint_rectangle π q E

example (π : V → History (n + 1)) (q : Local.Tilt n)
    (h : ∀ s, 0 < Local.rowLaw (Local.partSizes π) q s
      {a | WithLp.toLp 2 (fun t => (a t : ℝ)) ∈ Universal.historyEvent s}) :
    0 < law π q {d | ∀ v, realRow d v ∈ Universal.historyEvent (π v)} := history_pos π q h

example (π : V → History (n + 1)) (q : Local.Tilt n)
    (h : ∀ s, 0 < Local.rowLaw (Local.partSizes π) q s
      {a | WithLp.toLp 2 (fun t => (a t : ℝ)) ∈ Universal.historyEvent s}) :
    (cond (law π q) {d | ∀ v, realRow d v ∈ Universal.historyEvent (π v)}).map naturalRows =
      Measure.pi (fun v => Local.rowCondition (Local.partSizes π) q (π v)) :=
  conditioned_rows π q h

example (π : V → History (n + 1)) (q : Local.Tilt n)
    (h : ∀ s, 0 < Local.rowLaw (Local.partSizes π) q s (rowHistory s))
    (E : V → Set (History (n + 1) → ℕ)) :
    cond (law π q) {d | ∀ v, realRow d v ∈ Universal.historyEvent (π v)}
      {d | ∀ v, naturalRows d v ∈ E v} =
      ∏ v, Local.rowCondition (Local.partSizes π) q (π v) (E v) := conditioned_rectangle π q h E

example (π : V → History (n + 1)) (q : Local.Tilt n)
    (h : ∀ s, 0 < Local.rowLaw (Local.partSizes π) q s (rowHistory s)) :
    iIndepFun (fun v d => naturalRows d v)
      (cond (law π q) {d | ∀ v, realRow d v ∈ Universal.historyEvent (π v)}) :=
  conditioned_independent_rows π q h

example (π : V → History (n + 1)) (m : History (n + 1) → History (n + 1) → ℤ)
    (d : Ambient π) : d ∈ exactTotals π m ↔
      ∀ s t, (∑ v ∈ History.block π s, values d v t) = m s t := by
  simp only [exactTotals, Set.mem_ofPred_eq, totals, History.edgeTotals, funext_iff]

example (π : V → History (n + 1)) (m : History (n + 1) → History (n + 1) → ℤ)
    (C p : ℝ) (d : Ambient π) : Gamma π m C p d ↔
    ∀ s t, (1 / (p * (Fintype.card V : ℝ)^2)) *
      (∑ v ∈ History.block π s,
        ((values d v t : ℝ) - (m s t : ℝ) / (Local.partSizes π s : ℝ))^2) ≤ C := Iff.rfl

example (π : V → History (n + 1)) (p : ℝ) (d : Ambient π) : Regular p d ↔
    ∀ v t, |(values d v t : ℝ) - p * (Local.partSizes π t : ℝ)| ≤
      (p * (Fintype.card V : ℝ)) ^ (4 / 7 : ℝ) := Iff.rfl

example (π : V → History (n + 1)) (d : Ambient π) (s : History (n + 1)) (b : Bool) (v : V) :
    v ∈ childSet d s b ↔ π v = s ∧ realRow d v ∈ Universal.childEvent s b := mem_childSet d s b v

example (π : V → History (n + 1)) (d : Ambient π)
    (h : ∀ v, realRow d v ∈ Universal.historyEvent (π v)) (s t : History (n + 1)) :
    (childSet d s false).card + (childSet d s true).card = Local.partSizes π s ∧
      (∑ v ∈ childSet d s false, values d v t) + (∑ v ∈ childSet d s true, values d v t) =
        ∑ v ∈ History.block π s, values d v t :=
  ⟨child_card_conservation d h s, childMass_conservation d h s t⟩

example (σ : FineState.State V n) (s : History (n + 1)) (b : Bool) (t : History (n + 1)) :
    childSet (stateArray σ) s b = History.block (FineState.refinement σ) (append s b) ∧
      childMass (stateArray σ) s b t =
        ∑ v ∈ History.block (FineState.refinement σ) (append s b), σ.deg v t :=
  ⟨childSet_stateArray σ s b, childMass_stateArray σ s b t⟩

/-- Paper day one, arbitrary Fin N, visibly without an assumption N > 0. -/
example (N : ℕ) (π : Fin N → History 1) (q : Local.Tilt 0)
    (h : ∀ s, 0 < Local.rowLaw (Local.partSizes π) q s (rowHistory s)) :
    IsProbabilityMeasure (law π q) ∧
      (cond (law π q) (history π)).map naturalRows =
        Measure.pi (fun v => Local.rowCondition (Local.partSizes π) q (π v)) :=
  ⟨inferInstance, conditioned_rows π q h⟩

/-- info: 'MajorityDynamics.GraphProcess.RowArray.literalEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms literalEquiv
/-- info: 'MajorityDynamics.GraphProcess.RowArray.trials_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trials_int
/-- info: 'MajorityDynamics.GraphProcess.RowArray.graphArray' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graphArray
/-- info: 'MajorityDynamics.GraphProcess.RowArray.stateArray' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stateArray
/-- info: 'MajorityDynamics.GraphProcess.RowArray.law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms law
/-- info: 'MajorityDynamics.GraphProcess.RowArray.naturalRows_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms naturalRows_law
/-- info: 'MajorityDynamics.GraphProcess.RowArray.coordinate_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms coordinate_law
/-- info: 'MajorityDynamics.GraphProcess.RowArray.independent_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms independent_rows
/-- info: 'MajorityDynamics.GraphProcess.RowArray.independent_row_coordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms independent_row_coordinates
/-- info: 'MajorityDynamics.GraphProcess.RowArray.entry_rectangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entry_rectangle
/-- info: 'MajorityDynamics.GraphProcess.RowArray.rowCondition_eq_cond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rowCondition_eq_cond
/-- info: 'MajorityDynamics.GraphProcess.RowArray.history_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms history_pos
/-- info: 'MajorityDynamics.GraphProcess.RowArray.conditioned_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms conditioned_rows
/-- info: 'MajorityDynamics.GraphProcess.RowArray.conditioned_row_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms conditioned_row_law
/-- info: 'MajorityDynamics.GraphProcess.RowArray.conditioned_independent_rows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms conditioned_independent_rows
/-- info: 'MajorityDynamics.GraphProcess.RowArray.conditioned_rectangle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms conditioned_rectangle
/-- info: 'MajorityDynamics.GraphProcess.RowArray.Gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Gamma
/-- info: 'MajorityDynamics.GraphProcess.RowArray.Regular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Regular
/-- info: 'MajorityDynamics.GraphProcess.RowArray.childSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms childSet
/-- info: 'MajorityDynamics.GraphProcess.RowArray.childMass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms childMass
/-- info: 'MajorityDynamics.GraphProcess.RowArray.childSet_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms childSet_union
/-- info: 'MajorityDynamics.GraphProcess.RowArray.child_card_conservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms child_card_conservation
/-- info: 'MajorityDynamics.GraphProcess.RowArray.childMass_conservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms childMass_conservation
/-- info: 'MajorityDynamics.GraphProcess.RowArray.childSet_stateArray' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms childSet_stateArray
/-- info: 'MajorityDynamics.GraphProcess.RowArray.childMass_stateArray' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms childMass_stateArray

end MajorityDynamics.GraphProcess.RowArray.Checks
