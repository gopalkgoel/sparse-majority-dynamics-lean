import MajorityDynamics.GraphProcess.GraphicalArray.Main

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.GraphicalArray.Checks
open GraphicalArray History BlockDecomposition
variable {V : Type*} [Fintype V] {n : ℕ}

-- Every broad count datum is realizable, regardless of its regularity flag or histories.
example (y : Local.CoarseData V n) : ∃ G : SimpleGraph V,
    (fun s t => ∑ v ∈ History.block y.part s, History.degreeArray y.part G v t) = y.edge :=
  coarse_fixedCount_nonempty y

example (A : Type*) [Fintype A] (m : ℤ) (hm : 0 ≤ m) (he : Even m)
    (hu : m ≤ (Fintype.card A : ℤ) * ((Fintype.card A : ℤ)-1)) :
    ∃ G : SimpleGraph A, 2 * (G.edgeFinset.card : ℤ) = m :=
  exists_internal_count A m hm he hu

example (y : Local.CoarseData V n) (C : CountComponents y.part y.edge) :
    ((countFiberEquiv y.part y.edge y.edge_symm).symm C).val =
      BlockDecomposition.glue y.part
        (fun s => (C.1 s).val, fun p => (C.2 p).val) := rfl

example (π : V → Universal.History (n+1))
    (m : Universal.History (n+1) → Universal.History (n+1) → ℤ)
    (hm : ∀ s t, m s t = m t s) :
    (componentLaw π m).map (fun C => glue π (countComponents π m C)) =
      uniformOn {G : SimpleGraph V | edgeTotals π (degreeArray π G) = m} :=
  glue_componentLaw π m hm

example (π : V → Universal.History (n+1))
    (m : Universal.History (n+1) → Universal.History (n+1) → ℤ)
    (A : ∀ s, Set (SimpleGraph (Block π s)))
    (B : ∀ p : Pair (Universal.History (n+1)),
      Set (MajorityDynamics.Probability.FixedDegreeSampling.CrossEdges
        (Block π p.val.1) (Block π p.val.2))) :
    componentLaw π m {F | (∀ s, (F.1 s).val ∈ A s) ∧ ∀ p, (F.2 p).val ∈ B p} =
      (∏ s, uniformOn {G : SimpleGraph (Block π s) | 2 * (G.edgeFinset.card : ℤ) = m s s} (A s)) *
      ∏ p : Pair (Universal.History (n+1)),
        uniformOn {E : MajorityDynamics.Probability.FixedDegreeSampling.CrossEdges
          (Block π p.val.1) (Block π p.val.2) |
          (E.ncard : ℤ) = m p.val.1 p.val.2} (B p) := component_rectangle π m A B

example (y : Local.CoarseData V n) :
    law y.part y.edge =
      (uniformOn {G : SimpleGraph V | edgeTotals y.part (degreeArray y.part G) = y.edge}).map
        (RowArray.graphArray y.part) := rfl

example (π : V → Universal.History (n+1)) (G : SimpleGraph V) :
    RowArray.values (RowArray.graphArray π G) =
      fun v t => ∑ w ∈ History.block π t, if G.Adj v w then 1 else 0 :=
  RowArray.values_graphArray π G

example (p : unitInterval) (y : Local.CoarseData V n)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    0 < SimpleGraph.binomialRandom V p
      {G | edgeTotals y.part (degreeArray y.part G) = y.edge} ∧
      cond (SimpleGraph.binomialRandom V p)
        {G | edgeTotals y.part (degreeArray y.part G) = y.edge} =
      uniformOn {G | edgeTotals y.part (degreeArray y.part G) = y.edge} :=
  fixedCount_conditional p y hp hp1

example (y : Local.CoarseData V n) :
    law y.part y.edge {d | RowArray.totals d = y.edge ∧
      ∃ G : SimpleGraph V, degreeArray y.part G = RowArray.values d} = 1 := law_support y

example (p : unitInterval) (y : Local.CoarseData V n)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hy : ∃ σ : FineState.State V n, CoarseKernel.rho p σ = y) (hr : y.reg = true)
    (B : Set (RowArray.Ambient y.part)) :
    0 < law y.part y.edge (RowArray.history y.part ∩ {d | RowArray.Regular p d}) ∧
    CoarseKernel.Lambda p y {σ | ∃ d ∈ B, RowArray.values d = σ.deg} =
      cond (law y.part y.edge) (RowArray.history y.part ∩ {d | RowArray.Regular p d}) B :=
  proposition_3_7 p y hp hp1 hy hr B

example (y : Local.CoarseData V n) (s : Universal.History (n+1))
    (G : InternalCountFiber y.part y.edge s) :
    G.val.edgeFinset.card = (y.edge s s / 2).toNat := internal_half_count y.part y.edge s G

-- Day one includes the empty graph on Fin 0.
example (N : ℕ) (p : unitInterval) (y : Local.CoarseData (Fin N) 0)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hy : CoarseKernel.pAttainable p y) (hr : y.reg = true)
    (B : Set (RowArray.Ambient y.part)) :
    CoarseKernel.Lambda p y {σ | σ.deg ∈ RowArray.values '' B} =
      cond (law y.part y.edge) (RowArray.history y.part ∩ {d | RowArray.Regular p d}) B :=
  (proposition_3_7 p y hp hp1 hy hr B).2

end MajorityDynamics.GraphProcess.GraphicalArray.Checks


/-- info: 'MajorityDynamics.GraphProcess.GraphicalArray.exists_graph_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GraphicalArray.exists_graph_card

/-- info: 'MajorityDynamics.GraphProcess.GraphicalArray.exists_internal_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GraphicalArray.exists_internal_count

/-- info: 'MajorityDynamics.GraphProcess.GraphicalArray.exists_cross_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GraphicalArray.exists_cross_count

/-- info: 'MajorityDynamics.GraphProcess.GraphicalArray.countFiberEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GraphicalArray.countFiberEquiv

/-- info: 'MajorityDynamics.GraphProcess.GraphicalArray.coarse_fixedCount_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GraphicalArray.coarse_fixedCount_nonempty

/-- info: 'MajorityDynamics.GraphProcess.GraphicalArray.internal_half_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GraphicalArray.internal_half_count

/-- info: 'MajorityDynamics.GraphProcess.GraphicalArray.componentLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GraphicalArray.componentLaw

/-- info: 'MajorityDynamics.GraphProcess.GraphicalArray.componentLaw_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GraphicalArray.componentLaw_probability

/-- info: 'MajorityDynamics.GraphProcess.GraphicalArray.component_rectangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GraphicalArray.component_rectangle

/-- info: 'MajorityDynamics.GraphProcess.GraphicalArray.glue_componentLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GraphicalArray.glue_componentLaw

/-- info: 'MajorityDynamics.GraphProcess.GraphicalArray.component_array_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GraphicalArray.component_array_law

/-- info: 'MajorityDynamics.GraphProcess.GraphicalArray.graphLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GraphicalArray.graphLaw

/-- info: 'MajorityDynamics.GraphProcess.GraphicalArray.law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GraphicalArray.law

/-- info: 'MajorityDynamics.GraphProcess.GraphicalArray.law_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GraphicalArray.law_probability

/-- info: 'MajorityDynamics.GraphProcess.GraphicalArray.fixedCount_conditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GraphicalArray.fixedCount_conditional

/-- info: 'MajorityDynamics.GraphProcess.GraphicalArray.conditional_binomial_array' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GraphicalArray.conditional_binomial_array

/-- info: 'MajorityDynamics.GraphProcess.GraphicalArray.law_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GraphicalArray.law_support

/-- info: 'MajorityDynamics.GraphProcess.GraphicalArray.coarse_event_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GraphicalArray.coarse_event_eq

/-- info: 'MajorityDynamics.GraphProcess.GraphicalArray.historyRegular_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GraphicalArray.historyRegular_pos

/-- info: 'MajorityDynamics.GraphProcess.GraphicalArray.conditional_graph_array' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GraphicalArray.conditional_graph_array

/-- info: 'MajorityDynamics.GraphProcess.GraphicalArray.fiber_array_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GraphicalArray.fiber_array_event

/-- info: 'MajorityDynamics.GraphProcess.GraphicalArray.proposition_3_7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GraphicalArray.proposition_3_7

