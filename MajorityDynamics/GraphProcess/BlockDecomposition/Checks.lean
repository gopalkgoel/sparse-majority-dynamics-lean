import MajorityDynamics.GraphProcess.BlockDecomposition.Main

/-! Independent expanded contracts and transitive axiom audits. -/
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.BlockDecomposition
open History
open MajorityDynamics.Probability.FixedDegreeSampling

example (V L : Type*) [Fintype V] [Fintype L] [LinearOrder L] (π : V → L) :
    SimpleGraph V ≃
      (((s : L) → SimpleGraph {v : V // π v = s}) ×
       ((p : {p : L × L // p.1 < p.2}) →
        Set ({v : V // π v = p.val.1} × {w : V // π w = p.val.2}))) :=
  decompositionEquiv π

example (V : Type*) [Fintype V] (k : ℕ) (π : V → Universal.History k)
    (d : V → Universal.History k → ℤ) :
    FineState.Realizable π d ↔
      (∀ s, ∃ G : SimpleGraph {v : V // π v = s}, ∀ v, (G.degree v : ℤ) = d v s) ∧
      (∀ s t, s ≠ t → ∃ E : Set ({v : V // π v = s} × {w : V // π w = t}),
        (∀ v, ((Finset.univ.filter fun w => (v,w) ∈ E).card : ℤ) = d v t) ∧
        (∀ w, ((Finset.univ.filter fun v => (v,w) ∈ E).card : ℤ) = d w s)) :=
  by
    convert! fact_graphical_blockwise π d using 1
    simp only [InternalGraphical, CrossGraphical, leftDegree, leftNeighbors,
      rightDegree, rightNeighbors]
    simp only [SimpleGraph.degree, SimpleGraph.neighborFinset, Set.toFinset_card,
      ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]

example (V L : Type*) [Fintype V] [Fintype L] [LinearOrder L]
    (π : V → L) (d : V → L → ℤ) :
    {G : SimpleGraph V // degreeArray π G = d} ≃
      (((s : L) → {G : SimpleGraph {v : V // π v = s} //
        ∀ v, (G.degree v : ℤ) = d v s}) ×
       ((p : {p : L × L // p.1 < p.2}) →
        {E : Set ({v : V // π v = p.val.1} × {w : V // π w = p.val.2}) //
          (∀ v, (leftDegree E v : ℤ) = d v p.val.2) ∧
          (∀ w, (rightDegree E w : ℤ) = d w p.val.1)})) := fiberEquiv π d

example (V L : Type*) [Fintype V] [Fintype L] [LinearOrder L]
    (π : V → L) (d : V → L → ℤ) (G : GraphFiber π d) (s : L)
    (v w : Block π s) :
    (((fiberEquiv π d G).1 s).val).Adj v w ↔ G.val.Adj v.val w.val := Iff.rfl

example (V L : Type*) [Fintype V] [Fintype L] [LinearOrder L]
    (π : V → L) (d : V → L → ℤ) (G : GraphFiber π d) (p : Pair L)
    (v : Block π p.val.1) (w : Block π p.val.2) :
    (v,w) ∈ ((fiberEquiv π d G).2 p).val ↔ G.val.Adj v.val w.val := Iff.rfl

example (V L : Type*) [Fintype V] [Fintype L] [LinearOrder L]
    (π : V → L) (d : V → L → ℤ) (F : ComponentFiber π d) :
    ((fiberEquiv π d).symm F).val =
      glue π ⟨fun s => (F.1 s).val, fun p => (F.2 p).val⟩ := rfl

example (V L : Type*) [Fintype V] [Fintype L] [LinearOrder L]
    (π : V → L) (d : V → L → ℤ) :
    Nat.card {G : SimpleGraph V // degreeArray π G = d} =
      (∏ s, Nat.card {G : SimpleGraph {v : V // π v = s} //
        ∀ v, (G.degree v : ℤ) = d v s}) *
      ∏ p : {p : L × L // p.1 < p.2},
        Nat.card {E : Set ({v : V // π v = p.val.1} × {w : V // π w = p.val.2}) //
          (∀ v, (leftDegree E v : ℤ) = d v p.val.2) ∧
          (∀ w, (rightDegree E w : ℤ) = d w p.val.1)} := realization_count π d

example (V : Type*) [Fintype V] (n : ℕ) (σ : FineState.State V n) :
    {G : SimpleGraph V // degreeArray σ.part G = σ.deg} ≃
      ComponentFiber σ.part σ.deg := stateFiberEquiv σ

example (V : Type*) [Fintype V] (n : ℕ) (σ : FineState.State V n) :
    Nonempty (ComponentFiber σ.part σ.deg) := state_components_nonempty σ

example (V : Type*) [Fintype V] (n : ℕ) (σ : FineState.State V n)
    (s : Universal.History (n+1)) :
    InternalFiber σ.part σ.deg s ≃
      graphFamily (fun v : Block σ.part s => (σ.deg v s).toNat) := stateInternalNatEquiv σ s

example (V : Type*) [Fintype V] (n : ℕ) (σ : FineState.State V n)
    (s t : Universal.History (n+1)) :
    CrossFiber σ.part σ.deg s t ≃
      bipartiteFamily (fun v : Block σ.part s => (σ.deg v t).toNat)
        (fun w : Block σ.part t => (σ.deg w s).toNat) := stateCrossNatEquiv σ s t

/-- Impossible negative targets stay impossible, rather than truncating to zero. -/
example (V L : Type*) [Fintype V] (π : V → L) (d : V → L → ℤ)
    (v : V) (t : L) (h : d v t < 0) : ¬ ∃ G : SimpleGraph V, degreeArray π G = d := by
  rintro ⟨G, hG⟩
  have hn := degreeArray_nonneg π G v t
  rw [hG] at hn
  omega

/-- info: 'MajorityDynamics.GraphProcess.BlockDecomposition.decompositionEquiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decompositionEquiv
/-- info: 'MajorityDynamics.GraphProcess.BlockDecomposition.restrict_glue' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms restrict_glue
/-- info: 'MajorityDynamics.GraphProcess.BlockDecomposition.glue_restrict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms glue_restrict
/-- info: 'MajorityDynamics.GraphProcess.BlockDecomposition.glue_internal_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms glue_internal_degree
/-- info: 'MajorityDynamics.GraphProcess.BlockDecomposition.glue_left_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms glue_left_degree
/-- info: 'MajorityDynamics.GraphProcess.BlockDecomposition.glue_right_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms glue_right_degree
/-- info: 'MajorityDynamics.GraphProcess.BlockDecomposition.cellLabel_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cellLabel_injective
/-- info: 'MajorityDynamics.GraphProcess.BlockDecomposition.indexed_cellEdges_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms indexed_cellEdges_disjoint
/-- info: 'MajorityDynamics.GraphProcess.BlockDecomposition.edge_count_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edge_count_decomposition
/-- info: 'MajorityDynamics.GraphProcess.BlockDecomposition.glue_edge_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms glue_edge_count
/-- info: 'MajorityDynamics.GraphProcess.BlockDecomposition.graphical_blockwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms graphical_blockwise
/-- info: 'MajorityDynamics.GraphProcess.BlockDecomposition.fact_graphical_blockwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fact_graphical_blockwise
/-- info: 'MajorityDynamics.GraphProcess.BlockDecomposition.fiberEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fiberEquiv
/-- info: 'MajorityDynamics.GraphProcess.BlockDecomposition.realization_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms realization_count
/-- info: 'MajorityDynamics.GraphProcess.BlockDecomposition.stateFiberEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stateFiberEquiv
/-- info: 'MajorityDynamics.GraphProcess.BlockDecomposition.state_components_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms state_components_nonempty
/-- info: 'MajorityDynamics.GraphProcess.BlockDecomposition.state_graphFamily_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms state_graphFamily_nonempty
/-- info: 'MajorityDynamics.GraphProcess.BlockDecomposition.state_bipartiteFamily_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms state_bipartiteFamily_nonempty
/-- info: 'MajorityDynamics.GraphProcess.BlockDecomposition.state_degree_toNat_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms state_degree_toNat_cast
/-- info: 'MajorityDynamics.GraphProcess.BlockDecomposition.internalNatEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms internalNatEquiv
/-- info: 'MajorityDynamics.GraphProcess.BlockDecomposition.crossNatEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms crossNatEquiv
/-- info: 'MajorityDynamics.GraphProcess.BlockDecomposition.state_realization_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms state_realization_count
end MajorityDynamics.GraphProcess.BlockDecomposition
