import MajorityDynamics.GraphProcess.FineKernel.Main
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.FineKernel.Checks
open FineState History BlockDecomposition FineKernel
open MajorityDynamics.Probability.FixedDegreeSampling
variable {V : Type*} [Fintype V] {n : ℕ}

-- Literal component carrier and normalization: no density or coloring input.
example (σ : State V n) :
    componentLaw σ = uniformOn (Set.univ : Set
      (((s : Universal.History (n+1)) → InternalFiber σ.part σ.deg s) ×
        ((p : Pair (Universal.History (n+1))) → CrossFiber σ.part σ.deg p.val.1 p.val.2))) := rfl
example (σ : State V n) : IsProbabilityMeasure (componentLaw σ) := inferInstance

-- Full joint events, not merely individual uniform marginals.
example (σ : State V n)
    (A : ∀ s : Universal.History (n+1), Set (SimpleGraph (Block σ.part s)))
    (B : ∀ p : Pair (Universal.History (n+1)),
      Set (CrossEdges (Block σ.part p.val.1) (Block σ.part p.val.2))) :
    componentLaw σ {F | (∀ s, (F.1 s).val ∈ A s) ∧ ∀ p, (F.2 p).val ∈ B p} =
      (∏ s, uniformOn (graphFamily (fun v : Block σ.part s => (σ.deg v s).toNat)) (A s)) *
      ∏ p : Pair (Universal.History (n+1)),
        uniformOn (bipartiteFamily (fun v : Block σ.part p.val.1 => (σ.deg v p.val.2).toNat)
          (fun w : Block σ.part p.val.2 => (σ.deg w p.val.1).toNat)) (B p) :=
  component_rectangle σ A B

example (σ : State V n) :
    (componentLaw σ).map (fun F => glue σ.part (fiberComponents σ.part σ.deg F)) =
      uniformOn {G : SimpleGraph V | degreeArray σ.part G = σ.deg} := glue_componentLaw σ

-- Each factor is the existing law on actual graphs/edge sets via value projection.
example (σ : State V n) (s : Universal.History (n+1)) :
    (uniformOn (Set.univ : Set (InternalFiber σ.part σ.deg s))).map Subtype.val =
      uniformOn (graphFamily (fun v : Block σ.part s => (σ.deg v s).toNat)) :=
  internal_value_law σ s
example (σ : State V n) (s t : Universal.History (n+1)) :
    (uniformOn (Set.univ : Set (CrossFiber σ.part σ.deg s t))).map Subtype.val =
      uniformOn (bipartiteFamily (fun v : Block σ.part s => (σ.deg v t).toNat)
        (fun w : Block σ.part t => (σ.deg w s).toNat)) := cross_value_law σ s t

-- Actual glued graph data, and its pushforward to a valid next state.
example (σ : State V n) (F : ComponentFiber σ.part σ.deg) :
    sampleNext σ F = nextState σ (fiberGlue σ.part σ.deg F).val
      (fiberGlue σ.part σ.deg F).property := rfl
example (σ : State V n) (F : ComponentFiber σ.part σ.deg) :
    (sampleNext σ F).part = refinement σ ∧
      (sampleNext σ F).deg = degreeArray (refinement σ)
        (glue σ.part (fiberComponents σ.part σ.deg F)) := ⟨rfl, rfl⟩
example (σ : State V n) : K σ = (componentLaw σ).map (sampleNext σ) := rfl
example (σ : State V n) : IsProbabilityMeasure (K σ) := inferInstance
example (σ : State V n) : K σ {τ | τ.part = refinement σ} = 1 := K_refinement σ
example (σ : State V n) : K σ {τ | project (Nat.le_succ n) τ = σ} = 1 := K_project σ

-- Positive actual state mass supplies coloring compatibility, not an extra input.
example (c : V → Bool) (σ : State V n) (p : unitInterval)
    (h : 0 < SimpleGraph.binomialRandom V p {G | actualState G c n = σ}) :
    CompatibleInitial σ.part c ∧
      {G : SimpleGraph V | actualState G c n = σ} =
        {G | degreeArray σ.part G = σ.deg} :=
  ⟨compatible_of_positive c σ _ h, stateEvent_eq_realizer c σ _ h⟩

example (c : V → Bool) (σ : State V n) (p : unitInterval)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (h : 0 < SimpleGraph.binomialRandom V p {G | actualState G c n = σ}) :
    cond (SimpleGraph.binomialRandom V p) {G | actualState G c n = σ} =
      uniformOn {G : SimpleGraph V | degreeArray σ.part G = σ.deg} :=
  state_conditional_graph c σ p hp hp1 h

-- Exact present and full-past endpoint types.
example (c : V → Bool) (σ : State V n) (p : unitInterval)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (h : 0 < SimpleGraph.binomialRandom V p {G | actualState G c n = σ})
    (A : Set (State V (n+1))) :
    cond (SimpleGraph.binomialRandom V p) {G | actualState G c n = σ}
      {G | actualState G c (n+1) ∈ A} = K σ A :=
  present_transition c σ p hp hp1 h A

example (c : V → Bool) (h : (i : Fin (n+1)) → State V i.val)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hpos : 0 < SimpleGraph.binomialRandom V p {G | ∀ i, actualState G c i.val = h i})
    (A : Set (State V (n+1))) :
    cond (SimpleGraph.binomialRandom V p) {G | ∀ i, actualState G c i.val = h i}
      {G | actualState G c (n+1) ∈ A} = K (h (Fin.last n)) A :=
  past_transition c h p hp hp1 hpos A

-- Equality of measures is exported as well as individual event probabilities.
example (c : V → Bool) (σ : State V n) (p : unitInterval)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (h : 0 < SimpleGraph.binomialRandom V p {G | actualState G c n = σ}) :
    (cond (SimpleGraph.binomialRandom V p) {G | actualState G c n = σ}).map
      (fun G => actualState G c (n+1)) = K σ := present_transition_law c σ p hp hp1 h
example (c : V → Bool) (h : (i : Fin (n+1)) → State V i.val)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hpos : 0 < SimpleGraph.binomialRandom V p {G | ∀ i, actualState G c i.val = h i}) :
    (cond (SimpleGraph.binomialRandom V p) {G | ∀ i, actualState G c i.val = h i}).map
      (fun G => actualState G c (n+1)) = K (h (Fin.last n)) :=
  past_transition_law c h p hp hp1 hpos

-- Day one and arbitrary Fin N include N=0 without a hidden nonempty premise.
example (N : ℕ) (c : Fin N → Bool) (σ : State (Fin N) 0) (p : unitInterval)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (h : 0 < SimpleGraph.binomialRandom (Fin N) p {G | actualState G c 0 = σ})
    (A : Set (State (Fin N) 1)) :
    cond (SimpleGraph.binomialRandom (Fin N) p) {G | actualState G c 0 = σ}
      {G | actualState G c 1 ∈ A} = K σ A :=
  present_transition c σ p hp hp1 h A
end MajorityDynamics.GraphProcess.FineKernel.Checks

/-- info: 'MajorityDynamics.GraphProcess.FineKernel.componentLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.FineKernel.componentLaw
/-- info: 'MajorityDynamics.GraphProcess.FineKernel.component_rectangle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.FineKernel.component_rectangle
/-- info: 'MajorityDynamics.GraphProcess.FineKernel.internal_value_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.FineKernel.internal_value_law
/-- info: 'MajorityDynamics.GraphProcess.FineKernel.cross_value_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.FineKernel.cross_value_law
/-- info: 'MajorityDynamics.GraphProcess.FineKernel.glue_componentLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.FineKernel.glue_componentLaw
/-- info: 'MajorityDynamics.GraphProcess.FineKernel.sampleNext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.FineKernel.sampleNext
/-- info: 'MajorityDynamics.GraphProcess.FineKernel.K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.FineKernel.K
/-- info: 'MajorityDynamics.GraphProcess.FineKernel.K_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.FineKernel.K_probability
/-- info: 'MajorityDynamics.GraphProcess.FineKernel.K_refinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.FineKernel.K_refinement
/-- info: 'MajorityDynamics.GraphProcess.FineKernel.K_project' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.FineKernel.K_project
/-- info: 'MajorityDynamics.GraphProcess.FineKernel.K_eq_uniform_graph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.FineKernel.K_eq_uniform_graph
/-- info: 'MajorityDynamics.GraphProcess.FineKernel.realizer_conditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.FineKernel.realizer_conditional
/-- info: 'MajorityDynamics.GraphProcess.FineKernel.compatible_of_positive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.FineKernel.compatible_of_positive
/-- info: 'MajorityDynamics.GraphProcess.FineKernel.state_conditional_graph' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.FineKernel.state_conditional_graph
/-- info: 'MajorityDynamics.GraphProcess.FineKernel.present_transition_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.FineKernel.present_transition_law
/-- info: 'MajorityDynamics.GraphProcess.FineKernel.present_transition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.FineKernel.present_transition
/-- info: 'MajorityDynamics.GraphProcess.FineKernel.pastEvent_eq_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.FineKernel.pastEvent_eq_present
/-- info: 'MajorityDynamics.GraphProcess.FineKernel.past_transition_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.FineKernel.past_transition_law
/-- info: 'MajorityDynamics.GraphProcess.FineKernel.past_transition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.FineKernel.past_transition
