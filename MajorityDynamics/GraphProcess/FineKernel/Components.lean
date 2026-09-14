import MajorityDynamics.GraphProcess.FineKernel.Uniform
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.FineKernel
open FineState History BlockDecomposition
open MajorityDynamics.Probability.FixedDegreeSampling
variable {V : Type*} [Fintype V] {n : ℕ}

/-- Uniform on the literal constrained component product. The rectangle theorem
below proves mutual independence and identifies each existing component law. -/
def componentLaw (σ : State V n) : Measure (ComponentFiber σ.part σ.deg) :=
  uniformOn Set.univ

instance componentLaw_probability (σ : State V n) : IsProbabilityMeasure (componentLaw σ) := by
  have := state_components_nonempty σ
  exact ProbabilityTheory.instIsProbabilityMeasure_uniformOn_univ

theorem internal_value_law (σ : State V n) (s : Universal.History (n+1)) :
    (uniformOn (Set.univ : Set (InternalFiber σ.part σ.deg s))).map Subtype.val =
      fixedDegreeLaw (fun v : Block σ.part s => (σ.deg v s).toNat) := by
  convert map_uniform_fiber _ (stateInternalNatEquiv σ s) using 1 <;>
    simp [fixedDegreeLaw, stateInternalNatEquiv, internalNatEquiv]

theorem cross_value_law (σ : State V n) (s t : Universal.History (n+1)) :
    (uniformOn (Set.univ : Set (CrossFiber σ.part σ.deg s t))).map Subtype.val =
      bipartiteFixedDegreeLaw (fun v : Block σ.part s => (σ.deg v t).toNat)
        (fun w : Block σ.part t => (σ.deg w s).toNat) := by
  convert map_uniform_fiber _ (stateCrossNatEquiv σ s t) using 1 <;>
    simp [bipartiteFixedDegreeLaw, stateCrossNatEquiv, crossNatEquiv]

/-- Full joint factorization for arbitrary internal and cross-edge events. -/
theorem component_rectangle (σ : State V n)
    (A : ∀ s : Universal.History (n+1), Set (SimpleGraph (Block σ.part s)))
    (B : ∀ p : Pair (Universal.History (n+1)),
      Set (CrossEdges (Block σ.part p.val.1) (Block σ.part p.val.2))) :
    componentLaw σ {F | (∀ s, (F.1 s).val ∈ A s) ∧ ∀ p, (F.2 p).val ∈ B p} =
      (∏ s, fixedDegreeLaw (fun v : Block σ.part s => (σ.deg v s).toNat) (A s)) *
      ∏ p : Pair (Universal.History (n+1)),
        bipartiteFixedDegreeLaw (fun v : Block σ.part p.val.1 => (σ.deg v p.val.2).toNat)
          (fun w : Block σ.part p.val.2 => (σ.deg w p.val.1).toNat) (B p) := by
  change uniformOn Set.univ
    (({F : ∀ s, InternalFiber σ.part σ.deg s | ∀ s, (F s).val ∈ A s}) ×ˢ
      ({F : ∀ p : Pair (Universal.History (n+1)), CrossFiber σ.part σ.deg p.val.1 p.val.2 |
        ∀ p, (F p).val ∈ B p})) = _
  rw [uniform_prod_rectangle]
  apply congrArg₂ (· * ·)
  · calc
      _ = ∏ s, uniformOn (Set.univ : Set (InternalFiber σ.part σ.deg s))
          {G | G.val ∈ A s} := uniform_pi_rectangle _
      _ = _ := by
        apply Finset.prod_congr rfl
        intro s _
        rw [← internal_value_law, Measure.map_apply (measurable_of_countable _)
          (Set.toFinite _).measurableSet]
        rfl
  · calc
      _ = ∏ p : Pair (Universal.History (n+1)),
          uniformOn (Set.univ : Set (CrossFiber σ.part σ.deg p.val.1 p.val.2))
            {E | E.val ∈ B p} := uniform_pi_rectangle _
      _ = _ := by
        apply Finset.prod_congr rfl
        intro p _
        rw [← cross_value_law, Measure.map_apply (measurable_of_countable _)
          (Set.toFinite _).measurableSet]
        rfl

/-- The actual union graph has precisely the uniform realizer law. -/
theorem glue_componentLaw (σ : State V n) :
    (componentLaw σ).map (fun F => (fiberGlue σ.part σ.deg F).val) =
      uniformOn {G : SimpleGraph V | degreeArray σ.part G = σ.deg} :=
  map_uniform_fiber _ (stateFiberEquiv σ).symm

end MajorityDynamics.GraphProcess.FineKernel
