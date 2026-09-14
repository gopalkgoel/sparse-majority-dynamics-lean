import MajorityDynamics.GraphProcess.KernelInputs.Main
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Main

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.KernelEdgeSplitting
open Universal BlockDecomposition
variable {V : Type*} [Fintype V] {n : ℕ}

/-- The actual graph glued from the sampled constrained components. -/
def componentGraph (σ : FineState.State V n) (F : ComponentFiber σ.part σ.deg) :
    SimpleGraph V := (fiberGlue σ.part σ.deg F).val

/-- The actual internal graph coordinate. -/
def internalSample (σ : FineState.State V n) (s : History (n+1))
    (F : ComponentFiber σ.part σ.deg) : SimpleGraph (Block σ.part s) := (F.1 s).val

/-- The actual cross graph in either ordered orientation. -/
def crossSample (σ : FineState.State V n) (s t : History (n+1))
    (F : ComponentFiber σ.part σ.deg) :
    MajorityDynamics.Probability.FixedDegreeSampling.CrossEdges (Block σ.part s) (Block σ.part t) :=
  cross σ.part (componentGraph σ F) s t

/-- One literal S3 inequality, with the actual ordered next total and degree-mass center. -/
def EdgeGood (y : Local.CoarseData V n) (p C : ℝ)
    (σ : FineState.State V n) (τ : FineState.State V (n+1))
    (s t : History (n+1)) (b c : Bool) : Prop :=
  |(CoarseKernel.rho p τ).realEdges (append s b) (append t c) -
    (RowArray.childMass (RowArray.stateArray σ) s b t : ℝ) *
      (RowArray.childMass (RowArray.stateArray σ) t c s : ℝ) / y.realEdges s t| ≤
    C * LocalTransition.edgeScale (Fintype.card V) p

/-- Exactly S3, simultaneously over every ordered child pair. -/
def EdgesGood (y : Local.CoarseData V n) (p C : ℝ)
    (σ : FineState.State V n) (τ : FineState.State V (n+1)) : Prop :=
  ∀ s t b c, EdgeGood y p C σ τ s t b c

/-- The completed S1 and S3 event. -/
def SplitEdgesGood (y : Local.CoarseData V n) (p C : ℝ)
    (σ : FineState.State V n) (τ : FineState.State V (n+1)) : Prop :=
  τ.part = FineState.refinement σ ∧ EdgesGood y p C σ τ

/-- Explicit error after the finite union over the child pairs. -/
def unionError (n N : ℕ) : ℝ := (2 : ℝ)^(2*n+5) / Real.log N

theorem kernelGood_iff (y : Local.CoarseData V n) (p C : ℝ)
    (σ : FineState.State V n) (τ : FineState.State V (n+1)) :
    LocalTransition.KernelGood y p C σ τ ↔
      SplitEdgesGood y p C σ τ ∧ CoarseKernel.Regular p τ.part τ.deg := by
  simp only [LocalTransition.KernelGood, SplitEdgesGood, EdgesGood, EdgeGood]
  tauto

end MajorityDynamics.GraphProcess.KernelEdgeSplitting
