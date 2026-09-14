import MajorityDynamics.GraphProcess.FineKernel.Components
import MajorityDynamics.GraphProcess.FineKernel.Conditioning
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.FineKernel
open FineState History BlockDecomposition
variable {V : Type*} [Fintype V] {n : ℕ}

instance stateMeasurable : MeasurableSpace (State V n) := ⊤
instance stateDiscrete : DiscreteMeasurableSpace (State V n) := ⟨fun _ => trivial⟩

/-- Read actual glued graph degrees in the state's deterministic refinement. -/
def sampleNext (σ : State V n) (F : ComponentFiber σ.part σ.deg) : State V (n+1) :=
  nextState σ (fiberGlue σ.part σ.deg F).val (fiberGlue σ.part σ.deg F).property

@[simp] theorem sampleNext_part (σ : State V n) (F : ComponentFiber σ.part σ.deg) :
    (sampleNext σ F).part = refinement σ := rfl
@[simp] theorem sampleNext_deg (σ : State V n) (F : ComponentFiber σ.part σ.deg) :
    (sampleNext σ F).deg = degreeArray (refinement σ) (glue σ.part (fiberComponents σ.part σ.deg F)) := rfl

theorem sampleNext_actual (σ : State V n) (F : ComponentFiber σ.part σ.deg)
    (c : V → Bool) (hc : CompatibleInitial σ.part c) :
    sampleNext σ F = actualState (fiberGlue σ.part σ.deg F).val c (n+1) :=
  nextState_eq_actual σ _ c _ hc

/-- Universal transition kernel: no density or initial coloring parameter. -/
def K (σ : State V n) : Measure (State V (n+1)) := (componentLaw σ).map (sampleNext σ)

instance K_probability (σ : State V n) : IsProbabilityMeasure (K σ) := by
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

theorem K_apply (σ : State V n) (A : Set (State V (n+1))) :
    K σ A = componentLaw σ {F | sampleNext σ F ∈ A} :=
  Measure.map_apply (measurable_of_countable _) (Set.toFinite _).measurableSet

theorem sampleNext_project (σ : State V n) (F : ComponentFiber σ.part σ.deg) :
    project (Nat.le_succ n) (sampleNext σ F) = σ := by
  rw [sampleNext_actual σ F (initial σ) (initial_compatible σ), project_actualState]
  exact reconstruction_state σ _ (initial σ) (fiberGlue σ.part σ.deg F).property
    (initial_compatible σ)

theorem K_refinement (σ : State V n) : K σ {τ | τ.part = refinement σ} = 1 := by
  rw [K_apply]
  simpa only [Set.mem_ofPred_eq, sampleNext_part, Set.ofPred_true] using measure_univ (μ := componentLaw σ)

theorem K_project (σ : State V n) : K σ {τ | project (Nat.le_succ n) τ = σ} = 1 := by
  rw [K_apply]
  simpa only [Set.mem_ofPred_eq, sampleNext_project, Set.ofPred_true] using measure_univ (μ := componentLaw σ)

/-- Gluing the independent component law gives this equivalent whole-graph formula. -/
theorem K_eq_uniform_graph (σ : State V n) (c : V → Bool)
    (hc : CompatibleInitial σ.part c) :
    K σ = (uniformOn (realizerEvent σ)).map (fun G => actualState G c (n+1)) := by
  unfold K realizerEvent
  rw [← glue_componentLaw σ, Measure.map_map (measurable_of_countable _)
    (measurable_of_countable _)]
  congr 1
  funext F
  exact sampleNext_actual σ F c hc

end MajorityDynamics.GraphProcess.FineKernel
