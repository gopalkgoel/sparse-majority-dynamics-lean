import MajorityDynamics.GraphProcess.CoarseKernel.Transition
import MajorityDynamics.GraphProcess.GraphicalArray.Identification

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq

namespace MajorityDynamics.GraphProcess.AdmissibleFiber
open FineState Local CoarseKernel
variable {V : Type*} [Fintype V] {n : ℕ}

/-- An incompatible initial coloring makes the literal current event empty. -/
theorem currentEvent_empty_of_incompatible (p : ℝ) (y : CoarseData V n)
    (c : V → Bool) (hc : ¬ CompatibleInitial y.part c) :
    currentEvent p c y = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro G hG
  apply hc
  have hpart : (actualState G c n).part = y.part := congrArg CoarseData.part hG
  rw [← hpart]
  exact ((actualState_eq_iff G c (actualState G c n)).mp rfl).1

/-- Conditioning on that impossible current event is the zero measure. -/
theorem current_cond_zero_of_incompatible (p : ℝ) (y : CoarseData V n)
    (c : V → Bool) (hc : ¬ CompatibleInitial y.part c)
    (μ : Measure (SimpleGraph V)) : cond μ (currentEvent p c y) = 0 := by
  simp [currentEvent_empty_of_incompatible p y c hc]

/-- For an attainable coarse state, compatibility is exactly the remaining
obstruction to positive probability under an interior Bernoulli graph law. -/
theorem current_positive_iff (p : unitInterval) (y : CoarseData V n)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hy : pAttainable p y)
    (c : V → Bool) :
    0 < SimpleGraph.binomialRandom V p (currentEvent p c y) ↔
      CompatibleInitial y.part c := by
  constructor
  · exact compatible_of_positive p c y _
  · intro hc
    rw [currentEvent_eq_E p c y hc]
    exact (E_conditional p y hp hp1 hy).1

/-- Actual probability laws and literal event identities available once the
coarse state is attainable. In particular no quantitative probability bound
or next-step regularity claim is hidden in this bundle. -/
structure ActualLaws (p : unitInterval) (y : CoarseData V n) : Prop where
  graph_pos : 0 < SimpleGraph.binomialRandom V p (E p y)
  graph_probability : IsProbabilityMeasure (cond (SimpleGraph.binomialRandom V p) (E p y))
  graph_uniform : cond (SimpleGraph.binomialRandom V p) (E p y) = uniformOn (E p y)
  lambda_probability : IsProbabilityMeasure (Lambda p y)
  lambda_support : Lambda p y {σ | rho p σ = y} = 1
  lambda_regularity : Lambda p y {σ | Regular p σ.part σ.deg} = 1
  kbar_probability : IsProbabilityMeasure (Kbar p y)
  graphical_pos : 0 < GraphicalArray.law y.part y.edge (GraphicalArray.historyRegular p y.part)
  graphical_probability : IsProbabilityMeasure
    (cond (GraphicalArray.law y.part y.edge) (GraphicalArray.historyRegular p y.part))
  current_positive_iff : ∀ c : V → Bool,
    0 < SimpleGraph.binomialRandom V p (currentEvent p c y) ↔ CompatibleInitial y.part c
  current_event : ∀ c : V → Bool, CompatibleInitial y.part c → currentEvent p c y = E p y
  current_probability : ∀ c : V → Bool, CompatibleInitial y.part c →
    IsProbabilityMeasure (cond (SimpleGraph.binomialRandom V p) (currentEvent p c y))
  incompatible_empty : ∀ c : V → Bool, ¬ CompatibleInitial y.part c → currentEvent p c y = ∅
  incompatible_cond_zero : ∀ c : V → Bool, ¬ CompatibleInitial y.part c →
    cond (SimpleGraph.binomialRandom V p) (currentEvent p c y) = 0
  fine_law : ∀ c : V → Bool, CompatibleInitial y.part c →
    (cond (SimpleGraph.binomialRandom V p) (currentEvent p c y)).map
      (fun G => actualState G c n) = Lambda p y
  coarse_law : ∀ c : V → Bool, CompatibleInitial y.part c →
    (cond (SimpleGraph.binomialRandom V p) (currentEvent p c y)).map
      (fun G => rho p (actualState G c (n+1))) = Kbar p y
  transition : ∀ c : V → Bool, CompatibleInitial y.part c →
    ∀ B : Set (CoarseData V (n+1)),
      cond (SimpleGraph.binomialRandom V p) (currentEvent p c y)
        {G | rho p (actualState G c (n+1)) ∈ B} = Kbar p y B
  graph_array_law : (cond (SimpleGraph.binomialRandom V p) (E p y)).map
      (RowArray.graphArray y.part) =
    cond (GraphicalArray.law y.part y.edge) (GraphicalArray.historyRegular p y.part)
  proposition_3_7 : ∀ B : Set (RowArray.Ambient y.part),
    Lambda p y {σ | σ.deg ∈ RowArray.values '' B} =
      cond (GraphicalArray.law y.part y.edge)
        (RowArray.history y.part ∩ {d | RowArray.Regular p d}) B

/-- The bundle is a consequence of actual attainability and the true original
regularity bit, using only the previously proved exact law identities. -/
theorem actual_laws (p : unitInterval) (y : CoarseData V n)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hy : pAttainable p y) (hr : y.reg = true) : ActualLaws p y where
  graph_pos := (E_conditional p y hp hp1 hy).1
  graph_probability := cond_isProbabilityMeasure (E_conditional p y hp hp1 hy).1.ne'
  graph_uniform := (E_conditional p y hp hp1 hy).2
  lambda_probability := Lambda_probability p y hp hp1 hy
  lambda_support := Lambda_support p y hp hp1 hy
  lambda_regularity := Lambda_regularity p y hp hp1 hy hr
  kbar_probability := Kbar_probability p y hp hp1 hy
  graphical_pos := GraphicalArray.historyRegular_pos p y hp hp1 hy hr
  graphical_probability := by
    have := GraphicalArray.law_probability y
    exact cond_isProbabilityMeasure
      (GraphicalArray.historyRegular_pos p y hp hp1 hy hr).ne'
  current_positive_iff := current_positive_iff p y hp hp1 hy
  current_event := fun c hc => currentEvent_eq_E p c y hc
  current_probability := fun c hc => cond_isProbabilityMeasure
    ((current_positive_iff p y hp hp1 hy c).mpr hc).ne'
  incompatible_empty := currentEvent_empty_of_incompatible p y
  incompatible_cond_zero := fun c hc => current_cond_zero_of_incompatible p y c hc _
  fine_law := fun c hc => current_fine_law p c y hc
  coarse_law := fun c hc => coarse_transition_law p c y hp hp1
    ((current_positive_iff p y hp hp1 hy c).mpr hc)
  transition := fun c hc => coarse_transition p c y hp hp1
    ((current_positive_iff p y hp hp1 hy c).mpr hc)
  graph_array_law := GraphicalArray.conditional_graph_array p y hp hp1 hr
  proposition_3_7 := fun B => (GraphicalArray.proposition_3_7 p y hp hp1 hy hr B).2

end MajorityDynamics.GraphProcess.AdmissibleFiber
