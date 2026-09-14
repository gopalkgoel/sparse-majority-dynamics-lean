import MajorityDynamics.GraphProcess.GraphicalArray.CountFibers
import MajorityDynamics.GraphProcess.RowArray.Main

noncomputable section
open MeasureTheory ProbabilityTheory
open unitInterval (toNNReal)
open scoped Classical ENNReal BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.GraphicalArray
open History FineState
open MajorityDynamics.Probability.FixedDegreeSampling
variable {V : Type*} [Fintype V] {n : ℕ}

/-- The fixed-count graph law depends only on the partition and ordered counts. -/
def graphLaw (π : V → Universal.History (n+1))
    (m : Universal.History (n+1) → Universal.History (n+1) → ℤ) : Measure (SimpleGraph V) :=
  uniformOn (fixedCountFamily π m)

/-- The actual graphical auxiliary law: push an actual sampled simple graph to its array. -/
def law (π : V → Universal.History (n+1))
    (m : Universal.History (n+1) → Universal.History (n+1) → ℤ) : Measure (RowArray.Ambient π) :=
  (graphLaw π m).map (RowArray.graphArray π)

def Graphical {π : V → Universal.History (n+1)} (d : RowArray.Ambient π) : Prop :=
  ∃ G : SimpleGraph V, degreeArray π G = RowArray.values d

theorem graphLaw_probability (y : Local.CoarseData V n) :
    IsProbabilityMeasure (graphLaw y.part y.edge) :=
  isProbabilityMeasure_uniformOn (Set.toFinite _) (coarse_fixedCount_nonempty y)

theorem law_probability (y : Local.CoarseData V n) :
    IsProbabilityMeasure (law y.part y.edge) := by
  have := graphLaw_probability y
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

theorem fixedCount_same_edges (π : V → Universal.History (n+1))
    (m : Universal.History (n+1) → Universal.History (n+1) → ℤ)
    (G H : fixedCountFamily π m) : G.val.edgeSet.ncard = H.val.edgeSet.ncard := by
  have hg := CoarseKernel.total_edges π G.val
  have hh := CoarseKernel.total_edges π H.val
  rw [G.property] at hg
  rw [H.property] at hh
  omega

/-- Positive mass follows from broad coarse count capacities alone. -/
theorem fixedCount_conditional (p : unitInterval) (y : Local.CoarseData V n)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    0 < SimpleGraph.binomialRandom V p (fixedCountFamily y.part y.edge) ∧
      cond (SimpleGraph.binomialRandom V p) (fixedCountFamily y.part y.edge) =
        graphLaw y.part y.edge := by
  obtain ⟨G,hG⟩ := coarse_fixedCount_nonempty y
  apply conditional_eq_uniform _ _ ⟨G,hG⟩
    ((toNNReal p : ℝ≥0∞)^G.edgeSet.ncard *
      (toNNReal (unitInterval.symm p) : ℝ≥0∞)^((Nat.card V).choose 2 - G.edgeSet.ncard))
    (bernoulli_weight_ne_zero p hp hp1 _ _)
  intro H hH
  rw [SimpleGraph.binomialRandom_singleton, fixedCount_same_edges y.part y.edge ⟨H,hH⟩ ⟨G,hG⟩]

theorem conditional_binomial_array (p : unitInterval) (y : Local.CoarseData V n)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    (cond (SimpleGraph.binomialRandom V p) (fixedCountFamily y.part y.edge)).map
      (RowArray.graphArray y.part) = law y.part y.edge := by
  rw [(fixedCount_conditional p y hp hp1).2]
  rfl

theorem law_support (y : Local.CoarseData V n) :
    law y.part y.edge (RowArray.exactTotals y.part y.edge ∩ {d | Graphical d}) = 1 := by
  have := graphLaw_probability y
  rw [law, Measure.map_apply (measurable_of_countable _) (Set.toFinite _).measurableSet]
  apply le_antisymm (measure_mono (Set.subset_univ _) |>.trans_eq measure_univ)
  have hs : graphLaw y.part y.edge (fixedCountFamily y.part y.edge) = 1 := by
    exact uniformOn_self (Set.toFinite _) (coarse_fixedCount_nonempty y)
  rw [← hs]
  apply measure_mono
  intro G hG
  exact ⟨by simpa [RowArray.exactTotals, fixedCountFamily] using hG,
    ⟨G, (RowArray.values_graphArray _ _).symm⟩⟩

/-- Finite conditioning commutes with any actual map; no injectivity is needed. -/
theorem map_cond_preimage {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure α) (f : α → β) (B : Set β) :
    (cond μ (f ⁻¹' B)).map f = cond (μ.map f) B := by
  ext C _
  rw [Measure.map_apply (measurable_of_countable _) (Set.toFinite _).measurableSet,
    cond_apply (Set.toFinite _).measurableSet, cond_apply (Set.toFinite _).measurableSet,
    Measure.map_apply (measurable_of_countable _) (Set.toFinite _).measurableSet,
    Measure.map_apply (measurable_of_countable _) (Set.toFinite _).measurableSet]
  rfl

end MajorityDynamics.GraphProcess.GraphicalArray
