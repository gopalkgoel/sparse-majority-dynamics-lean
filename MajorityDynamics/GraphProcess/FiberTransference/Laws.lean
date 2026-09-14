import MajorityDynamics.GraphProcess.FiberTransference.Bayes
import MajorityDynamics.GraphProcess.AdmissibleFiber.Main

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.FiberTransference
variable {V : Type*} [Fintype V] {n : ℕ}

def graphArrayLaw (p : unitInterval) (y : Local.CoarseData V n) :=
  (SimpleGraph.binomialRandom V p).map (RowArray.graphArray y.part)

instance graphArrayLaw_probability (p : unitInterval) (y : Local.CoarseData V n) :
    IsProbabilityMeasure (graphArrayLaw p y) :=
  Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

theorem count_preimage (y : Local.CoarseData V n) :
    RowArray.graphArray y.part ⁻¹' RowArray.exactTotals y.part y.edge =
      GraphicalArray.fixedCountFamily y.part y.edge := by
  ext G
  simp [RowArray.exactTotals, RowArray.totals, GraphicalArray.fixedCountFamily]

theorem graphical_as_cond (p : unitInterval) (y : Local.CoarseData V n)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    GraphicalArray.law y.part y.edge =
      cond (graphArrayLaw p y) (RowArray.exactTotals y.part y.edge) := by
  classical
  rw [← GraphicalArray.conditional_binomial_array p y hp hp1]
  change (cond (SimpleGraph.binomialRandom V p) _).map _ =
    cond ((SimpleGraph.binomialRandom V p).map _ ) _
  rw [← GraphicalArray.map_cond_preimage]
  rw [count_preimage]

theorem graphical_history_cond (p : unitInterval) (y : Local.CoarseData V n)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    cond (GraphicalArray.law y.part y.edge) (GraphicalArray.historyRegular p y.part) =
      cond (graphArrayLaw p y)
        (RowArray.exactTotals y.part y.edge ∩ GraphicalArray.historyRegular p y.part) := by
  rw [graphical_as_cond p y hp hp1,
    cond_cond_eq_cond_inter (Set.to_countable _).measurableSet
      (Set.to_countable _).measurableSet]

theorem count_mass (p : unitInterval) (y : Local.CoarseData V n) :
    (graphArrayLaw p y).real (RowArray.exactTotals y.part y.edge) =
      (SimpleGraph.binomialRandom V p).real (GraphicalArray.fixedCountFamily y.part y.edge) := by
  unfold graphArrayLaw Measure.real
  rw [Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
  rw [count_preimage]

theorem lambda_complement (p : unitInterval) (y : Local.CoarseData V n)
    (h : AdmissibleFiber.ActualLaws p y) (E : Set (RowArray.Ambient y.part)) :
    (CoarseKernel.Lambda p y).real {σ | σ.deg ∉ RowArray.values '' E} =
      (cond (GraphicalArray.law y.part y.edge)
        (GraphicalArray.historyRegular p y.part)).real Eᶜ := by
  let := h.lambda_probability
  let := h.graphical_probability
  change (CoarseKernel.Lambda p y).real {σ | σ.deg ∈ RowArray.values '' E}ᶜ = _
  rw [probReal_compl_eq_one_sub (Set.to_countable _).measurableSet,
    probReal_compl_eq_one_sub (Set.to_countable _).measurableSet]
  exact congrArg (fun z => 1 - z.toReal) (h.proposition_3_7 E)

theorem row_condition_order (y : Local.CoarseData V n) (q : Local.Tilt n) :
    cond (cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge))
      (RowArray.history y.part) =
    cond (RowConcentration.conditionedLaw y q) (RowArray.exactTotals y.part y.edge) := by
  rw [RowExactTotals.iterated_history_totals,
    cond_cond_eq_cond_inter (Set.to_countable _).measurableSet
      (Set.to_countable _).measurableSet, Set.inter_comm]

end MajorityDynamics.GraphProcess.FiberTransference
