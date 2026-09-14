import MajorityDynamics.GraphProcess.GraphicalArray.Law

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.GraphicalArray
open History FineState
variable {V : Type*} [Fintype V] {n : ℕ}

/-- The original vertex histories together with the original regularity predicate. -/
def historyRegular (p : ℝ) (π : V → Universal.History (n+1)) : Set (RowArray.Ambient π) :=
  RowArray.history π ∩ {d | RowArray.Regular p d}

theorem realRow_graphArray (π : V → Universal.History (n+1)) (G : SimpleGraph V) (v : V) :
    RowArray.realRow (RowArray.graphArray π G) v = row (degreeArray π G) v := by
  apply WithLp.ofLp_injective
  funext t
  change RowArray.realRow (RowArray.graphArray π G) v t = (degreeArray π G v t : ℝ)
  rw [RowArray.realRow_apply, RowArray.values_graphArray]

theorem coarse_event_eq (p : ℝ) (y : Local.CoarseData V n) (hr : y.reg = true) :
    CoarseKernel.E p y = fixedCountFamily y.part y.edge ∩
      RowArray.graphArray y.part ⁻¹' historyRegular p y.part := by
  ext G
  simp only [CoarseKernel.E, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
    fixedCountFamily, historyRegular, RowArray.history, RowArray.Regular,
    RowArray.values_graphArray, realRow_graphArray, hr, CoarseKernel.flag_true]
  tauto

/-- The second Bayes denominator is positive from actual attainability, not a new assumption. -/
theorem historyRegular_pos (p : unitInterval) (y : Local.CoarseData V n)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hy : CoarseKernel.pAttainable p y) (hr : y.reg = true) :
    0 < law y.part y.edge (historyRegular p y.part) := by
  rw [← conditional_binomial_array p y hp hp1,
    Measure.map_apply (measurable_of_countable _) (Set.toFinite _).measurableSet]
  apply cond_pos_of_inter_ne_zero (Set.toFinite _).measurableSet
  rw [← coarse_event_eq p y hr]
  exact (CoarseKernel.E_conditional p y hp hp1 hy).1.ne'

/-- Bayes bridge from the actual Bernoulli coarse event to the graphical auxiliary law. -/
theorem conditional_graph_array (p : unitInterval) (y : Local.CoarseData V n)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hr : y.reg = true) :
    (cond (SimpleGraph.binomialRandom V p) (CoarseKernel.E p y)).map
      (RowArray.graphArray y.part) = cond (law y.part y.edge) (historyRegular p y.part) := by
  rw [coarse_event_eq p y hr, ← cond_cond_eq_cond_inter
    (Set.toFinite _).measurableSet (Set.toFinite _).measurableSet,
    map_cond_preimage, conditional_binomial_array p y hp hp1]

theorem values_injective (π : V → Universal.History (n+1)) :
    Function.Injective (@RowArray.values V _ n π) := by
  intro a b h
  exact (RowArray.literalEquiv π).injective (Subtype.ext h)

/-- On the actual conditioning support the existing Lambda state has exactly the graph array. -/
theorem fiber_array_event (p : ℝ) (y : Local.CoarseData V n)
    (B : Set (RowArray.Ambient y.part)) :
    CoarseKernel.E p y ∩ {G | (actualState G (CoarseKernel.initial y) n).deg ∈ RowArray.values '' B} =
      CoarseKernel.E p y ∩ RowArray.graphArray y.part ⁻¹' B := by
  ext G
  constructor
  · rintro ⟨hG,d,hd,he⟩
    refine ⟨hG, ?_⟩
    have hval : RowArray.values d = RowArray.values (RowArray.graphArray y.part G) := by
      rw [RowArray.values_graphArray, ← (CoarseKernel.raw_agreement p y G hG).2.1]
      exact he
    change RowArray.graphArray y.part G ∈ B
    exact (values_injective y.part hval) ▸ hd
  · rintro ⟨hG,hB⟩
    refine ⟨hG, RowArray.graphArray y.part G, hB, ?_⟩
    rw [RowArray.values_graphArray]
    exact (CoarseKernel.raw_agreement p y G hG).2.1.symm

/-- Proposition 3.7, for every literal ambient-array event and the existing actual Lambda.
The only substantive hypotheses are interior p, p-attainability and the true regularity bit. -/
theorem proposition_3_7 (p : unitInterval) (y : Local.CoarseData V n)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hy : CoarseKernel.pAttainable p y) (hr : y.reg = true)
    (B : Set (RowArray.Ambient y.part)) :
    0 < law y.part y.edge (RowArray.history y.part ∩ {d | RowArray.Regular p d}) ∧
    CoarseKernel.Lambda p y {σ | σ.deg ∈ RowArray.values '' B} =
      cond (law y.part y.edge) (RowArray.history y.part ∩ {d | RowArray.Regular p d}) B := by
  refine ⟨historyRegular_pos p y hp hp1 hy hr, ?_⟩
  change CoarseKernel.Lambda p y {σ | σ.deg ∈ RowArray.values '' B} =
    cond (law y.part y.edge) (historyRegular p y.part) B
  rw [← conditional_graph_array p y hp hp1 hr,
    CoarseKernel.Lambda,
    Measure.map_apply (measurable_of_countable _) (Set.toFinite _).measurableSet,
    Measure.map_apply (measurable_of_countable _) (Set.toFinite _).measurableSet,
    cond_apply (Set.toFinite _).measurableSet, cond_apply (Set.toFinite _).measurableSet]
  exact congrArg (fun S =>
    (SimpleGraph.binomialRandom V p (CoarseKernel.E p y))⁻¹ *
      SimpleGraph.binomialRandom V p S) (fiber_array_event p y B)

end MajorityDynamics.GraphProcess.GraphicalArray
