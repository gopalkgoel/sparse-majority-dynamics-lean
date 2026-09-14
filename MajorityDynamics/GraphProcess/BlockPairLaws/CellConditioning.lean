import MajorityDynamics.GraphProcess.BlockPairLaws.Cells
import MajorityDynamics.GraphProcess.BlockPairLaws.Atoms

/-! Exact count conditioning preserves independence of disjoint ordered cells. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators Classical ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.BlockPairLaws
open Universal BlockDecomposition
variable {V : Type*} [Fintype V] {n : ℕ}

theorem map_cond_preimage_countable {α β : Type*} [Countable α] [Countable β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure α) (f : α → β) (B : Set β) :
    (cond μ (f ⁻¹' B)).map f = cond (μ.map f) B := by
  ext C _
  rw [Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,
    cond_apply (Set.to_countable _).measurableSet,
    cond_apply (Set.to_countable _).measurableSet,
    Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,
    Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
  rfl

theorem cond_pi_countable {I : Type*} [Fintype I] {A : I → Type*}
    [∀ i, Countable (A i)] [∀ i, MeasurableSpace (A i)]
    [∀ i, MeasurableSingletonClass (A i)]
    (μ : ∀ i, Measure (A i)) [∀ i, IsProbabilityMeasure (μ i)]
    (E : ∀ i, Set (A i)) (h : ∀ i, 0 < μ i (E i)) :
    cond (Measure.pi μ) (Set.univ.pi E) = Measure.pi (fun i => cond (μ i) (E i)) := by
  have (i : I) : IsProbabilityMeasure (cond (μ i) (E i)) :=
    cond_isProbabilityMeasure (h i).ne'
  symm
  apply Measure.pi_eq
  intro F hF
  rw [cond_apply (MeasurableSet.univ_pi (fun _ => (Set.to_countable _).measurableSet)),
    Measure.pi_pi, ← Set.pi_inter_distrib, Measure.pi_pi]
  simp_rw [cond_apply (Set.to_countable _).measurableSet]
  rw [Finset.prod_mul_distrib, ENNReal.prod_inv_distrib]
  intro i _ j _ _
  exact Or.inl (h i).ne'

theorem cellsTotals_pos (y : Local.CoarseData V n) (q : Local.Tilt n) :
    0 < cellsLaw y.part q (cellsTotals y.part y.edge) := by
  rw [← cells_law, Measure.map_apply (measurable_of_countable _)
    (Set.to_countable _).measurableSet, ← cells_totals]
  exact exactTotals_pos y q

theorem cellTotal_pos (y : Local.CoarseData V n) (q : Local.Tilt n)
    (s t : History (n+1)) :
    0 < cellNaturalLaw y.part q s t (cellTotal y.part y.edge s t) := by
  have h := (cellsTotals_pos y q).ne'
  simp only [cellsLaw, cellsTotals, Measure.pi_pi, Finset.prod_ne_zero_iff,
    Finset.mem_univ, forall_const] at h
  exact pos_iff_ne_zero.mpr (h s t)

/-- Literal binomial sequence conditioned on its prescribed total. -/
def cellCondition (π : V → History (n+1))
    (m : History (n+1) → History (n+1) → ℤ) (q : Local.Tilt n)
    (s t : History (n+1)) : Measure (Block π s → ℕ) :=
  cond (cellNaturalLaw π q s t) (cellTotal π m s t)

theorem cellCondition_probability (y : Local.CoarseData V n) (q : Local.Tilt n)
    (s t : History (n+1)) : IsProbabilityMeasure (cellCondition y.part y.edge q s t) :=
  cond_isProbabilityMeasure (cellTotal_pos y q s t).ne'

theorem cells_conditioned (y : Local.CoarseData V n) (q : Local.Tilt n) :
    (cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge)).map cells =
      Measure.pi (fun s => Measure.pi fun t => cellCondition y.part y.edge q s t) := by
  rw [cells_totals, map_cond_preimage_countable, cells_law]
  unfold cellsLaw cellsTotals
  rw [cond_pi_countable]
  · congr 1
    funext s
    exact cond_pi_countable _ _ (cellTotal_pos y q s)
  · intro s
    rw [Measure.pi_pi]
    exact pos_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun t _ => (cellTotal_pos y q s t).ne')

/-- Full joint rectangle law over *all* ordered cells. -/
theorem ordered_cell_rectangle (y : Local.CoarseData V n) (q : Local.Tilt n)
    (E : ∀ s _t : History (n+1), Set (Block y.part s → ℕ)) :
    cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge)
      {d | ∀ s t, cells d s t ∈ E s t} =
      ∏ s, ∏ t, cellCondition y.part y.edge q s t (E s t) := by
  have (s t : History (n+1)) := cellCondition_probability y q s t
  have h := congrArg (fun μ : Measure (Cells y.part) =>
    μ (Set.univ.pi fun s => Set.univ.pi fun t => E s t)) (cells_conditioned y q)
  rw [Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet] at h
  simpa only [Measure.pi_pi, Set.preimage, Set.mem_univ_pi] using h

end MajorityDynamics.GraphProcess.BlockPairLaws
