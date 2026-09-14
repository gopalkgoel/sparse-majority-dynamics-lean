import MajorityDynamics.GraphProcess.RowConcentration.Basic

/-! Exact positivity, conditional marginals, and expectations of the original statistics. -/
set_option maxHeartbeats 1000000
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace MajorityDynamics.GraphProcess.RowConcentration
open Universal
variable {V : Type*} [Fintype V] {n : ℕ}

theorem row_history_mass (sizes : Local.Sizes n) (q : Local.Tilt n)
    (s : History (n + 1)) :
    (Local.rowLaw sizes q s).real (RowArray.rowHistory s) =
      Binomial.eventMass (Local.trials sizes s) (q s) (Local.historySupport sizes s) := by
  rw [Binomial.eventMass_eq_measure]
  have ha : Binomial.event (Local.historySupport sizes s) =ᵐ[Local.rowLaw sizes q s]
      RowArray.rowHistory s := by
    filter_upwards [Binomial.law_ae_box (Local.trials sizes s) (q s)] with a ha
    apply propext
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact (Local.mem_historySupport _ _ _).mp hc
    · intro h
      refine ⟨fun t => ⟨a t, Nat.lt_succ_of_le (ha t)⟩, ?_, rfl⟩
      exact (Local.mem_historySupport _ _ _).mpr h
  exact congrArg ENNReal.toReal (measure_congr ha).symm

theorem row_history_pos (y : Local.CoarseData V n) (q : Local.Tilt n) {φ : ℝ}
    (hφ : 0 < φ) (hc : Conditioning y q φ) (s : History (n + 1)) :
    0 < Local.rowLaw y.sizes q s (RowArray.rowHistory s) := by
  have hp : 0 < (Local.rowLaw y.sizes q s).real (RowArray.rowHistory s) := by
    rw [row_history_mass]
    exact hφ.trans_le (hc s)
  exact pos_iff_ne_zero.mpr (ENNReal.toReal_ne_zero.mp hp.ne').1

theorem history_pos (y : Local.CoarseData V n) (q : Local.Tilt n) {φ : ℝ}
    (hφ : 0 < φ) (hc : Conditioning y q φ) :
    0 < RowArray.law y.part q (RowArray.history y.part) :=
  RowArray.history_pos y.part q (row_history_pos y q hφ hc)

theorem conditioned_probability (y : Local.CoarseData V n) (q : Local.Tilt n) {φ : ℝ}
    (hφ : 0 < φ) (hc : Conditioning y q φ) :
    IsProbabilityMeasure (conditionedLaw y q) :=
  cond_isProbabilityMeasure (history_pos y q hφ hc).ne'

theorem conditioned_row_event_le (y : Local.CoarseData V n) (q : Local.Tilt n) {φ : ℝ}
    (hφ : 0 < φ) (hc : Conditioning y q φ) (v : V)
    (E : Set (History (n + 1) → ℕ)) :
    (conditionedLaw y q).real {d | RowArray.naturalRows d v ∈ E} ≤
      (Local.rowLaw y.sizes q (y.part v)).real E / φ := by
  have hm := RowArray.conditioned_row_law y.part q (row_history_pos y q hφ hc) v
  change (conditionedLaw y q).map (fun d => RowArray.naturalRows d v) =
    Local.rowCondition y.sizes q (y.part v) at hm
  have he : (conditionedLaw y q).real {d | RowArray.naturalRows d v ∈ E} =
      (Local.rowCondition y.sizes q (y.part v)).real E := by
    rw [← hm]
    simp only [measureReal_def, Measure.map_apply (measurable_of_countable _)
      (Set.to_countable _).measurableSet]
    rfl
  rw [he, RowArray.rowCondition_eq_cond, measureReal_def,
    cond_apply' (Set.to_countable _).measurableSet,
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  rw [mul_comm, ← div_eq_mul_inv]
  change (Local.rowLaw y.sizes q (y.part v)).real (RowArray.rowHistory (y.part v) ∩ E) /
    (Local.rowLaw y.sizes q (y.part v)).real (RowArray.rowHistory (y.part v)) ≤ _
  let : IsProbabilityMeasure (Local.rowLaw y.sizes q (y.part v)) :=
    inferInstanceAs (IsProbabilityMeasure (Binomial.law _ _))
  calc
    _ ≤ (Local.rowLaw y.sizes q (y.part v)).real E /
        (Local.rowLaw y.sizes q (y.part v)).real (RowArray.rowHistory (y.part v)) :=
      div_le_div_of_nonneg_right (measureReal_mono Set.inter_subset_right) measureReal_nonneg
    _ ≤ _ := div_le_div_of_nonneg_left measureReal_nonneg hφ
      (by rw [row_history_mass]; exact hc (y.part v))

theorem raw_row_coordinate (sizes : Local.Sizes n) (q : Local.Tilt n)
    (s t : History (n + 1)) (E : Set ℕ) :
    (Local.rowLaw sizes q s).real {a | a t ∈ E} =
      (binomial (Local.trials sizes s t) (Binomial.closedProbability (q s t))).real E := by
  have hm := Binomial.coordinate_law (Local.trials sizes s) (q s) t
  rw [← hm]
  simp only [measureReal_def, Measure.map_apply (measurable_pi_apply t)
    (Set.to_countable _).measurableSet]
  rfl

def rowChildIndicator (s : History (n + 1)) (b : Bool)
    (a : History (n + 1) → ℕ) : ℝ :=
  if WithLp.toLp 2 (fun t => (a t : ℝ)) ∈ childEvent s b then 1 else 0

def rowChildVariable (s : History (n + 1)) (b : Bool) (t : History (n + 1))
    (a : History (n + 1) → ℕ) : ℝ :=
  if WithLp.toLp 2 (fun u => (a u : ℝ)) ∈ childEvent s b then (a t : ℝ) else 0

theorem rowChildIndicator_integral (sizes : Local.Sizes n) (q : Local.Tilt n)
    (s : History (n + 1)) (b : Bool) :
    ∫ a, rowChildIndicator s b a ∂Local.rowCondition sizes q s =
      Local.splitProbability sizes q s b := by
  rw [Local.rowCondition, Binomial.integral_conditionalLaw]
  change (∑ a ∈ Local.historySupport sizes s,
    Binomial.conditionalWeight (Local.trials sizes s) (q s) (Local.historySupport sizes s) a *
      (if Local.rowVector a ∈ childEvent s b then (1 : ℝ) else 0)) = _
  simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  have hf : (Local.historySupport sizes s).filter
      (fun a => Local.rowVector a ∈ childEvent s b) =
      Local.childSupport sizes s b := by
    ext a
    simp only [Finset.mem_filter, Local.mem_historySupport, Local.mem_childSupport]
    exact ⟨And.right, fun h => ⟨h.1, h⟩⟩
  rw [hf]
  simp only [Local.splitProbability, Binomial.eventMass, Binomial.conditionalWeight, Finset.sum_div]

theorem rowChildVariable_integral (sizes : Local.Sizes n) (q : Local.Tilt n)
    (s : History (n + 1)) (b : Bool) (t : History (n + 1)) :
    ∫ a, rowChildVariable s b t a ∂Local.rowCondition sizes q s =
      Local.splitMoment sizes q s b t := by
  rw [Local.rowCondition, Binomial.integral_conditionalLaw]
  change (∑ a ∈ Local.historySupport sizes s,
    Binomial.conditionalWeight (Local.trials sizes s) (q s) (Local.historySupport sizes s) a *
      (if Local.rowVector a ∈ childEvent s b then Binomial.vector a t else 0)) = _
  simp only [mul_ite, mul_zero, ← Finset.sum_filter]
  have hf : (Local.historySupport sizes s).filter
      (fun a => Local.rowVector a ∈ childEvent s b) =
      Local.childSupport sizes s b := by
    ext a
    simp only [Finset.mem_filter, Local.mem_historySupport, Local.mem_childSupport]
    exact ⟨And.right, fun h => ⟨h.1, h⟩⟩
  rw [hf]
  simp only [Local.splitMoment, Binomial.conditionalWeight, Finset.sum_div, div_mul_eq_mul_div]

theorem childIndicator_as_row {π : V → History (n + 1)} (s : History (n + 1))
    (b : Bool) (v : V) (d : RowArray.Ambient π) :
    childIndicator s b v d = if π v = s then rowChildIndicator s b (RowArray.naturalRows d v)
      else 0 := by
  simp only [childIndicator, RowArray.mem_childSet, rowChildIndicator, ite_and]
  rfl

theorem childVariable_as_row {π : V → History (n + 1)} (s : History (n + 1))
    (b : Bool) (t : History (n + 1)) (v : V) (d : RowArray.Ambient π) :
    childVariable s b t v d = if π v = s then
      rowChildVariable s b t (RowArray.naturalRows d v) else 0 := by
  simp only [childVariable, RowArray.mem_childSet, rowChildVariable, ite_and]
  simp only [RowArray.values, RowArray.naturalRows, Binomial.point, Int.cast_natCast]
  rfl

theorem independent_childIndicator (y : Local.CoarseData V n) (q : Local.Tilt n)
    {φ : ℝ} (hφ : 0 < φ) (hc : Conditioning y q φ) (s : History (n + 1)) (b : Bool) :
    iIndepFun (childIndicator (π := y.part) s b) (conditionedLaw y q) := by
  have h := (RowArray.conditioned_independent_rows y.part q (row_history_pos y q hφ hc)).comp
    (fun v a => if y.part v = s then rowChildIndicator s b a else 0)
    (fun _ => measurable_of_countable _)
  change iIndepFun (fun v d => childIndicator s b v d) (cond (RowArray.law y.part q) _)
  simpa only [Function.comp_def, ← childIndicator_as_row] using h

theorem independent_childVariable (y : Local.CoarseData V n) (q : Local.Tilt n)
    {φ : ℝ} (hφ : 0 < φ) (hc : Conditioning y q φ)
    (s : History (n + 1)) (b : Bool) (t : History (n + 1)) :
    iIndepFun (childVariable (π := y.part) s b t) (conditionedLaw y q) := by
  have h := (RowArray.conditioned_independent_rows y.part q (row_history_pos y q hφ hc)).comp
    (fun v a => if y.part v = s then rowChildVariable s b t a else 0)
    (fun _ => measurable_of_countable _)
  change iIndepFun (fun v d => childVariable s b t v d) (cond (RowArray.law y.part q) _)
  simpa only [Function.comp_def, ← childVariable_as_row] using h

theorem integral_row_function (y : Local.CoarseData V n) (q : Local.Tilt n) {φ : ℝ}
    (hφ : 0 < φ) (hc : Conditioning y q φ) (v : V)
    (f : (History (n + 1) → ℕ) → ℝ) :
    ∫ d, f (RowArray.naturalRows d v) ∂conditionedLaw y q =
      ∫ a, f a ∂Local.rowCondition y.sizes q (y.part v) := by
  have hm := RowArray.conditioned_row_law y.part q (row_history_pos y q hφ hc) v
  change (conditionedLaw y q).map (fun d => RowArray.naturalRows d v) =
    Local.rowCondition y.sizes q (y.part v) at hm
  rw [← hm]
  exact (integral_map_of_stronglyMeasurable (measurable_of_countable _)
    (measurable_of_countable f).stronglyMeasurable).symm

theorem integral_childIndicator (y : Local.CoarseData V n) (q : Local.Tilt n)
    {φ : ℝ} (hφ : 0 < φ) (hc : Conditioning y q φ)
    (s : History (n + 1)) (b : Bool) (v : V) :
    ∫ d, childIndicator s b v d ∂conditionedLaw y q =
      if y.part v = s then Local.splitProbability y.sizes q s b else 0 := by
  simp_rw [childIndicator_as_row]
  split_ifs with hv
  · rw [integral_row_function y q hφ hc, hv, rowChildIndicator_integral]
  · simp only [integral_zero]

theorem integral_childVariable (y : Local.CoarseData V n) (q : Local.Tilt n)
    {φ : ℝ} (hφ : 0 < φ) (hc : Conditioning y q φ)
    (s : History (n + 1)) (b : Bool) (t : History (n + 1)) (v : V) :
    ∫ d, childVariable s b t v d ∂conditionedLaw y q =
      if y.part v = s then Local.splitMoment y.sizes q s b t else 0 := by
  simp_rw [childVariable_as_row]
  split_ifs with hv
  · rw [integral_row_function y q hφ hc, hv, rowChildVariable_integral]
  · simp only [integral_zero]

theorem expected_child_card (y : Local.CoarseData V n) (q : Local.Tilt n)
    {φ : ℝ} (hφ : 0 < φ) (hc : Conditioning y q φ)
    (s : History (n + 1)) (b : Bool) :
    ∫ d, ((RowArray.childSet d s b).card : ℝ) ∂conditionedLaw y q =
      Local.templateSizes y.sizes q (append s b) := by
  let := conditioned_probability y q hφ hc
  simp_rw [← sum_childIndicator]
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_childIndicator y q hφ hc]
  rw [← Finset.sum_filter]
  have he : Finset.univ.filter (fun v => y.part v = s) = History.block y.part s := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, History.mem_block]
  rw [he]
  simp only [Finset.sum_const, nsmul_eq_mul, History.block_card_partSizes,
    Local.templateSizes, parent_append, last_append]
  rfl

theorem expected_child_mass (y : Local.CoarseData V n) (q : Local.Tilt n)
    {φ : ℝ} (hφ : 0 < φ) (hc : Conditioning y q φ)
    (s : History (n + 1)) (b : Bool) (t : History (n + 1)) :
    ∫ d, (RowArray.childMass d s b t : ℝ) ∂conditionedLaw y q =
      Local.templateHalfEdges y.sizes q (append s b) t := by
  let := conditioned_probability y q hφ hc
  simp_rw [← sum_childVariable]
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_childVariable y q hφ hc]
  rw [← Finset.sum_filter]
  have he : Finset.univ.filter (fun v => y.part v = s) = History.block y.part s := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, History.mem_block]
  rw [he]
  simp only [Finset.sum_const, nsmul_eq_mul, History.block_card_partSizes,
    Local.templateHalfEdges, parent_append, last_append]
  rfl

end MajorityDynamics.GraphProcess.RowConcentration
