import MajorityDynamics.GraphProcess.RowExactTotals.Regularity

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.RowExactTotals
open Universal

/-- Actual conditioning divides event mass by the conditioning-event mass. -/
theorem conditioned_real_eq_div {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E F : Set Ω) (hF : MeasurableSet F) :
    (cond μ E).real F = μ.real (E ∩ F) / μ.real E := by
  rw [measureReal_def, cond_apply' hF, ENNReal.toReal_mul, ENNReal.toReal_inv]
  simp only [measureReal_def, div_eq_mul_inv, mul_comm]

/-- Bayes' loss bound for the actual conditional measure. -/
theorem conditioned_real_le_div {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E F : Set Ω) (hF : MeasurableSet F) :
    (cond μ E).real F ≤ μ.real F / μ.real E := by
  rw [conditioned_real_eq_div μ E F hF]
  exact div_le_div_of_nonneg_right (measureReal_mono Set.inter_subset_right) measureReal_nonneg

/-- A positive real event-mass lower bound certifies actual normalization. -/
theorem conditioned_probability_of_real_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : Set Ω) {b : ℝ}
    (hb : 0 < b) (hE : b ≤ μ.real E) : IsProbabilityMeasure (cond μ E) := by
  exact cond_isProbabilityMeasure (ENNReal.toReal_ne_zero.mp (hb.trans_le hE).ne').1

/-- Exact polynomial denominator loss, with the original base N²p. -/
theorem conditioned_failure_power {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E F : Set Ω) (hF : MeasurableSet F)
    {N p e A : ℝ} (hN : 0 < N) (hp : 0 < p) (hp1 : p ≤ 1) (he : 0 ≤ e)
    (hE : (N^2*p)^(-e) ≤ μ.real E)
    (hfailure : μ.real F ≤ N^(-(A+2*e))) :
    (cond μ E).real F ≤ N^(-A) := by
  have hb : 0 < (N^2*p)^(-e) := Real.rpow_pos_of_pos (by positivity) _
  have hmono : (N^2*p)^e ≤ N^(2*e) := by
    calc
      _ ≤ (N^2)^e := Real.rpow_le_rpow (by positivity)
        (by nlinarith [sq_nonneg N]) he
      _ = N^(2*e) := by rw [← Real.rpow_two, ← Real.rpow_mul hN.le]
  have hdiv : μ.real F / μ.real E ≤ N^(-(A+2*e)) * (N^2*p)^e := by
    calc
      _ ≤ μ.real F / (N^2*p)^(-e) :=
        div_le_div_of_nonneg_left measureReal_nonneg hb hE
      _ ≤ N^(-(A+2*e)) / (N^2*p)^(-e) :=
        div_le_div_of_nonneg_right hfailure hb.le
      _ = _ := by rw [Real.rpow_neg (by positivity : 0 ≤ N^2*p), div_inv_eq_mul]
  calc
    _ ≤ μ.real F / μ.real E := conditioned_real_le_div μ E F hF
    _ ≤ N^(-(A+2*e)) * (N^2*p)^e := hdiv
    _ ≤ N^(-(A+2*e)) * N^(2*e) :=
      mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg hN.le _)
    _ = N^(-A) := by rw [← Real.rpow_add hN]; congr 1; ring

/-- The iterated law is literally simultaneous history-and-total conditioning. -/
theorem iterated_history_totals {V : Type*} [Fintype V] {n : ℕ}
    (y : Local.CoarseData V n) (q : Local.Tilt n) :
    cond (RowConcentration.conditionedLaw y q) (RowArray.exactTotals y.part y.edge) =
      cond (RowArray.law y.part q)
        (RowArray.history y.part ∩ RowArray.exactTotals y.part y.edge) := by
  exact cond_cond_eq_cond_inter (Set.to_countable _).measurableSet
    (Set.to_countable _).measurableSet _

end MajorityDynamics.GraphProcess.RowExactTotals

/-- info: 'MajorityDynamics.GraphProcess.RowExactTotals.conditioned_real_eq_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowExactTotals.conditioned_real_eq_div

/-- info: 'MajorityDynamics.GraphProcess.RowExactTotals.conditioned_real_le_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowExactTotals.conditioned_real_le_div

/-- info: 'MajorityDynamics.GraphProcess.RowExactTotals.conditioned_probability_of_real_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowExactTotals.conditioned_probability_of_real_lower

/-- info: 'MajorityDynamics.GraphProcess.RowExactTotals.conditioned_failure_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowExactTotals.conditioned_failure_power

/-- info: 'MajorityDynamics.GraphProcess.RowExactTotals.iterated_history_totals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowExactTotals.iterated_history_totals
