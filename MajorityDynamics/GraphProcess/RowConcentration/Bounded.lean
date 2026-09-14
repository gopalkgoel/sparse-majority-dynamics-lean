import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace MajorityDynamics.GraphProcess.RowConcentration.Bounded

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- Two-sided Chernoff bound for a sub-Gaussian random variable. -/
theorem subgaussian_abs_tail {X : Ω → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |X ω|} ≤ 2 * Real.exp (-ε ^ 2 / (2 * c)) := by
  have hset : {ω | ε ≤ |X ω|} = {ω | ε ≤ X ω} ∪ {ω | ε ≤ -X ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs]
  rw [hset]
  calc
    _ ≤ μ.real {ω | ε ≤ X ω} + μ.real {ω | ε ≤ -X ω} :=
      measureReal_union_le _ _
    _ ≤ Real.exp (-ε ^ 2 / (2 * c)) + Real.exp (-ε ^ 2 / (2 * c)) := by
      exact add_le_add (hX.measure_ge_le hε) (hX.neg.measure_ge_le hε)
    _ = _ := by ring

/-- Hoeffding's inequality for a finite sum of independent variables in `[0,B]`.
The statement also covers an empty index set and `B=0`. -/
theorem sum_tail {X : ι → Ω → ℝ} (hind : iIndepFun X μ)
    (hmeas : ∀ i, AEMeasurable (X i) μ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc 0 B)
    (s : Finset ι) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ i ∈ s, (X i ω - ∫ x, X i x ∂μ)|} ≤
      2 * Real.exp (-2 * ε ^ 2 / ((s.card : ℝ) * B ^ 2)) := by
  classical
  have hind' : iIndepFun (fun i ω ↦ X i ω - ∫ x, X i x ∂μ) μ :=
    hind.comp (fun i ↦ fun x : ℝ ↦ x - ∫ ω, X i ω ∂μ)
      (fun _ ↦ measurable_id.sub_const _)
  have hsub : ∀ i ∈ s, HasSubgaussianMGF
      (fun ω ↦ X i ω - ∫ x, X i x ∂μ) ((‖B - 0‖₊ / 2) ^ 2) μ :=
    fun i _ ↦ hasSubgaussianMGF_of_mem_Icc (hmeas i) (hbound i)
  have h := subgaussian_abs_tail (HasSubgaussianMGF.sum_of_iIndepFun hind' hsub) hε
  convert h using 1
  congr 2
  simp only [Finset.sum_const, nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast,
    NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm, sub_zero,
    Real.norm_eq_abs, abs_of_nonneg hB]
  ring

/-- The same concentration bound, centered at the expectation of the actual sum. -/
theorem sum_integral_tail {X : ι → Ω → ℝ} (hind : iIndepFun X μ)
    (hmeas : ∀ i, AEMeasurable (X i) μ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc 0 B)
    (s : Finset ι) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |(∑ i ∈ s, X i ω) - ∫ x, ∑ i ∈ s, X i x ∂μ|} ≤
      2 * Real.exp (-2 * ε ^ 2 / ((s.card : ℝ) * B ^ 2)) := by
  classical
  have hint : ∀ i, Integrable (X i) μ :=
    fun i ↦ Integrable.of_mem_Icc 0 B (hmeas i) (hbound i)
  simpa only [integral_finsetSum s (fun i _ ↦ hint i), Finset.sum_sub_distrib]
    using sum_tail hind hmeas hB hbound s hε

end MajorityDynamics.GraphProcess.RowConcentration.Bounded

/-- info: 'MajorityDynamics.GraphProcess.RowConcentration.Bounded.subgaussian_abs_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.RowConcentration.Bounded.subgaussian_abs_tail

/-- info: 'MajorityDynamics.GraphProcess.RowConcentration.Bounded.sum_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.RowConcentration.Bounded.sum_tail

/-- info: 'MajorityDynamics.GraphProcess.RowConcentration.Bounded.sum_integral_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.RowConcentration.Bounded.sum_integral_tail

