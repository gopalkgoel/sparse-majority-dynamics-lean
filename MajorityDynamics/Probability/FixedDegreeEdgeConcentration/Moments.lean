import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

/-! Finite indicator moments and an actual-measure Chebyshev bound. The pair
hypothesis is required only for distinct indices; no independence is assumed. -/
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace MajorityDynamics.Probability.FixedDegreeEdgeConcentration

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

def atomExpectation (P : Ω → ℝ) (f : Ω → ℝ) : ℝ := ∑ ω, P ω * f ω

def eventIndicator (A : Ω → Prop) (ω : Ω) : ℝ := by
  classical
  exact if A ω then 1 else 0

def eventMass (P : Ω → ℝ) (A : Ω → Prop) : ℝ :=
  atomExpectation P (eventIndicator A)

def indicatorCount (A : ι → Ω → Prop) (ω : Ω) : ℝ :=
  ∑ i, eventIndicator (A i) ω

theorem expectation_indicatorCount (P : Ω → ℝ) (A : ι → Ω → Prop) :
    atomExpectation P (indicatorCount A) = ∑ i, eventMass P (A i) := by
  simp only [atomExpectation, indicatorCount, eventMass, Finset.mul_sum]
  exact Finset.sum_comm

omit [Fintype Ω] in
theorem indicator_joint (A B : Ω → Prop) (ω : Ω) :
    eventIndicator A ω * eventIndicator B ω = eventIndicator (fun ω => A ω ∧ B ω) ω := by
  classical
  simp only [eventIndicator]
  split_ifs <;> simp_all

theorem second_moment_identity (P : Ω → ℝ) (A : ι → Ω → Prop) :
    atomExpectation P (fun ω => indicatorCount A ω ^ 2) =
      ∑ i, ∑ j, eventMass P (fun ω => A i ω ∧ A j ω) := by
  simp only [atomExpectation, indicatorCount, pow_two, Finset.sum_mul, Finset.mul_sum,
    eventMass]
  simp_rw [← mul_assoc, mul_assoc (P _), indicator_joint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  simp only [and_comm]

theorem expectation_bias (P : Ω → ℝ) (A : ι → Ω → Prop) (w : ι → ℝ) (δ : ℝ)
    (hmarg : ∀ i, |eventMass P (A i) - w i| ≤ δ * w i) :
    |atomExpectation P (indicatorCount A) - ∑ i, w i| ≤ δ * ∑ i, w i := by
  rw [expectation_indicatorCount, ← Finset.sum_sub_distrib, Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hmarg i)

theorem second_moment_upper (P : Ω → ℝ) (A : ι → Ω → Prop) (w : ι → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hw : ∀ i, 0 ≤ w i)
    (hpair : ∀ i j, i ≠ j → eventMass P (fun ω => A i ω ∧ A j ω) ≤
      (1 + δ) * w i * w j) :
    atomExpectation P (fun ω => indicatorCount A ω ^ 2) ≤
      atomExpectation P (indicatorCount A) + (1 + δ) * (∑ i, w i) ^ 2 := by
  classical
  rw [second_moment_identity, expectation_indicatorCount]
  calc
    _ ≤ ∑ i, ∑ j, ((if i = j then eventMass P (A i) else 0) +
        (1 + δ) * w i * w j) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hij : i = j
      · subst j
        simp only [and_self]
        exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by linarith) (hw i)) (hw i))
      · simpa [hij] using hpair i j hij
    _ = _ := by simp [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, pow_two, mul_assoc]

theorem centered_second_moment (P : Ω → ℝ) (A : ι → Ω → Prop) (w : ι → ℝ) (δ : ℝ)
    (hP : ∑ ω, P ω = 1) (hδ : 0 ≤ δ) (hw : ∀ i, 0 ≤ w i)
    (hmarg : ∀ i, |eventMass P (A i) - w i| ≤ δ * w i)
    (hpair : ∀ i j, i ≠ j → eventMass P (fun ω => A i ω ∧ A j ω) ≤
      (1 + δ) * w i * w j) :
    atomExpectation P (fun ω => (indicatorCount A ω - ∑ i, w i) ^ 2) ≤
      (1 + δ) * (∑ i, w i) + 3 * δ * (∑ i, w i) ^ 2 := by
  have hW : 0 ≤ ∑ i, w i := Finset.sum_nonneg fun i _ => hw i
  have hb := abs_le.mp (expectation_bias P A w δ hmarg)
  have h2 := second_moment_upper P A w δ hδ hw hpair
  have hid : atomExpectation P (fun ω => (indicatorCount A ω - ∑ i, w i) ^ 2) =
      atomExpectation P (fun ω => indicatorCount A ω ^ 2) -
      2 * (∑ i, w i) * atomExpectation P (indicatorCount A) + (∑ i, w i) ^ 2 := by
    unfold atomExpectation
    simp_rw [sub_sq, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp_rw [show ∀ ω, P ω * (2 * indicatorCount A ω * ∑ i, w i) =
      (2 * ∑ i, w i) * (P ω * indicatorCount A ω) by intro ω; ring]
    rw [← Finset.mul_sum, ← Finset.sum_mul, hP, one_mul]
  rw [hid]
  have hlow := mul_le_mul_of_nonneg_left hb.1 hW
  nlinarith

theorem atom_markov_square (P : Ω → ℝ) (f : Ω → ℝ) (t : ℝ)
    (hP : ∀ ω, 0 ≤ P ω) (ht : 0 < t) :
    eventMass P (fun ω => t ≤ |f ω|) ≤ atomExpectation P (fun ω => f ω ^ 2) / t ^ 2 := by
  classical
  apply (le_div_iff₀ (sq_pos_of_pos ht)).2
  unfold eventMass atomExpectation
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : t ≤ |f ω|
  · simp only [eventIndicator, if_pos h, mul_one]
    apply mul_le_mul_of_nonneg_left _ (hP ω)
    nlinarith [sq_abs (f ω)]
  · simp only [eventIndicator, if_neg h, mul_zero, zero_mul]
    exact mul_nonneg (hP ω) (sq_nonneg _)

theorem shifted_second_moment (P : Ω → ℝ) (f : Ω → ℝ) (W c : ℝ)
    (hP : ∀ ω, 0 ≤ P ω) (hprob : ∑ ω, P ω = 1) :
    atomExpectation P (fun ω => (f ω - c) ^ 2) ≤
      2 * atomExpectation P (fun ω => (f ω - W) ^ 2) + 2 * (W - c) ^ 2 := by
  calc
    _ ≤ ∑ ω, P ω * (2 * (f ω - W) ^ 2 + 2 * (W - c) ^ 2) := by
      apply Finset.sum_le_sum
      intro ω _
      apply mul_le_mul_of_nonneg_left _ (hP ω)
      nlinarith [sq_nonneg (f ω - W - (W - c))]
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, atomExpectation]
      simp_rw [show ∀ ω, P ω * (2 * (f ω - W) ^ 2) =
        2 * (P ω * (f ω - W) ^ 2) by intro ω; ring]
      rw [← Finset.mul_sum, ← Finset.sum_mul, hprob, one_mul]

theorem indicator_tail (P : Ω → ℝ) (A : ι → Ω → Prop) (w : ι → ℝ) (δ c t : ℝ)
    (hP : ∀ ω, 0 ≤ P ω) (hprob : ∑ ω, P ω = 1) (hδ : 0 ≤ δ)
    (hw : ∀ i, 0 ≤ w i) (ht : 0 < t)
    (hmarg : ∀ i, |eventMass P (A i) - w i| ≤ δ * w i)
    (hpair : ∀ i j, i ≠ j → eventMass P (fun ω => A i ω ∧ A j ω) ≤
      (1 + δ) * w i * w j) :
    eventMass P (fun ω => t ≤ |indicatorCount A ω - c|) ≤
      (2 * ((1 + δ) * (∑ i, w i) + 3 * δ * (∑ i, w i) ^ 2) +
        2 * ((∑ i, w i) - c) ^ 2) / t ^ 2 := by
  refine (atom_markov_square P (fun ω => indicatorCount A ω - c) t hP ht).trans ?_
  apply div_le_div_of_nonneg_right _ (sq_nonneg t)
  have h1 := shifted_second_moment P (indicatorCount A) (∑ i, w i) c hP hprob
  have h2 := centered_second_moment P A w δ hprob hδ hw hmarg hpair
  linarith

section Measure
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

theorem eventMass_atoms (μ : Measure Ω) [IsFiniteMeasure μ] (A : Ω → Prop) :
    eventMass (fun ω => μ.real {ω}) A = μ.real {ω | A ω} := by
  classical
  simp only [eventMass, atomExpectation, eventIndicator, mul_ite, mul_one, mul_zero,
    ← Finset.sum_filter]
  rw [sum_measureReal_singleton]
  congr 1
  ext ω
  simp

theorem atoms_sum_one (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∑ ω, μ.real {ω} = 1 := by
  simpa only [Finset.coe_univ, measureReal_def, measure_univ, ENNReal.toReal_one] using
    sum_measureReal_singleton (μ := μ) (Finset.univ : Finset Ω)

theorem measure_indicator_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ι → Ω → Prop) (w : ι → ℝ) (δ c t : ℝ)
    (hδ : 0 ≤ δ) (hw : ∀ i, 0 ≤ w i) (ht : 0 < t)
    (hmarg : ∀ i, |μ.real {ω | A i ω} - w i| ≤ δ * w i)
    (hpair : ∀ i j, i ≠ j → μ.real {ω | A i ω ∧ A j ω} ≤
      (1 + δ) * w i * w j) :
    μ.real {ω | t ≤ |indicatorCount A ω - c|} ≤
      (2 * ((1 + δ) * (∑ i, w i) + 3 * δ * (∑ i, w i) ^ 2) +
        2 * ((∑ i, w i) - c) ^ 2) / t ^ 2 := by
  have h := indicator_tail (fun ω => μ.real {ω}) A w δ c t
    (fun ω => measureReal_nonneg) (atoms_sum_one μ) hδ hw ht
    (by simpa only [eventMass_atoms] using hmarg)
    (by simpa only [eventMass_atoms] using hpair)
  simpa only [eventMass_atoms] using h

end Measure
end MajorityDynamics.Probability.FixedDegreeEdgeConcentration
