import MajorityDynamics.Probability.FixedDegreeSampling.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace MajorityDynamics.Probability.FixedDegreeSampling
variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

theorem uniform_apply (s t : Set Ω) :
    uniformOn s t = ((s ∩ t).ncard : ℝ≥0∞) / s.ncard := by
  rw [uniformOn, cond_apply (Set.toFinite s).measurableSet]
  simp only [Measure.count_apply_finite _ (Set.toFinite _)]
  simp only [Set.Finite.toFinset]
  rw [Set.ncard_eq_toFinset_card' s, Set.ncard_eq_toFinset_card' (s ∩ t)]
  rw [div_eq_mul_inv, mul_comm]
  simp only [Set.toFinset_card, ← Nat.card_eq_fintype_card]

theorem uniform_singleton (s : Set Ω) (x : Ω) :
    uniformOn s {x} = if x ∈ s then (s.ncard : ℝ≥0∞)⁻¹ else 0 := by
  rw [uniform_apply]
  by_cases hx : x ∈ s
  · rw [Set.inter_singleton_of_mem hx]; simp [hx]
  · rw [Set.inter_singleton_eq_empty.mpr hx]; simp [hx]

theorem uniform_integral (s : Set Ω) (f : Ω → ℝ) :
    ∫ x, f x ∂uniformOn s = (∑ x ∈ s.toFinset, f x) / (s.ncard : ℝ) := by
  have hf : Integrable f (uniformOn s) := by
    simp
  rw [integral_fintype hf]
  simp only [Measure.real, uniform_singleton, apply_ite, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_zero, smul_eq_mul, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  rw [← Finset.mul_sum]
  rw [div_eq_mul_inv, mul_comm]
  congr 2
  ext x
  simp

/-- Constant positive singleton weights on a finite event imply the uniform conditional law. -/
theorem conditional_eq_uniform (μ : Measure Ω) [IsFiniteMeasure μ] (s : Set Ω)
    (hs : s.Nonempty) (c : ℝ≥0∞) (hc : c ≠ 0)
    (hw : ∀ x ∈ s, μ {x} = c) :
    0 < μ s ∧ cond μ s = uniformOn s := by
  obtain ⟨x, hx⟩ := hs
  have hct : c ≠ ∞ := by rw [← hw x hx]; exact measure_ne_top _ _
  have hr : μ.restrict s = c • Measure.count.restrict s := by
    apply Measure.ext_of_singleton
    intro y
    by_cases hy : y ∈ s
    · simp [Measure.restrict_apply, Set.singleton_inter_of_mem hy, hw y hy]
    · simp [Measure.restrict_apply, Set.singleton_inter_eq_empty.mpr hy]
  have hm : μ s = c * (s.ncard : ℝ≥0∞) := by
    have he := congrArg (fun ν : Measure Ω => ν Set.univ) hr
    simpa [Measure.count_apply_finite _ (Set.toFinite s), Set.Finite.toFinset,
      Set.ncard_eq_toFinset_card'] using he
  have hn : (s.ncard : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Set.ncard_pos (Set.toFinite s) |>.mpr ⟨x, hx⟩).ne'
  refine ⟨by rw [hm]; exact pos_iff_ne_zero.mpr (mul_ne_zero hc hn), ?_⟩
  unfold ProbabilityTheory.cond uniformOn
  rw [hm, hr, smul_smul, ENNReal.mul_inv, mul_assoc, mul_comm ((s.ncard : ℝ≥0∞)⁻¹),
    ← mul_assoc, ENNReal.inv_mul_cancel hc hct, one_mul]
  · congr 1
    simp only [Measure.count_apply_finite _ (Set.toFinite s), Set.Finite.toFinset,
      Set.ncard_eq_toFinset_card', Set.toFinset_card, ← Nat.card_eq_fintype_card]
  · exact Or.inl hc
  · exact Or.inl hct

end MajorityDynamics.Probability.FixedDegreeSampling
