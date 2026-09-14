import MajorityDynamics.GraphProcess.RowArray.Main

/-! Finite-law truncation with an explicit expectation-bias correction. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace MajorityDynamics.GraphProcess.RowConcentration
namespace Truncation
variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable (μ : Measure Ω) [IsFiniteMeasure μ]

/-- Changing a bounded statistic only on `bad` changes its expectation by
at most its global change bound times the actual probability of `bad`. -/
theorem expectation_bias (F G : Ω → ℝ) (bad : Set Ω) (K : ℝ)
    (hsame : ∀ x, x ∉ bad → F x = G x)
    (hbound : ∀ x, |F x - G x| ≤ K) :
    |(∫ x, F x ∂μ) - ∫ x, G x ∂μ| ≤ K * μ.real bad := by
  rw [← integral_sub Integrable.of_finite Integrable.of_finite]
  calc
    _ ≤ ∫ x, |F x - G x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, bad.indicator (fun _ => K) x ∂μ := by
      apply integral_mono Integrable.of_finite Integrable.of_finite
      intro x
      by_cases hx : x ∈ bad
      · simpa only [Set.indicator_of_mem hx] using hbound x
      · simp [Set.indicator_of_notMem hx, hsame x hx]
    _ = K * μ.real bad := by
      rw [integral_indicator_const K (Set.to_countable _).measurableSet]
      simp [mul_comm]

omit [Fintype Ω] [MeasurableSingletonClass Ω] in
/-- The original centered tail is controlled by the exceptional event and
the centered tail of the genuinely truncated random variable. -/
theorem centered_tail (F G : Ω → ℝ) (bad : Set Ω) (r : ℝ)
    (hsame : ∀ x, x ∉ bad → F x = G x)
    (hbias : |(∫ x, F x ∂μ) - ∫ x, G x ∂μ| ≤ r / 2) :
    μ.real {x | r < |F x - ∫ a, F a ∂μ|} ≤
      μ.real bad + μ.real {x | r / 2 < |G x - ∫ a, G a ∂μ|} := by
  calc
    _ ≤ μ.real (bad ∪ {x | r / 2 < |G x - ∫ a, G a ∂μ|}) := by
      refine measureReal_mono ?_ (by finiteness)
      intro x hx
      by_cases hx' : x ∈ bad
      · exact Or.inl hx'
      · right
        change r < |F x - ∫ a, F a ∂μ| at hx
        change r / 2 < |G x - ∫ a, G a ∂μ|
        have htri := abs_add_le (G x - ∫ a, G a ∂μ)
          ((∫ a, G a ∂μ) - ∫ a, F a ∂μ)
        rw [abs_sub_comm (∫ a, G a ∂μ)] at htri
        rw [hsame x hx'] at hx
        have heq : G x - (∫ a, G a ∂μ) +
            ((∫ a, G a ∂μ) - ∫ a, F a ∂μ) = G x - ∫ a, F a ∂μ := by ring
        rw [heq] at htri
        linarith
    _ ≤ _ := measureReal_union_le _ _

end Truncation
end MajorityDynamics.GraphProcess.RowConcentration
