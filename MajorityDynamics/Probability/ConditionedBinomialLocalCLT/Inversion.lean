import MajorityDynamics.Probability.ConditionedBinomialFourier.Characteristic
import MajorityDynamics.Probability.ConditionedBinomialFourier.HighFrequency
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace MajorityDynamics.Probability.ConditionedBinomialLocalCLT
open ConditionedBinomialFourier
open ConditionedBinomialFourier.HighFrequency

/-- The literal integer lattice sum of the independent copies. -/
def integerSum {d m : ℕ} (x : Fin m → Fin d → ℕ) : Fin d → ℤ :=
  fun i => ∑ j, (x j i : ℤ)

theorem integerSum_cast {d m : ℕ} (x : Fin m → Fin d → ℕ) :
    (fun i => (integerSum x i : ℝ)) = copySum x := by
  ext i
  simp [integerSum, copySum]

theorem integerSum_event_eq {d m : ℕ} (z : Fin d → ℤ) :
    {x : Fin m → Fin d → ℕ | integerSum x = z} =
      {x | copySum x = fun i => (z i : ℝ)} := by
  ext x
  simp only [Set.mem_ofPred_eq, ← integerSum_cast, funext_iff, Int.cast_inj]

/-- Exact one-dimensional harmonic orthogonality, with Lebesgue normalization. -/
theorem integral_integer_harmonic (k : ℤ) :
    (∫ t : ℝ in Set.Icc (-Real.pi) Real.pi,
      Complex.exp (Complex.I * (t : ℂ) * (k : ℂ))) =
      if k = 0 then (2 * Real.pi : ℂ) else 0 := by
  by_cases hk : k = 0
  · subst k
    simp only [Int.cast_zero, mul_zero, Complex.exp_zero, integral_const,
      Measure.real, Measure.restrict_apply_univ, Real.volume_Icc, ite_true]
    rw [ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    rw [Complex.real_smul, mul_one]
    push_cast
    ring
  · rw [if_neg hk, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    have hc : Complex.I * (k : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hk)
    have hmul : (fun t : ℝ => Complex.exp (Complex.I * (t : ℂ) * (k : ℂ))) =
        fun t : ℝ => Complex.exp ((Complex.I * (k : ℂ)) * (t : ℂ)) := by
      ext t; congr 1; ring
    rw [hmul, integral_exp_mul_complex hc]
    have heq : Complex.exp (Complex.I * (k : ℂ) * (Real.pi : ℂ)) =
        Complex.exp (Complex.I * (k : ℂ) * ((-Real.pi : ℝ) : ℂ)) := by
      have h := Complex.exp_int_mul_two_pi_mul_I k
      have hh : Complex.I * (k : ℂ) * (Real.pi : ℂ) =
          (k : ℂ) * (2 * Real.pi * Complex.I) +
            Complex.I * (k : ℂ) * ((-Real.pi : ℝ) : ℂ) := by push_cast; ring
      rw [hh, Complex.exp_add, h, one_mul]
    rw [heq, sub_self, zero_div]


/-- Exact product-cube orthogonality for every integer lattice vector. -/
theorem integral_lattice_phase {d : ℕ} (k : Fin d → ℤ) :
    (∫ t in cube d, phase t (fun i => (k i : ℝ))) =
      if k = 0 then ((2 * Real.pi : ℂ) ^ d) else 0 := by
  have hcube : cube d = Set.univ.pi (fun _ : Fin d => Set.Icc (-Real.pi) Real.pi) := by
    ext t
    simp only [cube, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Icc, abs_le]
  have hphase (t : Fin d → ℝ) : phase t (fun i => (k i : ℝ)) =
      ∏ i, Complex.exp (Complex.I * (t i : ℂ) * (k i : ℂ)) := by
    simp only [phase, dot, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast,
      Finset.mul_sum, ← Complex.exp_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hcube]
  change (∫ t, phase t (fun i => (k i : ℝ)) ∂(Measure.pi (fun _ : Fin d =>
    (volume : Measure ℝ))).restrict (Set.univ.pi (fun _ => Set.Icc (-Real.pi) Real.pi))) = _
  rw [Measure.restrict_pi_pi]
  simp_rw [hphase]
  rw [integral_fintype_prod_eq_prod (fun i (t : ℝ) =>
    Complex.exp (Complex.I * (t : ℂ) * (k i : ℂ)))]
  simp_rw [integral_integer_harmonic]
  by_cases hk : k = 0
  · subst k
    simp
  · rw [if_neg hk]
    obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
      by_contra h
      push Not at h
      exact hk (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)


/-- Fourier inversion for the actual copy law and any integer target. -/
theorem integral_translated_copySum {d : ℕ} (ρ : Measure (Fin d → ℕ))
    [IsProbabilityMeasure ρ] (m : ℕ) (z : Fin d → ℤ) :
    (∫ t in cube d, ∫ x, phase t (copySum x - fun i => (z i : ℝ)) ∂copyLaw ρ m) =
      ((2 * Real.pi : ℂ) ^ d) *
        (((copyLaw ρ m).real {x | integerSum x = z} : ℝ) : ℂ) := by
  let ν : Measure (Fin d → ℝ) := volume.restrict (cube d)
  have : IsFiniteMeasure ν := ⟨by
    simpa [ν] using cube_volume_lt_top d⟩
  have hmeas : Measurable (fun p : (Fin d → ℝ) × (Fin m → Fin d → ℕ) =>
      phase p.1 (copySum p.2 - fun i => (z i : ℝ))) := by
    unfold phase dot copySum
    fun_prop
  have hint : Integrable (fun p : (Fin d → ℝ) × (Fin m → Fin d → ℕ) =>
      phase p.1 (copySum p.2 - fun i => (z i : ℝ))) (ν.prod (copyLaw ρ m)) := by
    refine (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun p => (phase_norm _ _).le
  rw [integral_integral_swap hint]
  have hpoint (x : Fin m → Fin d → ℕ) :
      (∫ t in cube d, phase t (copySum x - fun i => (z i : ℝ))) =
        if integerSum x = z then ((2 * Real.pi : ℂ) ^ d) else 0 := by
    have hvec : (copySum x - fun i => (z i : ℝ)) =
        fun i => ((integerSum x - z) i : ℝ) := by
      rw [← integerSum_cast]
      ext i
      simp
    rw [hvec, integral_lattice_phase]
    simp only [sub_eq_zero]
  simp_rw [hpoint]
  have hind : (fun x : Fin m → Fin d → ℕ =>
      if integerSum x = z then ((2 * Real.pi : ℂ) ^ d) else 0) =
      {x | integerSum x = z}.indicator (fun _ => ((2 * Real.pi : ℂ) ^ d)) := by
    ext x
    simp [Set.indicator]
  rw [hind, integral_indicator (Set.to_countable _).measurableSet, setIntegral_const,
    Complex.real_smul]
  ring

/-- Mean-integrality turns the actual centered characteristic integral into an atom. -/
theorem integral_centeredChi {d : ℕ} (ρ : Measure (Fin d → ℕ))
    [IsProbabilityMeasure ρ] (m : ℕ) (z : Fin d → ℤ)
    (hz : ∀ i, (z i : ℝ) = (m : ℝ) * mean ρ i) :
    (∫ t in cube d, centeredChi ρ m t) =
      ((2 * Real.pi : ℂ) ^ d) *
        (((copyLaw ρ m).real {x | integerSum x = z} : ℝ) : ℂ) := by
  simpa only [centeredChi, hz] using integral_translated_copySum ρ m z


/-- The exact real-valued probability formula used by the lower-bound argument. -/
theorem integerSum_probability {d : ℕ} (ρ : Measure (Fin d → ℕ))
    [IsProbabilityMeasure ρ] (m : ℕ) (z : Fin d → ℤ)
    (hz : ∀ i, (z i : ℝ) = (m : ℝ) * mean ρ i) :
    (copyLaw ρ m).real {x | integerSum x = z} =
      (∫ t in cube d, centeredChi ρ m t).re / (2 * Real.pi) ^ d := by
  have h := congrArg Complex.re (integral_centeredChi ρ m z hz)
  have hc : ((2 * Real.pi : ℂ) ^ d) = (((2 * Real.pi) ^ d : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hc, ← Complex.ofReal_mul, Complex.ofReal_re] at h
  apply (eq_div_iff (pow_ne_zero _ (ne_of_gt (by positivity : 0 < 2 * Real.pi)))).2
  rw [h]
  ring

/-- The integer target event is literally the paper's actual mean event. -/
theorem integerSum_mean_event {d m : ℕ} (ρ : Measure (Fin d → ℕ))
    (z : Fin d → ℤ) (hz : ∀ i, (z i : ℝ) = (m : ℝ) * mean ρ i) :
    {x : Fin m → Fin d → ℕ | integerSum x = z} =
      {x | copySum x = fun i => (m : ℝ) * mean ρ i} := by
  rw [integerSum_event_eq]
  simp only [hz]

/-- A coordinatewise spelling of the exact integer-sum event. -/
theorem integerSum_event_forall {d m : ℕ} (z : Fin d → ℤ) :
    {x : Fin m → Fin d → ℕ | integerSum x = z} =
      {x | ∀ i, (∑ j, (x j i : ℤ)) = z i} := by
  ext x
  simp only [Set.mem_ofPred_eq, funext_iff, integerSum]

/-- Exact inversion directly at the actual mean, assuming it is a lattice point. -/
theorem mean_event_probability {d : ℕ} (ρ : Measure (Fin d → ℕ))
    [IsProbabilityMeasure ρ] (m : ℕ)
    (hz : ∃ z : Fin d → ℤ, ∀ i, (z i : ℝ) = (m : ℝ) * mean ρ i) :
    (copyLaw ρ m).real {x | copySum x = fun i => (m : ℝ) * mean ρ i} =
      (∫ t in cube d, centeredChi ρ m t).re / (2 * Real.pi) ^ d := by
  obtain ⟨z, hz⟩ := hz
  rw [← integerSum_mean_event ρ z hz]
  exact integerSum_probability ρ m z hz

end MajorityDynamics.Probability.ConditionedBinomialLocalCLT
