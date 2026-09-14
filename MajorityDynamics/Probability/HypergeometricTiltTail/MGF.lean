import MajorityDynamics.Probability.FixedSizeExponential.Main

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace MajorityDynamics.Probability.HypergeometricTiltTail
open FixedSizeExponential

/-- Finite fixed-size MGF with no lower size window. -/
theorem fixedSize_mgf_interior {n k : ℕ} (hk0 : 0 < k) (hkn : k < n)
    (a : Fin n → ℝ) (ha : ∀ i, |a i| ≤ 1) :
    fixedSizeExpectation n k (fun ξ => Real.exp (bitLinear a ξ)) ≤
      (Real.sqrt (k : ℝ) / centralAtomConstant) *
        Real.exp (((k : ℝ) / n) * ∑ i, a i +
          ((k : ℝ) / n) * ∑ i, (a i)^2) := by
  let q := centralProbability hk0 hkn
  have hmass : centralAtomConstant / Real.sqrt (k : ℝ) ≤
      (bitProductMeasure n q).real (fixedSizeEventSet n k) := by
    rw [conditioning_event_eq_binomial q hkn.le]
    exact central_binomial_point_mass_lower hk0 hkn
  have hE0 : 0 ≤ fixedSizeExpectation n k (fun ξ => Real.exp (bitLinear a ξ)) :=
    integral_nonneg (fun _ => (Real.exp_pos _).le)
  have hcond := conditional_expectation_mul_le q hkn.le
    (fun ξ => Real.exp (bitLinear a ξ)) (fun _ => (Real.exp_pos _).le)
  have hprod := bitProduct_mgf_bound q a ha
  have hsqrt : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hk0)
  have hc := centralAtomConstant_pos
  have hscaled := (mul_le_mul_of_nonneg_right hmass hE0).trans (hcond.trans hprod)
  have hdiv : fixedSizeExpectation n k (fun ξ => Real.exp (bitLinear a ξ)) ≤
      Real.exp ((q : ℝ) * ∑ i, a i + (q : ℝ) * ∑ i, (a i)^2) /
        (centralAtomConstant / Real.sqrt (k : ℝ)) :=
    (le_div_iff₀ (div_pos hc hsqrt)).2 (by simpa only [mul_comm] using hscaled)
  convert hdiv using 1
  dsimp [q, centralProbability]
  field_simp

/-- The zero-size exponential moment is exactly one. -/
theorem fixedSize_mgf_zero (n : ℕ) (a : Fin n → ℝ) :
    fixedSizeExpectation n 0 (fun ξ => Real.exp (bitLinear a ξ)) = 1 := by
  classical
  rw [fixedSizeExpectation_eq_average (Nat.zero_le _)]
  have hzero : ∀ ξ ∈ fixedSizeEvent n 0, bitLinear a ξ = 0 := by
    intro ξ hξ
    have hc : (bitSet ξ).card = 0 := (Finset.mem_filter.mp hξ).2
    have he : bitSet ξ = ∅ := Finset.card_eq_zero.mp hc
    unfold bitLinear
    apply Finset.sum_eq_zero
    intro i hi
    have hnot : ξ i ≠ true := by
      intro h
      have hm : i ∈ bitSet ξ := by simp [bitSet, h]
      rw [he] at hm
      exact Finset.notMem_empty i hm
    simp [hnot]
  unfold fixedSizeAverage
  simp only [Nat.choose_zero_right, Nat.cast_one, inv_one, one_mul]
  calc
    _ = ∑ _ξ ∈ fixedSizeEvent n 0, (1 : ℝ) :=
      Finset.sum_congr rfl (fun ξ hξ => by rw [hzero ξ hξ, Real.exp_zero])
    _ = 1 := by simp [fixedSizeEvent_card]

/-- The prefactor also accommodates the deterministic empty subset. -/
def mgfPrefactor (k : ℕ) : ℝ := max 1 (Real.sqrt (k : ℝ) / centralAtomConstant)

theorem mgfPrefactor_pos (k : ℕ) : 0 < mgfPrefactor k :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

/-- Every size below the population, including zero. -/
theorem fixedSize_mgf {n k : ℕ} (hkn : k < n)
    (a : Fin n → ℝ) (ha : ∀ i, |a i| ≤ 1) :
    fixedSizeExpectation n k (fun ξ => Real.exp (bitLinear a ξ)) ≤
      mgfPrefactor k * Real.exp (((k : ℝ) / n) * ∑ i, a i +
        ((k : ℝ) / n) * ∑ i, (a i)^2) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp [fixedSize_mgf_zero, mgfPrefactor]
  · exact (fixedSize_mgf_interior hk0 hkn a ha).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)

end MajorityDynamics.Probability.HypergeometricTiltTail
