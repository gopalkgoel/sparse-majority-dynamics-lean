import MajorityDynamics.Probability.ConditionedBinomialFourier.Characteristic
import MajorityDynamics.Probability.ConditionedBinomialFourier.Interval
import MajorityDynamics.Probability.ConditionedBinomialBox.Geometry

noncomputable section
open scoped BigOperators Classical ENNReal
open MeasureTheory MajorityDynamics.Probability.ConditionedBinomialBox
namespace MajorityDynamics.Probability.ConditionedBinomialFourier

variable {d : ℕ}

theorem uniformBox_eq_sum (B : Finset (Fin d → ℕ)) :
    uniformBox B = (B.card : ℝ≥0∞)⁻¹ • ∑ x ∈ B, Measure.dirac x := by
  apply Measure.ext_of_singleton
  intro x
  rw [uniformBox_singleton, Measure.smul_apply, smul_eq_mul,
    Measure.finsetSum_apply]
  simp only [Measure.dirac_apply' _ (measurableSet_singleton x)]
  by_cases hx : x ∈ B <;> simp [hx, one_div]

theorem uniformBox_integral (B : Finset (Fin d → ℕ)) (f : (Fin d → ℕ) → ℂ) :
    (∫ x, f x ∂uniformBox B) = (B.card : ℂ)⁻¹ * ∑ x ∈ B, f x := by
  rw [uniformBox_eq_sum, integral_smul_measure]
  rw [integral_finsetSum_measure (μ := fun x : Fin d → ℕ => Measure.dirac x)]
  · simp [integral_dirac, ENNReal.toReal_inv, Complex.real_smul]
  · intro x _
    exact integrable_dirac (by simp)

theorem phase_eq_prod (t x : Fin d → ℝ) :
    phase t x = ∏ i, Complex.exp (Complex.I * ((t i * x i : ℝ) : ℂ)) := by
  simp [phase, dot, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]

theorem uniformBox_chi_sum (a : Fin d → ℕ) (L : ℕ) (t : Fin d → ℝ) :
    chi (uniformBox (Geometry.box a L)) t =
      (L : ℂ)^(- (d : ℤ)) * ∏ i,
        ∑ k ∈ Finset.Ico (a i) (a i+L), Complex.exp (Complex.I * ((t i * k : ℝ) : ℂ)) := by
  rw [chi, uniformBox_integral]
  simp_rw [phase_eq_prod]
  rw [Geometry.box]
  rw [← Finset.prod_univ_sum (fun i => Finset.Ico (a i) (a i+L))
    (fun i k => Complex.exp (Complex.I * ((t i * k : ℝ) : ℂ)))]
  simp [Fintype.card_piFinset, zpow_neg, zpow_natCast]

theorem interval_sum_shift (a L : ℕ) (t : ℝ) :
    (∑ k ∈ Finset.Ico a (a+L), Complex.exp (Complex.I * ((t*k : ℝ) : ℂ))) =
      Complex.exp (Complex.I * ((t*a : ℝ) : ℂ)) *
        ∑ k : Fin L, Complex.exp (Complex.I * ((t*(k:ℕ) : ℝ) : ℂ)) := by
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left,
    Fin.sum_univ_eq_sum_range (fun k => Complex.exp (Complex.I * ((t*k : ℝ) : ℂ))) L,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem uniformBox_chi (a : Fin d → ℕ) (L : ℕ) (t : Fin d → ℝ) :
    chi (uniformBox (Geometry.box a L)) t =
      phase t (fun i => (a i : ℝ)) * ∏ i, intervalChi L (t i) := by
  rw [uniformBox_chi_sum]
  simp_rw [interval_sum_shift]
  rw [Finset.prod_mul_distrib]
  simp only [intervalChi, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, zpow_neg, zpow_natCast, phase_eq_prod]
  ring

theorem uniformBox_chi_norm_le_coordinate (a : Fin d → ℕ) {L : ℕ}
    (hL : 1 ≤ L) (t : Fin d → ℝ) (i : Fin d) :
    ‖chi (uniformBox (Geometry.box a L)) t‖ ≤ ‖intervalChi L (t i)‖ := by
  rw [uniformBox_chi, norm_mul, phase_norm, one_mul, norm_prod,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hrest : (∏ j ∈ Finset.univ.erase i, ‖intervalChi L (t j)‖) ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun j _ => intervalChi_norm_le_one hL (t j))
  simpa using mul_le_mul_of_nonneg_left hrest (norm_nonneg (intervalChi L (t i)))

theorem exists_abs_eq_norm (hd : 1 ≤ d) (t : Fin d → ℝ) :
    ∃ i : Fin d, |t i| = ‖t‖ := by
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  simpa [Real.norm_eq_abs] using (IsGreatest.pi_norm t).1

theorem uniformBox_chi_norm_gap (a : Fin d → ℕ) {L : ℕ}
    (hL : 16 ≤ L) (hd : 1 ≤ d) (t : Fin d → ℝ) (ht : ∀ i, |t i| ≤ Real.pi) :
    ‖chi (uniformBox (Geometry.box a L)) t‖ ≤
      1 - intervalConstant * min ((L:ℝ)^2 * ‖t‖^2) 1 := by
  obtain ⟨i, hi⟩ := exists_abs_eq_norm hd t
  have hs : (t i)^2 = ‖t‖^2 := by rw [← hi, sq_abs]
  exact (uniformBox_chi_norm_le_coordinate a (by omega) t i).trans
    (by simpa [hs] using intervalChi_norm_gap hL (ht i))

end MajorityDynamics.Probability.ConditionedBinomialFourier
