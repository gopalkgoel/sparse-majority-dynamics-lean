import MajorityDynamics.Analysis.GaussianCell

/-! # Checked scalar Gaussian tail and small-interval bounds -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace MajorityDynamics.Analysis

theorem centered_gaussian_tail (v : ℝ≥0) (hv : 0 < v) (R : ℝ) (hR : 0 ≤ R) :
    (gaussianReal 0 v).real {x : ℝ | R ≤ |x|} ≤ 2 * Real.exp (-(R ^ 2) / (2 * (v : ℝ))) := by
  have hv0 : (0 : ℝ) < v := hv
  have hu := measure_ge_le_exp_mul_mgf (X := id) (μ := gaussianReal 0 v) R
    (div_nonneg hR hv0.le) (integrable_exp_mul_gaussianReal (R / v))
  have hd := measure_le_le_exp_mul_mgf (X := id) (μ := gaussianReal 0 v) (-R)
    (neg_nonpos.mpr (div_nonneg hR hv0.le)) (integrable_exp_mul_gaussianReal (-(R / v)))
  have heq : -(R / (v : ℝ)) * R + (v : ℝ) * (R / v) ^ 2 / 2 = -(R ^ 2) / (2 * v) := by
    field_simp
    ring
  have heq' : -(-(R / (v : ℝ))) * (-R) + (v : ℝ) * (-(R / v)) ^ 2 / 2 = -(R ^ 2) / (2 * v) := by
    field_simp
    ring
  simp only [mgf_id_gaussianReal, zero_mul, zero_add, ← Real.exp_add, heq] at hu
  simp only [mgf_id_gaussianReal, zero_mul, zero_add, ← Real.exp_add, heq'] at hd
  have hsub : {x : ℝ | R ≤ |x|} ⊆ {x : ℝ | R ≤ x} ∪ {x : ℝ | x ≤ -R} := by
    intro x hx
    change R ≤ |x| at hx
    rcases le_or_gt 0 x with hx0 | hx0
    · left; simpa [abs_of_nonneg hx0] using hx
    · right
      change x ≤ -R
      rw [abs_of_neg hx0] at hx
      linarith
  have h := (measureReal_mono (μ := gaussianReal 0 v) hsub).trans (measureReal_union_le _ _)
  dsimp only [id_eq] at hu hd
  linarith

theorem gaussian_tail (m : ℝ) (v : ℝ≥0) (hv : 0 < v) (R : ℝ) (hR : 0 ≤ R) :
    (gaussianReal m v).real {x : ℝ | R ≤ |x - m|} ≤ 2 * Real.exp (-(R ^ 2) / (2 * (v : ℝ))) := by
  have h := centered_gaussian_tail v hv R hR
  rw [← sub_self m, ← gaussianReal_map_sub_const m,
    map_measureReal_apply (by fun_prop) (by measurability)] at h
  exact h

theorem gaussian_pdf_le (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal m v x ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
  have he : Real.exp (-((x - m) ^ 2) / (2 * (v : ℝ))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity))
  simpa only [mul_one, gaussianPDFReal] using mul_le_mul_of_nonneg_left he
    (show 0 ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ by positivity)

theorem gaussian_interval_le (m : ℝ) (v : ℝ≥0) (hv : 0 < v) (a b : ℝ) (hab : a ≤ b) :
    (gaussianReal m v).real (Icc a b) ≤ (b - a) / Real.sqrt (2 * Real.pi * (v : ℝ)) := by
  rw [gaussian_real_eq_integral m v hv.ne']
  calc
    _ ≤ ∫ _x in Icc a b, (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ :=
      integral_mono_ae (integrable_gaussianPDFReal m v).integrableOn (integrableOn_const (by simp))
        (ae_of_all _ (gaussian_pdf_le m v))
    _ = _ := by simp [Real.volume_real_Icc, hab, div_eq_mul_inv]

end MajorityDynamics.Analysis
