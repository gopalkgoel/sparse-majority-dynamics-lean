import MajorityDynamics.Idealized.Logit
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! The uniform derivative-scale estimate for the exact logit tilt used in
Step 3 of Theorem 5.2. The factor is proportional to `p / sqrt(pN)`, which
turns a normalized-mean error into the required probability error of order
`log(N)^L / N`. -/

noncomputable section
open Set Filter Topology
open scoped BigOperators

namespace MajorityDynamics.Idealized.Process

theorem odds_fraction_lipschitz (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |a / (1 + a) - b / (1 + b)| ≤ |a - b| := by
  have hda : 0 < 1 + a := by linarith
  have hdb : 0 < 1 + b := by linarith
  have he : a / (1 + a) - b / (1 + b) = (a - b) / ((1 + a) * (1 + b)) := by
    field_simp
    ring
  rw [he, abs_div, abs_of_pos (mul_pos hda hdb)]
  apply (div_le_iff₀ (mul_pos hda hdb)).mpr
  have hden : 1 ≤ (1 + a) * (1 + b) := by nlinarith [mul_nonneg ha hb]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hden (abs_nonneg (a - b))

theorem exp_lipschitz_bounded (a b R : ℝ) (ha : a ≤ R) (hb : b ≤ R) :
    |Real.exp a - Real.exp b| ≤ Real.exp R * |a - b| := by
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := Real.exp) (s := Iic R) (C := Real.exp R)
    (fun x _ => Real.differentiableAt_exp)
    (fun x hx => by
      rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
      exact Real.exp_le_exp.mpr hx)
    (convex_Iic R) hb ha
  simpa only [Real.norm_eq_abs] using hh

/-- The exact probability tilt is locally Lipschitz with the correct sparse
factor, uniformly for all means in a fixed coordinate interval. -/
theorem logitTilt_lipschitz (N : ℕ) (p : Binomial.Probability)
    (v R g h : ℝ) (hv : 0 < v) (hR : 0 ≤ R)
    (hp : (p : ℝ) ≤ 1 / 2) (hs : 1 ≤ Real.sqrt ((p : ℝ) * N))
    (hg : |g| ≤ R) (hh : |h| ≤ R) :
    |(logitTilt N p g v : ℝ) - (logitTilt N p h v : ℝ)| ≤
      (2 * Real.exp (R / v) / v) * ((p : ℝ) / Real.sqrt ((p : ℝ) * N)) * |g - h| := by
  let a := Real.sqrt ((p : ℝ) * N)
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one hs
  have hpden : 0 < 1 - (p : ℝ) := sub_pos.mpr p.property.2
  have ho : 0 ≤ (p : ℝ) / (1 - (p : ℝ)) := div_nonneg p.property.1.le hpden.le
  have hodds : (p : ℝ) / (1 - (p : ℝ)) ≤ 2 * (p : ℝ) := by
    apply (div_le_iff₀ hpden).mpr
    nlinarith [p.property.1]
  have hg' : g / (v * a) ≤ R / v := by
    apply (div_le_iff₀ (mul_pos hv ha)).mpr
    have hga := (le_abs_self g).trans hg
    have hRa : R ≤ R * a := by nlinarith
    calc
      g ≤ R := hga
      _ ≤ R * a := hRa
      _ = R / v * (v * a) := by field_simp
  have hh' : h / (v * a) ≤ R / v := by
    apply (div_le_iff₀ (mul_pos hv ha)).mpr
    have hha := (le_abs_self h).trans hh
    have hRa : R ≤ R * a := by nlinarith
    calc
      h ≤ R := hha
      _ ≤ R * a := hRa
      _ = R / v * (v * a) := by field_simp
  rw [logitTilt_formula, logitTilt_formula]
  calc
    _ ≤ |(p : ℝ) / (1 - (p : ℝ)) * Real.exp (g / (v * a)) -
        (p : ℝ) / (1 - (p : ℝ)) * Real.exp (h / (v * a))| :=
      odds_fraction_lipschitz _ _ (by positivity) (by positivity)
    _ = ((p : ℝ) / (1 - (p : ℝ))) *
        |Real.exp (g / (v * a)) - Real.exp (h / (v * a))| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg ho]
    _ ≤ (2 * (p : ℝ)) * (Real.exp (R / v) * |g / (v * a) - h / (v * a)|) :=
      mul_le_mul hodds (exp_lipschitz_bounded _ _ _ hg' hh')
        (abs_nonneg _) (mul_nonneg (by norm_num) p.property.1.le)
    _ = (2 * Real.exp (R / v) / v) * ((p : ℝ) / a) * |g - h| := by
      rw [← sub_div, abs_div, abs_of_pos (mul_pos hv ha)]
      ring

/-- Cancellation of the two Gaussian scales in the tilt error. -/
theorem logitTilt_error (N : ℕ) (p : Binomial.Probability)
    (v R g h C A : ℝ) (hv : 0 < v) (hR : 0 ≤ R) (_hC : 0 ≤ C) (_hA : 0 ≤ A)
    (hp : (p : ℝ) ≤ 1 / 2) (hs : 1 ≤ Real.sqrt ((p : ℝ) * N))
    (hg : |g| ≤ R) (hh : |h| ≤ R)
    (hgh : |g - h| ≤ C * A / Real.sqrt ((p : ℝ) * N)) :
    |(logitTilt N p g v : ℝ) - (logitTilt N p h v : ℝ)| ≤
      (2 * Real.exp (R / v) / v * C) * A / N := by
  have hsc : 0 < Real.sqrt ((p : ℝ) * N) := lt_of_lt_of_le zero_lt_one hs
  have hN : (N : ℝ) ≠ 0 := by
    intro h
    have : Real.sqrt ((p : ℝ) * N) = 0 := by rw [h, mul_zero, Real.sqrt_zero]
    linarith
  have hsq : Real.sqrt ((p : ℝ) * N) ^ 2 = (p : ℝ) * N :=
    Real.sq_sqrt (mul_nonneg p.property.1.le (Nat.cast_nonneg _))
  calc
    _ ≤ (2 * Real.exp (R / v) / v) * ((p : ℝ) / Real.sqrt ((p : ℝ) * N)) * |g - h| :=
      logitTilt_lipschitz N p v R g h hv hR hp hs hg hh
    _ ≤ (2 * Real.exp (R / v) / v) * ((p : ℝ) / Real.sqrt ((p : ℝ) * N)) *
        (C * A / Real.sqrt ((p : ℝ) * N)) :=
      mul_le_mul_of_nonneg_left hgh (mul_nonneg
        (div_nonneg (by positivity) hv.le) (div_nonneg p.property.1.le hsc.le))
    _ = (2 * Real.exp (R / v) / v * C) * A *
        ((p : ℝ) / Real.sqrt ((p : ℝ) * N) ^ 2) := by ring
    _ = (2 * Real.exp (R / v) / v * C) * A * (1 / N) := by
      congr 1
      rw [hsq]
      field_simp [p.property.1.ne']
    _ = (2 * Real.exp (R / v) / v * C) * A / N := by ring

end MajorityDynamics.Idealized.Process
