import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Diagonal Gaussian density calculus

The variance is a real parameter on its positive open domain. This avoids
nondifferentiable coercions through `NNReal.ofReal` in the analytic calculations;
`scalarDensity_eq_gaussianPDFReal` identifies the result with Mathlib's density.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ContDiff NNReal

namespace MajorityDynamics.Analysis.GaussianRegularity

/-- Scalar Gaussian density, expressed on real mean and variance parameters. -/
def scalarDensity (m v x : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(x - m) ^ 2 / (2 * v))

/-- Independent diagonal Gaussian density. -/
def density {d : ℕ} (m v x : Fin d → ℝ) : ℝ :=
  ∏ i, scalarDensity (m i) (v i) (x i)

theorem scalarDensity_eq_gaussianPDFReal (m x : ℝ) (v : ℝ≥0) :
    scalarDensity m v x = gaussianPDFReal m v x := rfl

theorem scalarDensity_pos (m x : ℝ) {v : ℝ} (hv : 0 < v) :
    0 < scalarDensity m v x := by
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))) (Real.exp_pos _)

theorem scalarDensity_nonneg (m v x : ℝ) : 0 ≤ scalarDensity m v x := by
  exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (Real.exp_pos _).le

/-- Joint smoothness of the density in its mean, positive variance and argument. -/
theorem contDiffAt_scalarDensity (p : ℝ × ℝ × ℝ) (hv : 0 < p.2.1) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℝ × ℝ => scalarDensity q.1 q.2.1 q.2.2) p := by
  unfold scalarDensity
  apply ContDiffAt.mul
  · apply ContDiffAt.inv
    · apply ContDiffAt.sqrt
      · fun_prop
      · positivity
    · exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  · apply ContDiffAt.exp
    apply ContDiffAt.div
    · fun_prop
    · fun_prop
    · positivity

/-- The score in the mean coordinate. -/
theorem hasDerivAt_scalarDensity_mean (m v x : ℝ) :
    HasDerivAt (fun a => scalarDensity a v x)
      (((x - m) / v) * scalarDensity m v x) m := by
  have h := ((((hasDerivAt_const m x).sub (hasDerivAt_id m)).pow 2).neg.div_const
    (2 * v)).exp.const_mul ((Real.sqrt (2 * Real.pi * v))⁻¹)
  convert h using 1 <;> try rfl
  dsimp [scalarDensity]
  ring

/-- The score in the variance coordinate, including the normalizing factor. -/
theorem hasDerivAt_scalarDensity_variance (m x : ℝ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun a => scalarDensity m a x)
      ((((x - m) ^ 2 / (2 * v ^ 2)) - 1 / (2 * v)) * scalarDensity m v x) v := by
  have hn : 2 * Real.pi * v ≠ 0 := by positivity
  have hs : Real.sqrt (2 * Real.pi * v) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hnorm := (((hasDerivAt_id v).const_mul (2 * Real.pi)).sqrt hn).inv hs
  have hexp := (((hasDerivAt_const v (-(x - m)^2)).div
    ((hasDerivAt_id v).const_mul 2) (by positivity : 2 * v ≠ 0))).exp
  have h := hnorm.mul hexp
  convert h using 1 <;> try rfl
  dsimp [scalarDensity]
  field_simp
  rw [Real.sq_sqrt (by positivity)]
  ring

/-- A uniform scalar Gaussian envelope on bounded means and a compact positive
variance interval. It is independent of the particular mean and variance. -/
theorem scalarDensity_le_envelope {m v x M a b : ℝ}
    (ha : 0 < a) (hav : a ≤ v) (hvb : v ≤ b) (hm : |m| ≤ M) :
    scalarDensity m v x ≤
      ((Real.sqrt (2 * Real.pi * a))⁻¹ * Real.exp (M ^ 2 / (2 * a))) *
        Real.exp (-x ^ 2 / (4 * b)) := by
  have hv : 0 < v := lt_of_lt_of_le ha hav
  have hb : 0 < b := lt_of_lt_of_le hv hvb
  have hms : m ^ 2 ≤ M ^ 2 := by
    have := sq_le_sq₀ (abs_nonneg m) (le_trans (abs_nonneg m) hm) |>.mpr hm
    simpa only [sq_abs] using this
  have hx : -(x - m) ^ 2 / (2 * v) ≤ m ^ 2 / (2 * v) - x ^ 2 / (4 * v) := by
    apply (mul_le_mul_iff_right₀ (show 0 < 4 * v by positivity)).mp
    field_simp
    nlinarith [sq_nonneg (x - 2*m)]
  have hmdiv : m ^ 2 / (2 * v) ≤ M ^ 2 / (2 * a) := by
    exact div_le_div₀ (sq_nonneg _) hms (by positivity) (by linarith)
  have hxdiv : x ^ 2 / (4 * b) ≤ x ^ 2 / (4 * v) := by
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
  have hex : -(x - m) ^ 2 / (2 * v) ≤ M ^ 2 / (2 * a) + -x ^ 2 / (4 * b) := by
    simp only [neg_div] at hx ⊢
    linarith
  have hnorm : (Real.sqrt (2 * Real.pi * v))⁻¹ ≤ (Real.sqrt (2 * Real.pi * a))⁻¹ := by
    apply inv_anti₀ (Real.sqrt_pos.mpr (by positivity))
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hav (by positivity)
  calc
    scalarDensity m v x ≤ (Real.sqrt (2 * Real.pi * a))⁻¹ *
        Real.exp (M ^ 2 / (2 * a) + -x ^ 2 / (4 * b)) :=
      mul_le_mul hnorm (Real.exp_le_exp.mpr hex) (Real.exp_pos _).le (by positivity)
    _ = _ := by rw [Real.exp_add]; ring

/-- Uniform polynomial bound for the mean score. -/
theorem mean_score_bound {m v x M a : ℝ} (ha : 0 < a) (hav : a ≤ v)
    (hm : |m| ≤ M) :
    |(x - m) / v| ≤ ((1 + M) / a) * (1 + x ^ 2) := by
  have hv : 0 < v := lt_of_lt_of_le ha hav
  have hM : 0 ≤ M := le_trans (abs_nonneg _) hm
  have hx : |x| ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg (|x| - 1), sq_abs x]
  have hnum : |x - m| ≤ (1 + M) * (1 + x ^ 2) := by
    have h := abs_sub x m
    nlinarith [sq_nonneg x]
  rw [abs_div, abs_of_pos hv]
  calc
    |x - m| / v ≤ ((1 + M) * (1 + x ^ 2)) / a :=
      div_le_div₀ (by positivity) hnum ha hav
    _ = _ := by ring

/-- Uniform polynomial bound for the variance score. -/
theorem variance_score_bound {m v x M a : ℝ} (ha : 0 < a) (hav : a ≤ v)
    (hm : |m| ≤ M) :
    |(x - m) ^ 2 / (2 * v ^ 2) - 1 / (2 * v)| ≤
      ((1 + M ^ 2) / a ^ 2 + 1 / (2 * a)) * (1 + x ^ 2) := by
  have hv : 0 < v := lt_of_lt_of_le ha hav
  have hms : m ^ 2 ≤ M ^ 2 := by
    have := (sq_le_sq₀ (abs_nonneg m) (le_trans (abs_nonneg m) hm)).mpr hm
    simpa only [sq_abs] using this
  have hnum : (x - m) ^ 2 ≤ 2 * (1 + M ^ 2) * (1 + x ^ 2) := by
    nlinarith [sq_nonneg (x+m), sq_nonneg x, sq_nonneg M, mul_nonneg (sq_nonneg x) (sq_nonneg M)]
  have hsq : a ^ 2 ≤ v ^ 2 := (sq_le_sq₀ ha.le hv.le).mpr hav
  have hfirst : (x - m) ^ 2 / (2 * v ^ 2) ≤
      ((1 + M ^ 2) / a ^ 2) * (1 + x ^ 2) := by
    calc
      _ ≤ (2 * (1 + M ^ 2) * (1 + x ^ 2)) / (2 * a ^ 2) :=
        div_le_div₀ (by positivity) hnum (by positivity) (by linarith)
      _ = _ := by ring
  have hsecond : 1 / (2 * v) ≤ 1 / (2 * a) := by
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  calc
    _ ≤ (x - m) ^ 2 / (2 * v ^ 2) + 1 / (2 * v) := by
      apply (abs_sub _ _).trans
      rw [abs_of_nonneg (by positivity : 0 ≤ (x - m)^2/(2*v^2)),
        abs_of_nonneg (by positivity : 0 ≤ 1/(2*v))]
    _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ 1/(2*a) by positivity) (sq_nonneg x)]

/-- A single integrable envelope for the density and both parameter derivatives. -/
def envelope (M a b x : ℝ) : ℝ :=
  (1 + (1 + M) / a + ((1 + M ^ 2) / a ^ 2 + 1 / (2 * a))) * (1 + x ^ 2) *
    (((Real.sqrt (2 * Real.pi * a))⁻¹ * Real.exp (M ^ 2 / (2 * a))) *
        Real.exp (-x ^ 2 / (4 * b)))

theorem envelope_nonneg {M a b x : ℝ} (hM : 0 ≤ M) (ha : 0 < a) :
    0 ≤ envelope M a b x := by unfold envelope; positivity

private theorem score_mul_density_le_envelope {m v x M a b c s : ℝ}
    (ha : 0 < a) (hav : a ≤ v) (hvb : v ≤ b) (hm : |m| ≤ M)
    (hs : |s| ≤ c * (1 + x ^ 2))
    (hc : c ≤ 1 + (1 + M) / a + ((1 + M ^ 2) / a ^ 2 + 1 / (2 * a))) :
    |s * scalarDensity m v x| ≤ envelope M a b x := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) hm
  rw [abs_mul, abs_of_nonneg (scalarDensity_nonneg _ _ _)]
  apply mul_le_mul
    (hs.trans (mul_le_mul_of_nonneg_right hc (by positivity)))
    (scalarDensity_le_envelope ha hav hvb hm) (scalarDensity_nonneg _ _ _)
  positivity

theorem scalarDensity_le_common_envelope {m v x M a b : ℝ}
    (ha : 0 < a) (hav : a ≤ v) (hvb : v ≤ b) (hm : |m| ≤ M) :
    |scalarDensity m v x| ≤ envelope M a b x := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) hm
  simpa only [one_mul] using score_mul_density_le_envelope ha hav hvb hm
    (s := 1) (c := 1) (by simp only [abs_one, one_mul]; nlinarith [sq_nonneg x])
    (by
      have h1 : 0 ≤ (1 + M) / a := by positivity
      have h2 : 0 ≤ (1 + M ^ 2) / a ^ 2 + 1 / (2 * a) := by positivity
      linarith)

theorem mean_derivative_le_envelope {m v x M a b : ℝ}
    (ha : 0 < a) (hav : a ≤ v) (hvb : v ≤ b) (hm : |m| ≤ M) :
    |((x - m) / v) * scalarDensity m v x| ≤ envelope M a b x := by
  apply score_mul_density_le_envelope ha hav hvb hm (mean_score_bound ha hav hm)
  have : 0 ≤ (1 + M ^ 2) / a ^ 2 + 1 / (2 * a) := by positivity
  linarith

theorem variance_derivative_le_envelope {m v x M a b : ℝ}
    (ha : 0 < a) (hav : a ≤ v) (hvb : v ≤ b) (hm : |m| ≤ M) :
    |(((x - m) ^ 2 / (2 * v ^ 2)) - 1 / (2 * v)) * scalarDensity m v x| ≤
      envelope M a b x := by
  apply score_mul_density_le_envelope ha hav hvb hm (variance_score_bound ha hav hm)
  have hM : 0 ≤ M := le_trans (abs_nonneg _) hm
  have : 0 ≤ (1 + M) / a := by positivity
  linarith

/-- The same explicit envelope controls joint mean/variance differences. -/
theorem scalarDensity_sub_le_envelope {m m' v v' x M a b : ℝ}
    (ha : 0 < a) (hav : a ≤ v) (hvb : v ≤ b) (hav' : a ≤ v') (hv'b : v' ≤ b)
    (hm : |m| ≤ M) (hm' : |m'| ≤ M) :
    |scalarDensity m v x - scalarDensity m' v' x| ≤
      envelope M a b x * (|m - m'| + |v - v'|) := by
  have hmean : |scalarDensity m v x - scalarDensity m' v x| ≤
      envelope M a b x * |m - m'| := by
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := fun z => scalarDensity z v x)
        (fun z (_ : z ∈ Icc (-M) M) => (hasDerivAt_scalarDensity_mean z v x).hasDerivWithinAt)
        (fun z hz => by simpa only [Real.norm_eq_abs] using
          mean_derivative_le_envelope ha hav hvb (abs_le.mpr hz))
        (convex_Icc (-M) M) (abs_le.mp hm') (abs_le.mp hm)
  have hvar : |scalarDensity m' v x - scalarDensity m' v' x| ≤
      envelope M a b x * |v - v'| := by
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := fun z => scalarDensity m' z x)
        (fun z (hz : z ∈ Icc a b) =>
          (hasDerivAt_scalarDensity_variance m' x (lt_of_lt_of_le ha hz.1)).hasDerivWithinAt)
        (fun z hz => by simpa only [Real.norm_eq_abs] using
          variance_derivative_le_envelope ha hz.1 hz.2 hm')
        (convex_Icc a b) ⟨hav', hv'b⟩ ⟨hav, hvb⟩
  calc
    _ ≤ |scalarDensity m v x - scalarDensity m' v x| +
        |scalarDensity m' v x - scalarDensity m' v' x| := abs_sub_le _ _ _
    _ ≤ _ := by nlinarith

end MajorityDynamics.Analysis.GaussianRegularity
