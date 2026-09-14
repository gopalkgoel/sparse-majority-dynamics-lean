import MajorityDynamics.Analysis.ConditionalGaussian.Basic
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Uniform coercivity of the tilted Gaussian potential

Source: `latest/main.tex`, the moving-ball argument in `thm:orthant-bijection`.
The lower bound only uses a ball inside the open conditioning set, a positive
minimum of the centered weight on a compact ball, and translation invariance
of volume. It applies to unbounded conditioning sets and arbitrary covariance
matrices whenever the explicitly supplied partition facts hold.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Topology ContDiff

namespace MajorityDynamics.Analysis.ConditionalGaussian

variable {d : ℕ}

/-- The forward ball used in the paper lies both in a fixed ball and in a
strict half-space in its unit direction. -/
theorem shiftedBall_subset_and_inner (y e : Space d) {η : ℝ} (hη : 0 < η)
    (he : ‖e‖ = 1) :
    Metric.ball (y + (3 / 2 * η) • e) (η / 2) ⊆ Metric.ball y (2 * η) ∧
      ∀ x ∈ Metric.ball (y + (3 / 2 * η) • e) (η / 2), η < ⟪x - y, e⟫ := by
  let z := y + (3 / 2 * η) • e
  have hz : dist z y = 3 / 2 * η := by
    simp [z, dist_eq_norm, norm_smul, he, abs_of_pos hη]
  constructor
  · intro x hx
    have hx' : dist x z < η / 2 := hx
    have := dist_triangle x z y
    change dist x y < 2 * η
    linarith
  · intro x hx
    have hx' : ‖x - z‖ < η / 2 := by
      simpa only [dist_eq_norm] using (show dist x z < η / 2 from hx)
    have hlower : -‖x - z‖ ≤ ⟪x - z, e⟫ := by
      simpa only [he, mul_one] using neg_le_of_abs_le (abs_real_inner_le_norm (x - z) e)
    have hsplit : x - y = (x - z) + (3 / 2 * η) • e := by
      dsimp [z]
      abel
    rw [hsplit, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he]
    norm_num
    linarith

/-- A fixed positive lower bound for the centered Gaussian weight on a compact
ball. Positive definiteness is unnecessary for this local assertion. -/
theorem exists_positive_weight_lowerBound_closedBall (S : Covariance d)
    (y : Space d) (r : ℝ) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ Metric.closedBall y r, m ≤ weight S 0 x := by
  have hcont : Continuous (weight S (0 : Space d)) := by
    unfold weight exponent
    fun_prop
  exact (isCompact_closedBall y r).exists_forall_le' hcont.continuousOn
    (fun x _ => Real.exp_pos (exponent S 0 x))

/-- The open-set ball argument gives a linear lower bound, uniform in every
natural-parameter direction. Only the named partition inputs are assumed. -/
theorem coerciveAt_of_partitionFacts (S : Covariance d) (O : Set (Space d))
    (hO : IsOpen O) (hpart : PartitionFacts S O) {y : Space d} (hy : y ∈ O) :
    CoerciveAt S O y := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO y hy
  let η := r / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hball' : Metric.ball y (2 * η) ⊆ O := by
    have heq : 2 * η = r := by dsimp [η]; ring
    rwa [heq]
  obtain ⟨c, hc, hc_bound⟩ := exists_positive_weight_lowerBound_closedBall S y (2 * η)
  let m := c * volume.real (Metric.ball (0 : Space d) (η / 2))
  have hvol : 0 < volume.real (Metric.ball (0 : Space d) (η / 2)) := by
    exact ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos volume 0 (by positivity)))
      measure_ball_lt_top.ne
  have hm : 0 < m := mul_pos hc hvol
  refine ⟨η, hη, min (Real.log m) (logPartition S O 0), ?_⟩
  intro θ
  by_cases hθ : θ = 0
  · simpa only [hθ, norm_zero, mul_zero, inner_zero_left, sub_zero, zero_add] using
      (min_le_right (Real.log m) (logPartition S O 0))
  let e := NormedSpace.normalize θ
  let z := y + (3 / 2 * η) • e
  let B := Metric.ball z (η / 2)
  have he : ‖e‖ = 1 := NormedSpace.norm_normalize hθ
  obtain ⟨hsub, hinner⟩ := shiftedBall_subset_and_inner y e hη he
  have hBO : B ⊆ O := hsub.trans hball'
  have hBc : ∀ x ∈ B, c ≤ weight S 0 x := by
    intro x hx
    exact hc_bound x (Metric.ball_subset_closedBall (hsub hx))
  have hBinner : ∀ x ∈ B, ⟪θ, y⟫ + η * ‖θ‖ ≤ ⟪θ, x⟫ := by
    intro x hx
    have hscaled := mul_le_mul_of_nonneg_left (hinner x hx).le (norm_nonneg θ)
    have heq : ⟪θ, x - y⟫ = ‖θ‖ * ⟪x - y, e⟫ := by
      calc
        ⟪θ, x - y⟫ = ⟪‖θ‖ • e, x - y⟫ := by
          rw [show ‖θ‖ • e = θ from NormedSpace.norm_smul_normalize θ]
        _ = ‖θ‖ * ⟪x - y, e⟫ := by
          rw [real_inner_smul_left, real_inner_comm e (x - y)]
    rw [← heq, inner_sub_right] at hscaled
    linarith
  have hweight : ∀ x ∈ B,
      Real.exp (⟪θ, y⟫ + η * ‖θ‖) * c ≤ weight S θ x := by
    intro x hx
    have hfactor : weight S θ x = Real.exp ⟪θ, x⟫ * weight S 0 x := by
      unfold weight exponent
      simp only [inner_zero_left, zero_sub]
      rw [sub_eq_add_neg, Real.exp_add]
    rw [hfactor]
    exact mul_le_mul (Real.exp_le_exp.mpr (hBinner x hx)) (hBc x hx) hc.le
      (Real.exp_pos _).le
  have hBint : IntegrableOn (weight S θ) B volume :=
    IntegrableOn.mono_set (hpart.integrable_weight θ) hBO
  have hlower : Real.exp (⟪θ, y⟫ + η * ‖θ‖) * m ≤ partition S O θ := by
    calc
      Real.exp (⟪θ, y⟫ + η * ‖θ‖) * m =
          (Real.exp (⟪θ, y⟫ + η * ‖θ‖) * c) * volume.real B := by
        dsimp [m, B]
        rw [Measure.addHaar_real_ball_center volume z (η / 2)]
        ring
      _ ≤ ∫ x in B, weight S θ x :=
        setIntegral_ge_of_const_le_real measurableSet_ball measure_ball_lt_top.ne hweight hBint
      _ ≤ partition S O θ :=
        setIntegral_mono_set (hpart.integrable_weight θ)
          (Filter.Eventually.of_forall (fun x => (Real.exp_pos (exponent S θ x)).le))
          (Filter.Eventually.of_forall hBO)
  have hlog := Real.log_le_log (mul_pos (Real.exp_pos _) hm) hlower
  rw [Real.log_mul (Real.exp_ne_zero _) hm.ne', Real.log_exp] at hlog
  have hb := min_le_left (Real.log m) (logPartition S O 0)
  change η * ‖θ‖ + min (Real.log m) (logPartition S O 0) ≤
    Real.log (partition S O θ) - ⟪θ, y⟫
  linarith

end MajorityDynamics.Analysis.ConditionalGaussian
