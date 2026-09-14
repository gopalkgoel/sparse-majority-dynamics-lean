import MajorityDynamics.Analysis.ConditionalGaussian.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Surjectivity from coercivity of the tilted potential

Source: `latest/main.tex`, the surjectivity argument in `thm:orthant-bijection`.
The analytic inputs are the explicitly named `LogPartitionFacts` and
`CoerciveAt` interfaces; no bijectivity theorem is assumed.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Topology ContDiff

namespace MajorityDynamics.Analysis.ConditionalGaussian

variable {d : ℕ}

/-- A continuous potential with a positive linear lower bound has a local
minimum, obtained in the interior of a sufficiently large closed ball. -/
theorem exists_isLocalMin_of_linear_lowerBound {f : Space d → ℝ}
    (hf : Continuous f) {a b : ℝ} (ha : 0 < a)
    (hbound : ∀ θ, a * ‖θ‖ + b ≤ f θ) : ∃ θ, IsLocalMin f θ := by
  obtain ⟨R, hR⟩ := exists_gt (max 0 ((f 0 - b) / a))
  have hRpos : 0 < R := lt_of_le_of_lt (le_max_left _ _) hR
  have hRlarge : f 0 < a * R + b := by
    have := (div_lt_iff₀ ha).mp (lt_of_le_of_lt (le_max_right _ _) hR)
    nlinarith
  have hzero : (0 : Space d) ∈ Metric.closedBall 0 R := by
    simp only [Metric.mem_closedBall, dist_self]
    exact hRpos.le
  obtain ⟨θ, hθ, hmin⟩ := (isCompact_closedBall (0 : Space d) R).exists_isMinOn
    ⟨0, hzero⟩ hf.continuousOn
  have hinterior : θ ∈ Metric.ball (0 : Space d) R := by
    simp only [Metric.mem_ball, dist_zero_right]
    by_contra h
    have hnorm : R ≤ ‖θ‖ := le_of_not_gt h
    have hmul := mul_le_mul_of_nonneg_left hnorm ha.le
    have hcenter : f θ ≤ f 0 := hmin hzero
    have hθbound := hbound θ
    linarith
  exact ⟨θ, hmin.isLocalMin (Filter.mem_of_superset
    (Metric.isOpen_ball.mem_nhds hinterior) Metric.ball_subset_closedBall)⟩

/-- Coercivity and the log-partition gradient identity imply that every point
of the conditioning set is a natural-parameter mean. -/
theorem meanSurjective_of_coerciveAt (S : Covariance d) (O : Set (Space d))
    (hlog : LogPartitionFacts S O) (hcoercive : ∀ y ∈ O, CoerciveAt S O y) :
    MeanSurjective S O := by
  intro y hy
  obtain ⟨a, ha, b, hbound⟩ := hcoercive y hy
  let Ψ : Space d → ℝ := fun θ => logPartition S O θ - ⟪y, θ⟫
  have hΨcont : Continuous Ψ :=
    hlog.smooth_logPartition.continuous.sub (continuous_const.inner continuous_id)
  have hΨbound : ∀ θ, a * ‖θ‖ + b ≤ Ψ θ := by
    intro θ
    simpa only [Ψ, real_inner_comm y θ] using hbound θ
  obtain ⟨θ, hmin⟩ := exists_isLocalMin_of_linear_lowerBound hΨcont ha hΨbound
  have hderiv : HasFDerivAt Ψ
      (InnerProductSpace.toDual ℝ (Space d) (naturalMean S O θ) -
        InnerProductSpace.toDual ℝ (Space d) y) θ :=
    (hlog.hasGradientAt θ).hasFDerivAt.sub
      (InnerProductSpace.toDual ℝ (Space d) y).hasFDerivAt
  have heq := sub_eq_zero.mp (hmin.hasFDerivAt_eq_zero hderiv)
  exact ⟨θ, (InnerProductSpace.toDual ℝ (Space d)).injective heq⟩

end MajorityDynamics.Analysis.ConditionalGaussian
