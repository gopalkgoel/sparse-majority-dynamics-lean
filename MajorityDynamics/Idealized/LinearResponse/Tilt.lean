import MajorityDynamics.Idealized.LinearResponse.Basic
import MajorityDynamics.Binomial.ChangingTrials
import MajorityDynamics.Idealized.Process.TiltEstimates
import MajorityDynamics.Idealized.RowLimits.GeometryLocal

/-! Exact algebra of the effective tilt: the paper's displayed equation, its
identification with the A.2 different-trial tilt parameter, and its form as a
standard sparse logit tilt. -/

noncomputable section
open scoped BigOperators

namespace MajorityDynamics.Idealized.LinearResponse

open MajorityDynamics.Universal
open MajorityDynamics.Idealized (logistic logitTilt)
open MajorityDynamics.Binomial (logOdds)

variable {n : ℕ}

theorem residual_sub (p : ℝ) (ref sizes : Local.Sizes n) (s t : History (n + 1)) :
    residual p ref ref s t - residual p ref sizes s t = (ref t : ℝ) - sizes t := by
  unfold residual
  ring

theorem effectiveTilt_in_unit (N : ℕ) (p : Binomial.Probability) (ref : Local.Sizes n)
    (reference : History (n + 1) → Binomial.Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (τ : ℝ) (σ : Row (n + 1)) (t : History (n + 1)) :
    0 < (effectiveTilt N p ref reference sizes s τ σ t : ℝ) ∧
      (effectiveTilt N p ref reference sizes s τ σ t : ℝ) < 1 :=
  (effectiveTilt N p ref reference sizes s τ σ t).property

/-- The paper's exact effective-tilt equation. -/
theorem effectiveTilt_equation (N : ℕ) (p : Binomial.Probability) (ref : Local.Sizes n)
    (reference : History (n + 1) → Binomial.Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (τ : ℝ) (σ : Row (n + 1)) (t : History (n + 1))
    (href : 0 < residual (p : ℝ) ref ref s t) (hnew : 0 < residual (p : ℝ) ref sizes s t)
    (hcenter : 0 < (p : ℝ) * (ref t : ℝ)) :
    logOdds (effectiveTilt N p ref reference sizes s τ σ t) +
        Real.log (residual (p : ℝ) ref sizes s t / ((p : ℝ) * (ref t : ℝ))) =
      logOdds (reference t) +
        Real.log (residual (p : ℝ) ref ref s t / ((p : ℝ) * (ref t : ℝ))) +
        τ * betaScale N (p : ℝ) n * σ t := by
  rw [logOdds_effectiveTilt, Real.log_div hnew.ne' hcenter.ne', Real.log_div href.ne' hcenter.ne',
    Real.log_div href.ne' hnew.ne']
  ring

theorem trials_gt_center (p : Binomial.Probability) (ref sizes : Local.Sizes n)
    (s t : History (n + 1)) (hres : 0 < residual (p : ℝ) ref sizes s t) :
    0 < sizes t ∧ (p : ℝ) * (ref t : ℝ) < (Local.trials sizes s t : ℝ) := by
  have hres' : 0 < (sizes t : ℝ) - (if s = t then (1 : ℝ) else 0) - (p : ℝ) * (ref t : ℝ) := hres
  have hd : 0 ≤ (if s = t then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have hc : 0 ≤ (p : ℝ) * (ref t : ℝ) := mul_nonneg p.property.1.le (Nat.cast_nonneg _)
  have hpos : (0 : ℝ) < sizes t := by linarith
  have hsz : 0 < sizes t := by exact_mod_cast hpos
  refine ⟨hsz, ?_⟩
  rw [RowLimits.trials_cast sizes s t hsz]
  linarith

/-- The A.2 different-trial tilt vector is exactly `τ β₀ σ`. -/
theorem effectiveTilt_difference (N : ℕ) (p : Binomial.Probability) (ref : Local.Sizes n)
    (reference : History (n + 1) → Binomial.Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (τ : ℝ) (σ : Row (n + 1))
    (href : ∀ t, 0 < residual (p : ℝ) ref ref s t)
    (hnew : ∀ t, 0 < residual (p : ℝ) ref sizes s t) :
    Binomial.Approximation.tiltDifference p ref (Local.trials ref s) (Local.trials sizes s)
        reference (effectiveTilt N p ref reference sizes s τ σ) =
      fun t => τ * betaScale N (p : ℝ) n * σ t := by
  funext t
  obtain ⟨hrefsz, h₀⟩ := trials_gt_center p ref ref s t (href t)
  obtain ⟨hsz, h₁⟩ := trials_gt_center p ref sizes s t (hnew t)
  change Binomial.Approximation.scalarTiltDifference (Local.trials ref s t) (Local.trials sizes s t)
    ((p : ℝ) * (ref t : ℝ)) (reference t) (effectiveTilt N p ref reference sizes s τ σ t) = _
  rw [Binomial.Approximation.scalarTiltDifference_eq h₀ h₁, RowLimits.trials_cast ref s t hrefsz,
    RowLimits.trials_cast sizes s t hsz]
  change logOdds (effectiveTilt N p ref reference sizes s τ σ t) +
    Real.log (residual (p : ℝ) ref sizes s t) -
    (logOdds (reference t) + Real.log (residual (p : ℝ) ref ref s t)) = _
  rw [logOdds_effectiveTilt, Real.log_div (href t).ne' (hnew t).ne']
  ring

/-- The effective tilt as a sparse logit tilt with an explicit macroscopic parameter. -/
theorem effectiveTilt_eq_logitTilt (N : ℕ) (p : Binomial.Probability) (ref : Local.Sizes n)
    (reference : History (n + 1) → Binomial.Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (τ : ℝ) (σ : Row (n + 1)) (t : History (n + 1)) (σ₀ : ℝ)
    (hν : 0 < ν n t) (hscale : 0 < Real.sqrt ((p : ℝ) * N))
    (href : reference t = logitTilt N p σ₀ (ν n t)) :
    effectiveTilt N p ref reference sizes s τ σ t =
      logitTilt N p
        (σ₀ + ν n t * Real.sqrt ((p : ℝ) * N) *
          (Real.log (residual (p : ℝ) ref ref s t / residual (p : ℝ) ref sizes s t) +
            τ * betaScale N (p : ℝ) n * σ t))
        (ν n t) := by
  apply Binomial.logOdds_strictMono.injective
  rw [logOdds_effectiveTilt, Idealized.logOdds_logitTilt, href, Idealized.logOdds_logitTilt]
  have h1 : ν n t ≠ 0 := hν.ne'
  have h2 : Real.sqrt ((p : ℝ) * N) ≠ 0 := hscale.ne'
  field_simp
  ring

/-- Coordinatewise sparse bound for a logit tilt with bounded macroscopic parameter. -/
theorem logitTilt_sub_p_le (N : ℕ) (p : Binomial.Probability) (v g G : ℝ) (hv : 0 < v)
    (hG : 0 ≤ G) (hp : (p : ℝ) ≤ 1 / 2) (hs : 1 ≤ Real.sqrt ((p : ℝ) * N)) (hg : |g| ≤ G) :
    |(logitTilt N p g v : ℝ) - p| ≤
      (2 * Real.exp (G / v) / v) * ((p : ℝ) / Real.sqrt ((p : ℝ) * N)) * G := by
  have h := Process.logitTilt_lipschitz N p v G g 0 hv hG hp hs hg (by rw [abs_zero]; exact hG)
  rw [Idealized.logitTilt_zero, sub_zero] at h
  refine h.trans (mul_le_mul_of_nonneg_left hg ?_)
  exact mul_nonneg (div_nonneg (by positivity) hv.le)
    (div_nonneg p.property.1.le (Real.sqrt_nonneg _))

end MajorityDynamics.Idealized.LinearResponse
