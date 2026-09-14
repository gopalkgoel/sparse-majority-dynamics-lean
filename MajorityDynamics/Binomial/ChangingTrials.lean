import MajorityDynamics.Binomial.WindowPointEstimate

/-! # Local likelihood comparison for different binomial trial counts

The first-order parameter is the original A.2 odds times remaining-trials
ratio. The shared reference center is independent of either trial count.
-/

noncomputable section

namespace MajorityDynamics.Binomial.Approximation
open Analysis

def scalarTiltDifference (m₀ m₁ : ℕ) (μ : ℝ) (q₀ q₁ : Probability) : ℝ :=
  Real.log (((q₁ : ℝ) / (1 - (q₁ : ℝ)) * ((m₁ : ℝ) - μ)) /
    ((q₀ : ℝ) / (1 - (q₀ : ℝ)) * ((m₀ : ℝ) - μ)))

theorem scalarTiltDifference_eq {m₀ m₁ : ℕ} {μ : ℝ}
    (h₀ : μ < m₀) (h₁ : μ < m₁) (q₀ q₁ : Probability) :
    scalarTiltDifference m₀ m₁ μ q₀ q₁ =
      logOdds q₁ + Real.log ((m₁ : ℝ) - μ) -
        (logOdds q₀ + Real.log ((m₀ : ℝ) - μ)) := by
  have hp₀ := q₀.property.1
  have hp₁ := q₁.property.1
  have hq₀ := sub_pos.mpr q₀.property.2
  have hq₁ := sub_pos.mpr q₁.property.2
  have hd₀ := sub_pos.mpr h₀
  have hd₁ := sub_pos.mpr h₁
  rw [scalarTiltDifference,
    Real.log_div (mul_pos (div_pos hp₁ hq₁) hd₁).ne' (mul_pos (div_pos hp₀ hq₀) hd₀).ne',
    Real.log_mul (div_pos hp₁ hq₁).ne' hd₁.ne',
    Real.log_mul (div_pos hp₀ hq₀).ne' hd₀.ne',
    Real.log_div hp₁.ne' hq₁.ne', Real.log_div hp₀.ne' hq₀.ne']
  rfl

def scalarLikelihoodRemainder (m₀ m₁ : ℕ) (μ : ℝ) (q₀ q₁ : Probability) (k : ℕ) : ℝ :=
  Real.log (pointMass m₁ k q₁) - Real.log (pointMass m₀ k q₀) -
    scalarTiltDifference m₀ m₁ μ q₀ q₁ * ((k : ℝ) - μ)

/-- Uniform log-likelihood error around a common real center, allowing
different trial counts on both sides. -/
theorem changing_trials_log_error (m₀ m₁ : ℕ) (μ L : ℝ) (q₀ q₁ : Probability)
    (h₀ : μ < m₀) (h₁ : μ < m₁) (hL : 0 ≤ L)
    (hL₀ : L ≤ ((m₀ : ℝ) - μ) / 2) (hL₁ : L ≤ ((m₁ : ℝ) - μ) / 2)
    (a b : ℕ) (ha : |(a : ℝ) - μ| ≤ L) (hb : |(b : ℝ) - μ| ≤ L) :
    |scalarLikelihoodRemainder m₀ m₁ μ q₀ q₁ b -
      scalarLikelihoodRemainder m₀ m₁ μ q₀ q₁ a| ≤
        4 * L ^ 2 * (1 / ((m₀ : ℝ) - μ) + 1 / ((m₁ : ℝ) - μ)) := by
  have hd₀ := sub_pos.mpr h₀
  have hd₁ := sub_pos.mpr h₁
  have hbound := window_log_error (scalarLikelihoodRemainder m₀ m₁ μ q₀ q₁)
    μ L (2 * L / ((m₀ : ℝ) - μ) + 2 * L / ((m₁ : ℝ) - μ))
    (by positivity) a b ha hb (by
      intro k hk _
      have hkb := (abs_le.mp hk).2
      have hk₀ : k < m₀ := by exact_mod_cast (show (k : ℝ) < m₀ by linarith)
      have hk₁ : k < m₁ := by exact_mod_cast (show (k : ℝ) < m₁ by linarith)
      have heq : scalarLikelihoodRemainder m₀ m₁ μ q₀ q₁ (k + 1) -
          scalarLikelihoodRemainder m₀ m₁ μ q₀ q₁ k =
          (Real.log ((m₁ : ℝ) - k) - Real.log ((m₁ : ℝ) - μ)) -
          (Real.log ((m₀ : ℝ) - k) - Real.log ((m₀ : ℝ) - μ)) := by
        have hstep₀ := log_pointMass_succ hk₀ q₀
        have hstep₁ := log_pointMass_succ hk₁ q₁
        dsimp [scalarLikelihoodRemainder]
        rw [scalarTiltDifference_eq h₀ h₁, Nat.cast_add, Nat.cast_one]
        nlinarith only [hstep₀, hstep₁]
      rw [heq]
      calc
        _ ≤ |Real.log ((m₁ : ℝ) - k) - Real.log ((m₁ : ℝ) - μ)| +
            |Real.log ((m₀ : ℝ) - k) - Real.log ((m₀ : ℝ) - μ)| := abs_sub _ _
        _ ≤ 2 * L / ((m₀ : ℝ) - μ) + 2 * L / ((m₁ : ℝ) - μ) := by
          linarith [complement_log_error hL hd₀ hL₀ hk, complement_log_error hL hd₁ hL₁ hk])
  convert hbound using 1
  ring

end MajorityDynamics.Binomial.Approximation
