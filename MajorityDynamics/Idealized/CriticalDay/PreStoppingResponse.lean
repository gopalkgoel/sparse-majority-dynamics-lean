import MajorityDynamics.Idealized.CriticalDay.FlexibleScales
import MajorityDynamics.Idealized.LinearResponse.SparseRates

noncomputable section
open Filter Topology
namespace MajorityDynamics.Idealized.CriticalDay
open Binomial.Approximation LinearResponse

/-- Every pre-stopping response satisfies the fixed polynomial cutoff used
by the widened response theorem. The cutoff is independent of the freely
chosen stopping exponent, provided that exponent is at most one quarter. -/
theorem pre_stopping_response_small (θ T : ℝ) (hθ : θ < 1) (hT : 0 < T) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Binomial.Probability, SparseRange θ T N p →
      ∀ r : ℝ, r ≤ 1/4 → ∀ n : ℕ,
        betaScale N p n * scale N p < scale N p ^ (r-1) →
        ResponseSmall θ N p n := by
  have hgap : (1-θ)/4 < 3*(1-θ)/8 := by linarith
  filter_upwards [eventually_ge_atTop (1:ℕ),
    RowLimits.density_scale_lower_power_sparse θ T 1 0 hθ hT zero_lt_one,
    eventually_poly_log_le ((T⁻¹)^(3/8:ℝ))⁻¹ (3*(1-θ)/8) ((1-θ)/4) 0
      (by positivity) hgap] with N hN hs hbudget
  intro p hp r hr n hprev
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hs1 : 1 ≤ scale N p := by simpa using hs p hp
  have hlo := (scale_rpow_sparse_bounds (by omega) hT
    (by norm_num : (0:ℝ) ≤ 3/4) hp).1
  have hlo' : (T⁻¹)^(3/8:ℝ) * (N:ℝ)^(3*(1-θ)/8) ≤ scale N p^(3/4:ℝ) := by
    convert hlo using 1
    congr 2 <;> ring
  have hi := inv_anti₀ (show 0 < (T⁻¹)^(3/8:ℝ) * (N:ℝ)^(3*(1-θ)/8) by positivity) hlo'
  have hi' : scale N p^(-(3/4:ℝ)) ≤
      ((T⁻¹)^(3/8:ℝ))⁻¹ * (N:ℝ)^(-(3*(1-θ)/8)) := by
    simpa only [Real.rpow_neg (zero_le_one.trans hs1), Real.rpow_neg hn.le,
      mul_inv_rev, mul_comm] using hi
  have hc : scale N p^(r-1) ≤ scale N p^(-(3/4:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)
  exact hprev.le.trans (hc.trans (hi'.trans (by simpa only [pow_zero, mul_one] using hbudget)))

end MajorityDynamics.Idealized.CriticalDay
