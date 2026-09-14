import MajorityDynamics.Idealized.CriticalDay.Rates
import MajorityDynamics.Idealized.PerturbedTilt.Geometry

noncomputable section
open Filter Topology
namespace MajorityDynamics.Idealized.CriticalDay
open Universal LinearResponse PerturbedTilt
open Binomial.Approximation (Density)

/-- Faithful critical-day sizes are positive, have their original integer
values after conversion, and satisfy the full affine-support size threshold. -/
theorem faithful_geometry (θ T δ : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hδ : 0 < δ) (n ell : ℕ)
    (hk : (n : ℝ) + 1 = 1 / (1 - θ)) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Binomial.Probability, Density θ T N p →
    ∀ a : Process.Data, Process.Specification N p (responseHorizon θ) ell a →
    ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
    ∀ η : History (n + 1) → ℤ, ∀ e : History (n + 1) → History (n + 1) → ℤ,
    FaithfulNumericalData N (p : ℝ) T δ τ a n η e →
    (∀ t, 0 < η t) ∧
    (∀ t, ((naturalSizes η t : ℕ) : ℝ) = (η t : ℝ)) ∧
    (∀ t, 2 * n + 5 ≤ naturalSizes η t) ∧
    (∀ t, 0 < (a.state n).sizes t) := by
  have hT0 : 0 < T := by linarith
  have hC : 0 < comparisonConstant n T := hT0.trans_le (comparisonConstant_ge n hT0.le)
  obtain ⟨v, hv, hvle⟩ := RowLimits.finite_common_positive (ν n) (ν_positive n)
  have hlarge : ∀ᶠ N : ℕ in atTop,
      (4 * ((2 * n + 5 : ℕ) : ℝ) / v) ≤ N :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    Process.eventually_level_sizes (n := n) θ T ell hθhi hT0,
    beta_small θ T hθlo hθhi hT n hk,
    eventually_rpow_neg_le (rate θ) (v / (4 * comparisonConstant n T))
      (rate_pos hθlo hθhi) (by positivity),
    eventually_rpow_neg_le δ 1 hδ zero_lt_one, hlarge]
    with N hN hlev hbeta hsmall hpow hlarge
  intro p hp a ha τ hτ hτT η e hf
  have hτ0 : 0 ≤ τ := ((inv_pos.mpr hT0).trans_le hτ).le
  have hc := faithful_size_close hT0.le hτ0 hτT hpow hf
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hlevel := hlev.2 p hp (a.state n)
    (ha.estimates n (Nat.lt_of_succ_lt (critical_level_lt_horizon hk)))
  have hlo : ∀ t, ((2 * n + 5 : ℕ) : ℝ) ≤ η t := by
    intro t
    have hscale : sizeScale N (p : ℝ) n = betaScale N (p : ℝ) n * N :=
      sizeScale_eq N hN (p : ℝ) n
    have hb := mul_le_mul_of_nonneg_left ((hbeta p hp).trans hsmall) hC.le
    have hid : comparisonConstant n T * (v / (4 * comparisonConstant n T)) = v / 4 := by
      field_simp
    rw [hid] at hb
    have hbN := mul_le_mul_of_nonneg_right hb hN0.le
    have he := (abs_le.mp (hc t)).1
    rw [hscale] at he
    have href := (hlevel t).2.1
    have hν := mul_le_mul_of_nonneg_left (hvle t) hN0.le
    have hmin := (div_le_iff₀ hv).mp hlarge
    nlinarith
  have hη : ∀ t, 0 < η t := by
    intro t
    have := hlo t
    have : (0 : ℝ) < η t := lt_of_lt_of_le (by positivity) this
    exact_mod_cast this
  have hcast : ∀ t, ((naturalSizes η t : ℕ) : ℝ) = (η t : ℝ) := by
    intro t
    exact_mod_cast Int.toNat_of_nonneg (hη t).le
  refine ⟨hη, hcast, ?_, fun t => (hlevel t).1⟩
  intro t
  have hh := hlo t
  rw [← hcast t] at hh
  exact_mod_cast hh

end MajorityDynamics.Idealized.CriticalDay
