import MajorityDynamics.Idealized.CriticalDay.Basic
import MajorityDynamics.Idealized.LinearResponse.Rates

noncomputable section
namespace MajorityDynamics.Idealized.CriticalDay
open Universal LinearResponse
open Binomial.Approximation (Density)

/-- At the edge day the normalized response has constant, uniformly positive
scale. Neither bound involves the faithfulness exponent. -/
theorem critical_scale_bounds {N n : ℕ} {θ T : ℝ} {p : Binomial.Probability}
    (hN : 0 < N) (hT : 0 < T) (hp : Density θ T N p)
    (hk : (n : ℝ) + 1 = 1 / (1 - θ)) (hθ : θ < 1) :
    (Real.sqrt T)⁻¹ ^ (n + 1) ≤
      betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N) ∧
    betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N) ≤
      Real.sqrt T ^ (n + 1) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hsn : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  obtain ⟨hl, hu⟩ := sqrt_pN_bounds hN hT hp
  have hexp : (1 - θ) / 2 * ((n + 1 : ℕ) : ℝ) = 1 / 2 := by
    push_cast
    rw [hk]
    field_simp [(sub_pos.mpr hθ).ne']
  have hpN : ((N : ℝ) ^ ((1 - θ) / 2)) ^ (n + 1) = Real.sqrt N := by
    rw [← Real.rpow_mul_natCast hNr.le, hexp, ← Real.sqrt_eq_rpow]
  have hid : betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N) =
      Real.sqrt ((p : ℝ) * N) ^ (n + 1) / Real.sqrt (N : ℝ) := by
    unfold betaScale
    rw [pow_succ]
    ring
  rw [hid]
  constructor
  · apply (le_div_iff₀ hsn).mpr
    have h := pow_le_pow_left₀ (by positivity : 0 ≤
      (Real.sqrt T)⁻¹ * (N : ℝ) ^ ((1 - θ) / 2)) hl (n + 1)
    simpa only [mul_pow, hpN] using h
  · apply (div_le_iff₀ hsn).mpr
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) hu (n + 1)
    simpa only [mul_pow, hpN] using h

end MajorityDynamics.Idealized.CriticalDay
