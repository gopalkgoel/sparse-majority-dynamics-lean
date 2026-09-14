import MajorityDynamics.GraphProcess.EnumerationComparison.Basic
import MajorityDynamics.Probability.NeighborhoodBulk.BipartiteSparse

noncomputable section
open Filter
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.EnumerationComparison
open Probability.NeighborhoodBulk EnumerationBounds

theorem scale_from_global {θ T N a p m : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hN : 0 < N) (ha : N/T ≤ a) (haN : a ≤ N)
    (hp : T⁻¹*N^(-θ) < p) (hp' : p < T*N^(-θ))
    (hm : p*N^2/(4*T^3) ≤ m) (hm' : m ≤ 2*T*p*N^2) :
    (4*T^4)⁻¹*a^(2-θ) ≤ m ∧ m ≤ (4*T^4)*a^(2-θ) := by
  have hT0 : 0 < T := by linarith
  have ha0 : 0 < a := (div_pos hN hT0).trans_le ha
  have hr : 0 ≤ 2-θ := by linarith
  have hp0 : 0 < p := (by positivity : 0 < T⁻¹*N^(-θ)).trans hp
  have hpow := Real.rpow_le_rpow ha0.le haN hr
  have hNa : N ≤ T*a := by have := (div_le_iff₀ hT0).mp ha; nlinarith
  have hscale : N^(2-θ) ≤ T^2*a^(2-θ) := by
    calc
      _ ≤ (T*a)^(2-θ) := Real.rpow_le_rpow hN.le hNa hr
      _ = T^(2-θ)*a^(2-θ) := Real.mul_rpow hT0.le ha0.le
      _ ≤ T^2*a^(2-θ) := by
        gcongr
        simpa only [Real.rpow_two] using
          (Real.rpow_le_rpow_of_exponent_le hT.le (show 2-θ ≤ (2:ℝ) by linarith))
  have hid : N^(-θ)*N^2 = N^(2-θ) := by
    rw [← Real.rpow_two, ← Real.rpow_add hN]
    congr 1
    ring
  have hlo := mul_le_mul_of_nonneg_right hp.le (sq_nonneg N)
  have hhi := mul_le_mul_of_nonneg_right hp'.le (sq_nonneg N)
  rw [mul_assoc, hid] at hlo hhi
  constructor
  · have hlow := (div_le_div_of_nonneg_right hlo (by positivity : 0 ≤ 4*T^3)).trans hm
    have he : T⁻¹*N^(2-θ)/(4*T^3) = (4*T^4)⁻¹*N^(2-θ) := by
      field_simp

    rw [he] at hlow
    exact (mul_le_mul_of_nonneg_left hpow (by positivity)).trans hlow
  · have hh := mul_le_mul_of_nonneg_left hhi (show 0 ≤ 2*T by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hscale (show 0 ≤ 2*T^2 by positivity)
    have hn : 0 ≤ T^4*a^(2-θ) := by positivity
    nlinarith

end MajorityDynamics.GraphProcess.EnumerationComparison
