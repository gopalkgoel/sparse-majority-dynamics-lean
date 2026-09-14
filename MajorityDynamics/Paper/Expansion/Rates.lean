import MajorityDynamics.Idealized.LinearResponse.Rates
import MajorityDynamics.GraphProcess.LocalTransition.Basic
import MajorityDynamics.Paper.CleanupAsymptotics

noncomputable section
open Filter Topology
namespace MajorityDynamics.Paper.Expansion
open Idealized.LinearResponse Binomial.Approximation

theorem density_power_lower {θ T : ℝ} {N : ℕ} {p : Binomial.Probability}
    (hT : 0 < T) (hN : 0 < (N : ℝ)) (hp : Density θ T N p) {a : ℝ} (ha : 0 ≤ a) :
    T^(-a) * (N : ℝ)^((1-θ)*a) ≤ ((p : ℝ)*N)^a := by
  have hlo : T⁻¹ * (N : ℝ)^(1-θ) ≤ (p : ℝ)*N := by
    rw [show 1-θ = -θ+1 by ring, Real.rpow_add_one hN.ne', ← mul_assoc]
    exact (mul_lt_mul_of_pos_right hp.1 hN).le
  have h := Real.rpow_le_rpow (by positivity : 0 ≤ T⁻¹*(N : ℝ)^(1-θ)) hlo ha
  rw [Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hT.le,
    ← Real.rpow_neg hT.le, ← Real.rpow_mul hN.le] at h
  exact h

theorem sqrt_power (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    Real.sqrt x ^ k = x ^ ((k : ℝ)/2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  ring

theorem eventually_noncritical_lead {θ T c : ℝ} {n : ℕ}
    (hT : 0 < T) (hc : 0 < c) (hn : 1 < (1-θ)*((n : ℝ)+1)) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Binomial.Probability, Density θ T N p →
      (N : ℝ)/Real.sqrt ((p : ℝ)*N)*Real.log N ≤ c*sizeScale N p n := by
  let a : ℝ := ((n : ℝ)+1)/2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have he : 0 < (1-θ)*a-1/2 := by dsimp [a]; nlinarith
  filter_upwards [eventually_gt_atTop (0:ℕ),
    eventually_log_pow_le_rpow 1 he (show 0 < c*T^(-a) by positivity)] with N hN hl
  intro p hp
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast hN
  have hx : 0 < (p:ℝ)*N := mul_pos p.property.1 hN0
  have hs : 0 < Real.sqrt ((p:ℝ)*N) := Real.sqrt_pos.mpr hx
  have hlo := density_power_lower hT hN0 hp ha
  have hpw : Real.sqrt ((p:ℝ)*N)^(n+1) = ((p:ℝ)*N)^a := by
    rw [sqrt_power _ hx.le]
    simp [a]
  have hlog : Real.sqrt (N:ℝ)*Real.log N ≤ c*Real.sqrt ((p:ℝ)*N)^(n+1) := by
    calc
      _ ≤ Real.sqrt (N:ℝ)*(c*T^(-a)*(N:ℝ)^((1-θ)*a-1/2)) :=
        mul_le_mul_of_nonneg_left (by simpa using hl) (Real.sqrt_nonneg _)
      _ = c*(T^(-a)*(N:ℝ)^((1-θ)*a)) := by
        rw [Real.sqrt_eq_rpow]
        have heq : (N:ℝ)^((1:ℝ)/2)*(N:ℝ)^((1-θ)*a-1/2) = (N:ℝ)^((1-θ)*a) := by
          rw [← Real.rpow_add hN0]
          congr 1
          ring
        calc
          _ = c*T^(-a)*((N:ℝ)^((1:ℝ)/2)*(N:ℝ)^((1-θ)*a-1/2)) := by ring
          _ = _ := by rw [heq]; ring
      _ ≤ _ := by rw [hpw]; exact mul_le_mul_of_nonneg_left hlo hc.le
  apply (mul_le_mul_iff_of_pos_right hs).mp
  have hm := mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg (N:ℝ))
  have hnroot := Real.mul_self_sqrt hN0.le
  calc
    _ = (N:ℝ)*Real.log N := by
      rw [div_eq_mul_inv]
      calc
        _ = ((N:ℝ)*Real.log N)*((Real.sqrt ((p:ℝ)*N))⁻¹*Real.sqrt ((p:ℝ)*N)) := by ring
        _ = _ := by rw [inv_mul_cancel₀ hs.ne', mul_one]
    _ ≤ Real.sqrt (N:ℝ)*(c*Real.sqrt ((p:ℝ)*N)^(n+1)) := by simpa only [← mul_assoc, hnroot] using hm
    _ = _ := by simp only [sizeScale, pow_succ]; ring

theorem eventually_critical_lead {θ T c : ℝ} (hθ : θ < 1) (hT : 0 < T) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Binomial.Probability, Density θ T N p →
      (N:ℝ)/Real.sqrt ((p:ℝ)*N)*Real.log N ≤ c*N := by
  filter_upwards [eventually_gt_atTop (0:ℕ),
    eventually_log_pow_le_rpow 1 (show 0 < (1-θ)/2 by linarith)
      (show 0 < c*T^(-(1:ℝ)/2) by positivity)] with N hN hl
  intro p hp
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast hN
  have hs : 0 < Real.sqrt ((p:ℝ)*N) := Real.sqrt_pos.mpr (mul_pos p.property.1 hN0)
  have hlo := density_power_lower hT hN0 hp (show 0 ≤ (1:ℝ)/2 by norm_num)
  have hlo' : T^(-(1:ℝ)/2)*(N:ℝ)^((1-θ)*((1:ℝ)/2)) ≤ ((p:ℝ)*N)^((1:ℝ)/2) := by convert hlo using 1; ring
  have hlog : Real.log (N:ℝ) ≤ c*Real.sqrt ((p:ℝ)*N) := by
    rw [Real.sqrt_eq_rpow]
    exact (show Real.log (N:ℝ) ≤ c*(T^(-(1:ℝ)/2)*(N:ℝ)^((1-θ)*((1:ℝ)/2))) by
      convert (show Real.log (N:ℝ) ≤ c*T^(-(1:ℝ)/2)*(N:ℝ)^((1-θ)/2) by simpa using hl) using 1; ring).trans
      (mul_le_mul_of_nonneg_left hlo' hc.le)
  apply (mul_le_mul_iff_of_pos_right hs).mp
  calc
    _ = (N:ℝ)*Real.log N := by
      rw [div_eq_mul_inv]
      calc
        _ = ((N:ℝ)*Real.log N)*((Real.sqrt ((p:ℝ)*N))⁻¹*Real.sqrt ((p:ℝ)*N)) := by ring
        _ = _ := by rw [inv_mul_cancel₀ hs.ne', mul_one]
    _ ≤ (N:ℝ)*(c*Real.sqrt ((p:ℝ)*N)) := mul_le_mul_of_nonneg_left hlog hN0.le
    _ = _ := by ring

theorem eventually_critical_error {C ζ : ℝ} (hC : 0 ≤ C) (hζ : 0 < ζ) :
    ∀ᶠ N : ℕ in atTop, C*GraphProcess.LocalTransition.sizeScale N ≤ (ζ/2)*N := by
  filter_upwards [eventually_gt_atTop (0:ℕ),
    eventually_log_pow_le_rpow 1 (show 0 < (1:ℝ)/2 by norm_num)
      (show 0 < ζ/(2*(C+1)) by positivity)] with N hN hl
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast hN
  have hlog : Real.log (N:ℝ) ≤ ζ/(2*(C+1))*Real.sqrt N := by
    simpa [Real.sqrt_eq_rpow] using hl
  have hcoef : C*(ζ/(2*(C+1))) ≤ ζ/2 := by
    field_simp
    nlinarith
  have h := mul_le_mul_of_nonneg_left hlog (show 0 ≤ C*Real.sqrt N by positivity)
  have hs := Real.mul_self_sqrt hN0.le
  have hb := mul_le_mul_of_nonneg_right hcoef hN0.le
  unfold GraphProcess.LocalTransition.sizeScale
  calc
    _ = C*Real.sqrt N*Real.log N := by ring
    _ ≤ C*Real.sqrt N*(ζ/(2*(C+1))*Real.sqrt N) := h
    _ = C*(ζ/(2*(C+1)))*N := by
      calc
        _ = C*(ζ/(2*(C+1)))*(Real.sqrt N*Real.sqrt N) := by ring
        _ = _ := by rw [hs]
    _ ≤ _ := hb

theorem eventually_error_coefficient (D : ℝ) {δ b : ℝ} (hδ : 0 < δ) (hb : 0 < b) :
    ∀ᶠ N : ℕ in atTop, D*(N:ℝ)^(-δ) ≤ b := by
  have ht : Tendsto (fun N : ℕ => D*(N:ℝ)^(-δ)) atTop (nhds 0) := by
    simpa using ((tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop).const_mul D
  exact ht.eventually (eventually_le_nhds hb)

end MajorityDynamics.Paper.Expansion
