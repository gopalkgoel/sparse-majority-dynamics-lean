import MajorityDynamics.Idealized.CriticalDay.ReferenceBounds
noncomputable section
open Filter Topology
namespace MajorityDynamics.Idealized.CriticalDay
open Universal LinearResponse
open Binomial.Approximation (Density)

def rate (θ : ℝ) : ℝ := responseRate θ 0 / 2

theorem rate_pos {θ : ℝ} (hθlo : 1 / 2 < θ) (hθhi : θ < 1) : 0 < rate θ :=
  half_pos (responseRate_pos hθlo hθhi (first_day_subcritical hθlo hθhi))

theorem critical_level_lt_horizon {θ : ℝ} {n : ℕ}
    (hk : (n : ℝ) + 1 = 1 / (1 - θ)) : n + 1 < responseHorizon θ := by
  have hfloor : 1 / (1 - θ) < ((⌊1 / (1 - θ)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlt : (n : ℝ) + 1 < ((⌊1 / (1 - θ)⌋₊ : ℕ) : ℝ) + 1 := hk.trans_lt hfloor
  exact_mod_cast hlt

theorem beta_small (θ T : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (n : ℕ) (hk : (n : ℝ) + 1 = 1 / (1 - θ)) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Binomial.Probability, Density θ T N p →
      betaScale N (p : ℝ) n ≤ (N : ℝ) ^ (-rate θ) := by
  have hκ := responseRate_pos hθlo hθhi (first_day_subcritical hθlo hθhi)
  have hrκ : rate θ < responseRate θ 0 := by unfold rate; linarith
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    eventually_small θ T hθlo hθhi hT 0 0 (first_day_subcritical hθlo hθhi),
    eventually_poly_log_le (Real.sqrt T ^ (n + 1)) (responseRate θ 0) (rate θ) 0
      (by positivity) hrκ] with N hN hsmall hpoly
  intro p hp
  have hS : 0 < Real.sqrt ((p : ℝ) * N) := Real.sqrt_pos.mpr
    (mul_pos p.property.1 (Nat.cast_pos.mpr hN))
  have hb := (critical_scale_bounds hN (by linarith) hp hk hθhi).2
  have hb' : betaScale N (p : ℝ) n ≤ Real.sqrt T ^ (n + 1) / Real.sqrt ((p : ℝ) * N) :=
    (le_div_iff₀ hS).mpr hb
  have hinv := (hsmall p hp).2.2.1
  simp only [pow_zero] at hinv
  have hh := mul_le_mul_of_nonneg_left hinv (show 0 ≤ Real.sqrt T ^ (n + 1) by positivity)
  simp only [pow_zero, mul_one] at hpoly
  have hh' : Real.sqrt T ^ (n + 1) / Real.sqrt ((p : ℝ) * N) ≤
      Real.sqrt T ^ (n + 1) * (N : ℝ) ^ (-responseRate θ 0) := by
    simpa only [mul_one_div] using hh
  exact hb'.trans (hh'.trans hpoly)

end MajorityDynamics.Idealized.CriticalDay
