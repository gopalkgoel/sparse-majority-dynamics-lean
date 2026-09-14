import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

noncomputable section
open Filter Set
open scoped Topology

namespace MajorityDynamics.GraphProcess.EnumerationBounds

/-- Arbitrary fixed finite size, density and expected-degree bounds hold uniformly
throughout the density window. The threshold is chosen before the density. -/
theorem eventually_window {θ T L U M : ℝ}
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (_hL : 0 < L) (hU : 0 < U) (_hM : 0 < M) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹ * (N : ℝ) ^ (-θ) < p → p < T * (N : ℝ) ^ (-θ) →
      0 < (N : ℝ) ∧ 0 < p ∧ M ≤ (N : ℝ) ∧ L ≤ p * N ∧ p ≤ U := by
  have hT0 : 0 < T := by linarith
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun N : ℕ => T * (N : ℝ) ^ (-θ)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by linarith : 0 < θ)).comp hnat).const_mul T
  have hl : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - θ)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp hnat
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((eventually_ge_atTop (1 : ℕ)).and
      ((hnat.eventually_ge_atTop M).and
        ((hu.eventually (eventually_lt_nhds hU)).and
          (hl.eventually_gt_atTop (T * L)))))
  refine ⟨N₀, ?_⟩
  intro N hN p hpLo hpHi
  obtain ⟨hN1, hM, hup, hlo⟩ := hN₀ N hN
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hp0 : 0 < p := (mul_pos (inv_pos.mpr hT0) (Real.rpow_pos_of_pos hN0 _)).trans hpLo
  have hpow : (N : ℝ) ^ (-θ) * N = (N : ℝ) ^ (1 - θ) := by
    calc
      _ = (N : ℝ) ^ (-θ) * (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hN0]; congr 1; ring
  have hh := mul_lt_mul_of_pos_right hpLo hN0
  have hh' := mul_lt_mul_of_pos_left hh hT0
  have heq : T * (T⁻¹ * (N : ℝ) ^ (-θ) * N) = (N : ℝ) ^ (1 - θ) := by
    rw [mul_assoc, ← mul_assoc T, mul_inv_cancel₀ hT0.ne', one_mul, hpow]
  rw [heq] at hh'
  refine ⟨hN0, hp0, hM, ?_, (hpHi.trans hup).le⟩
  nlinarith

/-- Strictly larger real powers eventually dominate any fixed positive multiple. -/
theorem eventually_mul_rpow_le {a b A B : ℝ} (hab : a < b) (hB : 0 < B) :
    ∃ X : ℝ, 0 < X ∧ ∀ x ≥ X, A * x ^ a ≤ B * x ^ b := by
  have hp := (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_ge_atTop (A / B)
  obtain ⟨X, hX⟩ := eventually_atTop.mp ((eventually_ge_atTop (1 : ℝ)).and hp)
  refine ⟨max 1 X, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x hx
  obtain ⟨hx1, hpow⟩ := hX x ((le_max_right _ _).trans hx)
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hAB : A ≤ B * x ^ (b-a) := by
    have hh := (div_le_iff₀ hB).mp hpow
    simpa [mul_comm] using hh
  have hm := mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg hx0.le a)
  calc
    A * x ^ a ≤ (B * x ^ (b-a)) * x ^ a := hm
    _ = B * x ^ b := by
      rw [mul_assoc, ← Real.rpow_add hx0]
      congr 2
      ring

/-- Both real-exponent gaps in the maximum-deviation preparation, with a common threshold. -/
theorem eventually_deviation_regime {T : ℝ} (hT : 1 < T) :
    ∃ X : ℝ, 0 < X ∧ ∀ x ≥ X,
      T^2 * Real.sqrt x ≤ x ^ ((4:ℝ)/7) ∧
      2 * x ^ ((4:ℝ)/7) ≤ (x / (2*T^2)) ^ ((7:ℝ)/12) := by
  have hden : 0 < 2*T^2 := by positivity
  obtain ⟨X₁, hX₁, h₁⟩ := eventually_mul_rpow_le
    (a := (1:ℝ)/2) (b := (4:ℝ)/7) (A := T^2) (B := 1) (by norm_num) zero_lt_one
  obtain ⟨X₂, hX₂, h₂⟩ := eventually_mul_rpow_le
    (a := (4:ℝ)/7) (b := (7:ℝ)/12) (A := 2)
    (B := ((2*T^2)^((7:ℝ)/12))⁻¹) (by norm_num) (by positivity)
  refine ⟨max X₁ X₂, hX₁.trans_le (le_max_left _ _), ?_⟩
  intro x hx
  have hx0 : 0 < x := hX₁.trans_le ((le_max_left _ _).trans hx)
  constructor
  · simpa [Real.sqrt_eq_rpow] using h₁ x ((le_max_left _ _).trans hx)
  · convert h₂ x ((le_max_right _ _).trans hx) using 1
    rw [Real.div_rpow hx0.le hden.le]
    ring

/-- The explicit scalar enumeration error tends to zero uniformly in the paper's density window. -/
theorem scalar_error_vanishes {θ T ε : ℝ}
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹ * (N : ℝ) ^ (-θ) < p → p < T * (N : ℝ) ^ (-θ) →
      (Real.log (N : ℝ))^2 / Real.sqrt (N : ℝ) +
        (p*N)^(-(1:ℝ)/12) < ε := by
  have hlog : Tendsto (fun N : ℕ => (Real.log (N : ℝ))^2 / Real.sqrt (N : ℝ))
      atTop (𝓝 0) := by
    have hh := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero
    simpa [Function.comp_def, Real.rpow_two, Real.sqrt_eq_rpow] using
      hh.comp (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have herr : Tendsto (fun x : ℝ => x^(-(1:ℝ)/12)) atTop (𝓝 0) := by
    simpa only [neg_div] using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/12))
  obtain ⟨L, hL⟩ := eventually_atTop.mp
    ((eventually_ge_atTop (1 : ℝ)).and (herr.eventually (eventually_lt_nhds (by linarith : (0:ℝ)<ε/2))))
  let L' := max 1 L
  have hL' : 0 < L' := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨N₁, hN₁⟩ := eventually_window hθlo hθhi hT hL' (U := 1) zero_lt_one (M := 1) zero_lt_one
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp
    (hlog.eventually (eventually_lt_nhds (by linarith : (0:ℝ)<ε/2)))
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN p hpLo hpHi
  have hw := hN₁ N ((le_max_left _ _).trans hN) p hpLo hpHi
  have he := (hL (p*N) ((le_max_right 1 L).trans hw.2.2.2.1)).2
  have hl := hN₂ N ((le_max_right _ _).trans hN)
  linarith

end MajorityDynamics.GraphProcess.EnumerationBounds
