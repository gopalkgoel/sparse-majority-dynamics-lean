import MajorityDynamics.GraphProcess.EnumerationBounds.Asymptotics

noncomputable section
open Filter Set
open scoped Topology

namespace MajorityDynamics.GraphProcess.EnumerationBounds

/-- Arbitrary fixed finite size, density and expected-degree bounds hold uniformly
throughout the density window. The threshold is chosen before the density. -/
theorem eventually_band_window {θ η T L U M : ℝ}
    (hη : 0 < η) (hθhi : θ < 1) (hT : 1 < T)
    (_hL : 0 < L) (hU : 0 < U) (_hM : 0 < M) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹ * (N : ℝ) ^ (-θ) < p → p < T * (N : ℝ) ^ (-η) →
      0 < (N : ℝ) ∧ 0 < p ∧ M ≤ (N : ℝ) ∧ L ≤ p * N ∧ p ≤ U := by
  have hT0 : 0 < T := by linarith
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun N : ℕ => T * (N : ℝ) ^ (-η)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hη).comp hnat).const_mul T
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

end MajorityDynamics.GraphProcess.EnumerationBounds
