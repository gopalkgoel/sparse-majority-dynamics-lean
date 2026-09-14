import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

noncomputable section
open Filter Set
open scoped Topology
namespace MajorityDynamics.GraphProcess.AutomaticGraphicality

/-- A common threshold gives the finite regime throughout the paper's density window. -/
theorem eventually_regime {θ T : ℝ} (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹ * (N : ℝ) ^ (-θ) < p → p < T * (N : ℝ) ^ (-θ) →
      0 < (N : ℝ) ∧ 0 < p ∧ 1 ≤ p * N ∧ 4 * T ^ 6 ≤ p * N ∧
        p ≤ 1 / (12 * T ^ 2) := by
  have hT0 : 0 < T := by linarith
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun N : ℕ => T * (N : ℝ) ^ (-θ)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by linarith : 0 < θ)).comp hnat).const_mul T
  have hl : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - θ)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp hnat
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((eventually_ge_atTop (1 : ℕ)).and
      ((hu.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < 1 / (12 * T ^ 2)))).and
        (hl.eventually_gt_atTop (T * max 1 (4 * T ^ 6)))))
  refine ⟨N₀, ?_⟩
  intro N hN p hpLo hpHi
  obtain ⟨hN1, hup, hlo⟩ := hN₀ N hN
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hp0 : 0 < p := (mul_pos (inv_pos.mpr hT0) (Real.rpow_pos_of_pos hN0 _)).trans hpLo
  have hpow : (N : ℝ) ^ (-θ) * N = (N : ℝ) ^ (1 - θ) := by
    calc
      _ = (N : ℝ) ^ (-θ) * (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hN0]; congr 1; ring
  have hmax : max 1 (4 * T ^ 6) < p * N := by
    have hh := mul_lt_mul_of_pos_right hpLo hN0
    have hh' := mul_lt_mul_of_pos_left hh hT0
    have heq : T * (T⁻¹ * (N : ℝ) ^ (-θ) * N) = (N : ℝ) ^ (1 - θ) := by
      rw [mul_assoc, ← mul_assoc T, mul_inv_cancel₀ hT0.ne', one_mul, hpow]
    rw [heq] at hh'
    nlinarith
  exact ⟨hN0, hp0, (le_max_left _ _).trans hmax.le,
    (le_max_right _ _).trans hmax.le, (hpHi.trans hup).le⟩

end MajorityDynamics.GraphProcess.AutomaticGraphicality
