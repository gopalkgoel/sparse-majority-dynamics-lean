import MajorityDynamics.Paper.Inputs
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Uniform scalar estimates in the paper's polynomial density range -/

noncomputable section
open Filter Topology

namespace MajorityDynamics.Paper

theorem density_expectedDegree_lower {N : ℕ} (θ T : ℝ) (p : unitInterval)
    (hN : 0 < (N : ℝ)) (hdensity : densityRange θ T N p) :
    T⁻¹ * (N : ℝ) ^ (1 - θ) < (p : ℝ) * N := by
  have h := mul_lt_mul_of_pos_right hdensity.1 hN
  have heq : (N : ℝ) ^ (1 - θ) = (N : ℝ) ^ (-θ) * N := by
    rw [show 1 - θ = -θ + 1 by ring, Real.rpow_add_one hN.ne']
  rwa [mul_assoc, ← heq] at h

/-- The paper's range eventually lies in the imported jumbledness regime. -/
theorem density_eventually_jumbled_regime (θ T : ℝ)
    (hθ0 : 0 < θ) (hθ : θ < 1) (hT : 0 < T) :
    ∀ᶠ N : ℕ in atTop, ∀ p : unitInterval, densityRange θ T N p →
      0 < (p : ℝ) ∧ (p : ℝ) ≤ 99 / 100 ∧
        (Real.log (N : ℝ)) ^ 2 ≤ (p : ℝ) * N := by
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun N : ℕ => T * (N : ℝ) ^ (-θ)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hθ0).comp hnat).const_mul T
  have hlog := ((isLittleO_log_rpow_rpow_atTop 2 (by linarith : 0 < 1 - θ)).comp_tendsto
    hnat).bound (inv_pos.mpr hT)
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    hupper.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 99 / 100)), hlog]
    with N hN hupperN hlogN
  intro p hdensity
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hp : 0 < (p : ℝ) := lt_trans
    (mul_pos (inv_pos.mpr hT) (Real.rpow_pos_of_pos hN0 _)) hdensity.1
  refine ⟨hp, (hdensity.2.trans hupperN).le, ?_⟩
  have hlog' : (Real.log (N : ℝ)) ^ 2 ≤ T⁻¹ * (N : ℝ) ^ (1 - θ) := by
    simpa only [Function.comp_apply, Real.rpow_two, Real.norm_of_nonneg (sq_nonneg _),
      Real.norm_of_nonneg (Real.rpow_nonneg hN0.le _)] using hlogN
  exact hlog'.trans (density_expectedDegree_lower θ T p hN0 hdensity).le

def degreeFailureEnvelope (θ T : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) * Real.exp (-(T⁻¹ * (N : ℝ) ^ (1 - θ)) / 1000)

/-- A fixed scalar sequence bounds all allowed densities and tends to zero. -/
theorem degreeFailureEnvelope_tendsto (θ T : ℝ) (hθ : θ < 1) (hT : 0 < T) :
    Tendsto (degreeFailureEnvelope θ T) atTop (𝓝 0) := by
  let a := 1 - θ
  let b := T⁻¹ / 1000
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; positivity
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpow := (tendsto_rpow_atTop ha).comp hnat
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / a) b hb).comp hpow
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  change ((N : ℝ) ^ a) ^ (1 / a) * Real.exp (-b * (N : ℝ) ^ a) = _
  rw [← Real.rpow_mul hN0, mul_one_div_cancel ha.ne', Real.rpow_one]
  unfold degreeFailureEnvelope
  congr 2
  dsimp [a, b]
  ring

theorem degree_failure_le_envelope {N : ℕ} (θ T : ℝ) (p : unitInterval)
    (hN : 0 < (N : ℝ)) (hdensity : densityRange θ T N p) :
    (N : ℝ) * Real.exp (-((p : ℝ) * N) / 1000) ≤ degreeFailureEnvelope θ T N := by
  apply mul_le_mul_of_nonneg_left _ hN.le
  apply Real.exp_le_exp.mpr
  have h := density_expectedDegree_lower θ T p hN hdensity
  linarith

end MajorityDynamics.Paper
