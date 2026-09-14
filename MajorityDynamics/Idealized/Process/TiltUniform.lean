import MajorityDynamics.Idealized.Process.Basic
import MajorityDynamics.Idealized.Process.TiltEstimates
import MajorityDynamics.Idealized.RowLimits.Basic
import MajorityDynamics.Idealized.RowLimits.Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Uniform literal tilt estimates after absorbing a fixed coefficient -/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace MajorityDynamics.Idealized.Process

open Universal Binomial Binomial.Approximation

theorem eventually_tilt_estimates (θ T : ℝ) (n L : ℕ) (R C : ℝ)
    (hθ : 0 < θ) (hθ' : θ < 1) (hT : 0 < T) (hR : 0 ≤ R) (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Probability, Density θ T N p →
      ∀ σ : History (n + 1) → Row (n + 1),
      (∀ s t, |σ s t| ≤ R) → (∀ s t, |γ n s t| ≤ R) →
      (∀ s t, |σ s t - γ n s t| ≤ C * (Real.log N ^ L / scale N p)) →
      TiltEstimates N p (L + 1) (fun s => RowLimits.rowTilt N p (σ s)) := by
  classical
  let B := 1 + ∑ t : History (n + 1), 2 * Real.exp (R / ν n t) / ν n t * C
  have hB : 1 ≤ B := by
    dsimp [B]
    apply le_add_of_nonneg_right
    exact Finset.sum_nonneg fun t _ => mul_nonneg
      (div_nonneg (by positivity) (ν_positive n t).le) hC
  have hBt (t : History (n + 1)) : 2 * Real.exp (R / ν n t) / ν n t * C ≤ B := by
    have hh : 2 * Real.exp (R / ν n t) / ν n t * C ≤
        ∑ j : History (n + 1), 2 * Real.exp (R / ν n j) / ν n j * C := Finset.single_le_sum
      (fun j _ => show 0 ≤ 2 * Real.exp (R / ν n j) / ν n j * C from
        mul_nonneg (div_nonneg (by positivity) (ν_positive n j).le) hC)
      (Finset.mem_univ t)
    dsimp [B]
    linarith
  have hlog := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop B)
  have ht : Tendsto (fun N : ℕ => T * (N : ℝ) ^ (-θ)) atTop (nhds 0) := by
    simpa using ((tendsto_rpow_neg_atTop hθ).comp tendsto_natCast_atTop_atTop).const_mul T
  have hupper := ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hlog, hupper,
    RowLimits.density_scale_lower_power θ T 1 0 hθ' hT zero_lt_one]
      with N hlog hupper hscale
  intro p hp σ hσ hγ hclose s t
  have hs : 1 ≤ Real.sqrt ((p : ℝ) * N) := by simpa [scale] using hscale p hp
  have hlog0 : 0 ≤ Real.log (N : ℝ) := le_trans zero_le_one (hB.trans hlog)
  have hh := logitTilt_error N p (ν n t) R (σ s t) (γ n s t) C (Real.log N ^ L)
    (ν_positive n t) hR hC (pow_nonneg hlog0 _) (hp.2.trans hupper).le
    hs (hσ s t) (hγ s t) (by simpa [scale, mul_div_assoc] using hclose s t)
  calc
    _ ≤ (2 * Real.exp (R / ν n t) / ν n t * C) * Real.log N ^ L / N := hh
    _ ≤ Real.log N * Real.log N ^ L / N :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right ((hBt t).trans hlog) (pow_nonneg hlog0 _))
        (Nat.cast_nonneg _)
    _ = Real.log N ^ (L + 1) / N := by rw [pow_succ]; ring

end MajorityDynamics.Idealized.Process
