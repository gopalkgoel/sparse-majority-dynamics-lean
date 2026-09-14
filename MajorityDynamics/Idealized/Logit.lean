import MajorityDynamics.Binomial.TiltUniqueness
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # The exact logit tilt of §5 (`def:logit-tilt`) -/

noncomputable section

namespace MajorityDynamics.Idealized

open Binomial

def logistic (θ : ℝ) : Probability :=
  ⟨Real.exp θ / (1 + Real.exp θ), div_pos (Real.exp_pos _) (by positivity),
    (div_lt_one (by positivity)).mpr (by linarith)⟩

theorem logOdds_logistic (θ : ℝ) : logOdds (logistic θ) = θ := by
  have hd : 1 + Real.exp θ ≠ 0 := ne_of_gt (by positivity)
  have hsub : 1 - (logistic θ : ℝ) = 1 / (1 + Real.exp θ) := by
    dsimp [logistic]
    field_simp
    ring
  rw [logOdds, hsub]
  change Real.log (Real.exp θ / (1 + Real.exp θ)) - Real.log (1 / (1 + Real.exp θ)) = θ
  rw [Real.log_div (Real.exp_pos _).ne' hd, Real.log_div one_ne_zero hd]
  simp

theorem logistic_logOdds (p : Probability) : logistic (logOdds p) = p :=
  logOdds_strictMono.injective (logOdds_logistic _)

theorem exp_logOdds (p : Probability) : Real.exp (logOdds p) = (p : ℝ) / (1 - (p : ℝ)) := by
  rw [logOdds, Real.exp_sub, Real.exp_log p.property.1,
    Real.exp_log (sub_pos.mpr p.property.2)]

/-- Defined at all scalar inputs; the paper uses `N ≥ 1` and `v > 0`. -/
def logitTilt (N : ℕ) (p : Probability) (g v : ℝ) : Probability :=
  logistic (logOdds p + g / (v * Real.sqrt ((p : ℝ) * N)))

theorem logitTilt_formula (N : ℕ) (p : Probability) (g v : ℝ) :
    (logitTilt N p g v : ℝ) =
      ((p : ℝ) / (1 - (p : ℝ)) * Real.exp (g / (v * Real.sqrt ((p : ℝ) * N)))) /
      (1 + (p : ℝ) / (1 - (p : ℝ)) * Real.exp (g / (v * Real.sqrt ((p : ℝ) * N)))) := by
  simp only [logitTilt, logistic, Real.exp_add, exp_logOdds]

theorem logOdds_logitTilt (N : ℕ) (p : Probability) (g v : ℝ) :
    logOdds (logitTilt N p g v) = logOdds p + g / (v * Real.sqrt ((p : ℝ) * N)) :=
  logOdds_logistic _

@[simp] theorem logitTilt_zero (N : ℕ) (p : Probability) (v : ℝ) :
    logitTilt N p 0 v = p := by simp [logitTilt, logistic_logOdds]

theorem logitTilt_injective (N : ℕ) (hN : 0 < N) (p : Probability)
    (v : ℝ) (hv : 0 < v) : Function.Injective (fun g => logitTilt N p g v) := by
  intro g h he
  have hd : v * Real.sqrt ((p : ℝ) * N) ≠ 0 := by
    apply ne_of_gt
    exact mul_pos hv (Real.sqrt_pos.mpr (mul_pos p.property.1 (by exact_mod_cast hN)))
  have he' := congrArg logOdds he
  simp only [logOdds_logitTilt, add_right_inj] at he'
  exact (div_left_inj' hd).mp he'

end MajorityDynamics.Idealized
