import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! # Tail moments controlled by a checked second moment -/

noncomputable section
open MeasureTheory Set
namespace MajorityDynamics.Analysis

theorem tail_moment_sqrt {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → ℝ) (hf : MemLp f 2 μ) (E : Set Ω) (hE : MeasurableSet E) :
    (∫ x in E, |f x| ∂μ) ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (μ.real E) := by
  classical
  have hi : MemLp (E.indicator (fun _ => (1 : ℝ))) 2 μ := (memLp_const 1).indicator hE
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all μ (fun x => abs_nonneg (f x)))
    (ae_of_all μ (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x))
    (show MemLp (fun x => |f x|) (ENNReal.ofReal 2) μ by simpa using hf.norm)
    (show MemLp (E.indicator (fun _ => (1 : ℝ))) (ENNReal.ofReal 2) μ by simpa using hi)
  have hprod : (fun x => |f x| * E.indicator (fun _ => (1 : ℝ)) x) = E.indicator (fun x => |f x|) := by
    funext x
    by_cases hx : x ∈ E <;> simp [hx]
  have hsq : (fun x => (E.indicator (fun _ => (1 : ℝ)) x) ^ (2 : ℝ)) = E.indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ E <;> simp [hx]
  rw [hprod, integral_indicator hE, hsq, integral_indicator hE] at h
  simpa only [Real.rpow_two, sq_abs, setIntegral_const, smul_eq_mul, mul_one, ← Real.sqrt_eq_rpow] using h

end MajorityDynamics.Analysis
