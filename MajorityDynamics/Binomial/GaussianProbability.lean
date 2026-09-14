import MajorityDynamics.Binomial.CellComparison
import MajorityDynamics.Analysis.GaussianLinear

/-! # Coordinate and boundary probabilities for the actual product Gaussian -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace MajorityDynamics.Binomial.Approximation
variable {d r : ℕ}

instance gaussianLaw_probability (p : Probability) (η : Fin d → ℕ) (α : Fin d → ℝ) :
    IsProbabilityMeasure (gaussianLaw p η α) := by
  unfold gaussianLaw
  infer_instance

theorem gaussian_coordinate_law (p : Probability) (η : Fin d → ℕ) (α : Fin d → ℝ) (i : Fin d) :
    (gaussianLaw p η α).map (fun x => x i) = gaussianReal (gaussianMean p η α i) (gaussianVariance p η i) :=
  (measurePreserving_eval (fun j => gaussianReal (gaussianMean p η α j) (gaussianVariance p η j)) i).map_eq

theorem gaussian_coordinate_tail (p : Probability) (η : Fin d → ℕ) (α : Fin d → ℝ)
    (i : Fin d) (hη : 0 < η i) (R : ℝ) (hR : 0 ≤ R) :
    (gaussianLaw p η α).real {x | R ≤ |x i - gaussianMean p η α i|} ≤
      2 * Real.exp (-(R ^ 2) / (2 * ((p : ℝ) * η i))) := by
  have hv : 0 < gaussianVariance p η i := mul_pos p.property.1 (by exact_mod_cast hη)
  have h := Analysis.gaussian_tail (gaussianMean p η α i) (gaussianVariance p η i) hv R hR
  rw [← gaussian_coordinate_law p η α i, map_measureReal_apply (measurable_pi_apply i) (by measurability)] at h
  exact h

/-- A strip normal with a unit-sized coordinate has variance at least the
smallest coordinate variance. This bound is uniform in the mean and offset. -/
theorem gaussian_strip_le (p : Probability) (η : Fin d → ℕ) (α a : Fin d → ℝ)
    (T s : ℝ) (hT : 1 ≤ T) (hs : 0 < s)
    (hvar : ∀ i, s ^ 2 / T ≤ (p : ℝ) * η i)
    (ha : ∃ i, 1 ≤ |a i|) (b R : ℝ) (hR : 0 ≤ R) :
    (gaussianLaw p η α).real {x | |(∑ i, a i * x i) - b| ≤ R} ≤ 2 * R * T / s := by
  have hT0 : 0 < T := by linarith
  let V : ℝ≥0 := ∑ i, NNReal.mk (a i ^ 2) (sq_nonneg _) * gaussianVariance p η i
  have hV : s ^ 2 / T ≤ (V : ℝ) := by
    obtain ⟨i, hi⟩ := ha
    have hai : 1 ≤ a i ^ 2 := by nlinarith [sq_abs (a i)]
    have hvi : 0 ≤ (p : ℝ) * η i := mul_nonneg p.property.1.le (Nat.cast_nonneg _)
    have hsum : a i ^ 2 * ((p : ℝ) * η i) ≤ (V : ℝ) := by
      dsimp [V, gaussianVariance]
      simp only [NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_mk]
      exact Finset.single_le_sum (fun j _ => mul_nonneg (sq_nonneg _) (mul_nonneg p.property.1.le (Nat.cast_nonneg _))) (Finset.mem_univ i)
    exact (hvar i).trans ((by nlinarith : (p : ℝ) * η i ≤ a i ^ 2 * ((p : ℝ) * η i)).trans hsum)
  have hV0 : (0 : ℝ) < V := (by positivity : 0 < s ^ 2 / T).trans_le hV
  have hden : s / T ≤ Real.sqrt (2 * Real.pi * (V : ℝ)) := by
    have hT2 : T ≤ T ^ 2 := by nlinarith
    have hsq : (s / T) ^ 2 ≤ s ^ 2 / T := by
      rw [div_pow]
      exact div_le_div_of_nonneg_left (sq_nonneg _) hT0 hT2
    have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.one_le_pi_div_two]
    have hV' : (V : ℝ) ≤ 2 * Real.pi * V := by nlinarith
    exact (Real.le_sqrt (by positivity) (by positivity)).mpr ((hsq.trans hV).trans hV')
  have h := Analysis.gaussian_linear_strip (gaussianMean p η α) a (gaussianVariance p η)
    (show 0 < V from hV0) b R hR
  have hratio : 2 * R / Real.sqrt (2 * Real.pi * (V : ℝ)) ≤ 2 * R * T / s := by
    have hh := div_le_div_of_nonneg_left (show 0 ≤ 2 * R by positivity) (show 0 < s / T by positivity) hden
    simpa only [div_div_eq_mul_div] using hh
  simp only [V, NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_mk] at hratio
  exact h.trans hratio

end MajorityDynamics.Binomial.Approximation
