import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Analytic estimates for the random-graph discrepancy union bound

These elementary estimates retain the logarithmic Bennett exponent needed
for very unequal subset sizes. They are proved here from Mathlib's checked
logarithm inequalities, rather than assumed as a concentration theorem.
-/

namespace MajorityDynamics.Literature.RandomGraph
open Set

lemma bennett_ge_half_mul_log {z : ℝ} (hz : 0 ≤ z) :
    z / 2 * Real.log (1 + z) ≤ (1 + z) * Real.log (1 + z) - z := by
  have h := Real.le_log_one_add_of_nonneg hz
  have hp : 0 < z + 2 := by positivity
  have h' := (div_le_iff₀ hp).mp h
  nlinarith

lemma log_one_add_le_mul_log_one_add_div {A y : ℝ} (hA : 0 ≤ A) (hy : 1 ≤ y) :
    Real.log (1 + A) ≤ y * Real.log (1 + A / y) := by
  have hy0 : 0 < y := by linarith
  have hi : 0 ≤ 1 - y⁻¹ := by
    have : y⁻¹ ≤ 1 := (inv_le_one₀ hy0).mpr hy
    linarith
  have h := strictConcaveOn_log_Ioi.concaveOn.2
    (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show 1 + A ∈ Ioi 0 by change 0 < 1 + A; positivity)
    hi (inv_nonneg.mpr hy0.le) (show (1 - y⁻¹) + y⁻¹ = 1 by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at h
  have he : (1 - y⁻¹) * 1 + y⁻¹ * (1 + A) = 1 + A / y := by ring
  rw [he] at h
  have hm := mul_le_mul_of_nonneg_left h hy0.le
  simpa [← mul_assoc, hy0.ne'] using hm

noncomputable def subsetEntropy (N s : ℝ) : ℝ := s * (1 + Real.log (N / s))

lemma subsetEntropy_mono {N u w : ℝ} (hu : 0 < u) (huw : u ≤ w) (hwN : w ≤ N) :
    subsetEntropy N u ≤ subsetEntropy N w := by
  have hw : 0 < w := hu.trans_le huw
  have hN : 0 < N := hw.trans_le hwN
  have hl : 0 ≤ Real.log (N / w) := Real.log_nonneg ((one_le_div hw).mpr hwN)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hw hu)
  have hm := mul_le_mul_of_nonneg_left hlog hu.le
  have hid : Real.log (N / u) = Real.log (N / w) + Real.log (w / u) := by
    rw [Real.log_div hN.ne' hu.ne', Real.log_div hN.ne' hw.ne',
      Real.log_div hw.ne' hu.ne']
    ring
  have he : u * (w / u - 1) = w - u := by field_simp
  rw [he] at hm
  dsimp [subsetEntropy]
  rw [hid]
  nlinarith [mul_le_mul_of_nonneg_right huw hl]

lemma log_le_subsetEntropy {N w : ℝ} (hw : 1 ≤ w) (hwN : w ≤ N) :
    Real.log N ≤ subsetEntropy N w := by
  have h := subsetEntropy_mono (N := N) (by norm_num : (0 : ℝ) < 1) hw hwN
  simp only [subsetEntropy, div_one, one_mul] at h
  dsimp [subsetEntropy]
  linarith

lemma entropy_log_le {x : ℝ} (hx : 1 ≤ x) :
    1 + Real.log x ≤ 3 * Real.log (1 + x) := by
  have hx0 : 0 < x := by linarith
  have hl := Real.log_le_log hx0 (show x ≤ 1 + x by linarith)
  have hh := Real.le_log_one_add_of_nonneg (by linarith : 0 ≤ x)
  have hp : 0 < x + 2 := by positivity
  have hh' := (div_le_iff₀ hp).mp hh
  have hz : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
  have hlo : (1 : ℝ) / 2 ≤ Real.log (1 + x) := by
    by_contra! hn
    nlinarith
  linarith

/-- Scaling the sharp Bennett exponent pays for subset entropy even when
one subset is much larger than the other. -/
lemma scaled_bennett_entropy {N w y K : ℝ} (hw : 0 < w) (hwN : w ≤ N)
    (hy : 1 ≤ y) (hK : 1 ≤ K) :
    K / 3 * subsetEntropy N w ≤
      (K * y * w) * Real.log (1 + K * N / (y * w)) := by
  have hN : 0 < N := hw.trans_le hwN
  have hy0 : 0 < y := by linarith
  have hK0 : 0 < K := by linarith
  have hx : 1 ≤ N / w := (one_le_div hw).mpr hwN
  have hs := log_one_add_le_mul_log_one_add_div
    (A := N / w) (by positivity) hy
  have he : (N / w) / y = N / (y * w) := by field_simp
  rw [he] at hs
  have hratio : N / (y * w) ≤ K * N / (y * w) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have hlog := Real.log_le_log (by positivity : 0 < 1 + N / (y * w))
    (show 1 + N / (y * w) ≤ 1 + K * N / (y * w) by linarith)
  have hh := entropy_log_le hx
  have hf : 1 + Real.log (N / w) ≤
      3 * y * Real.log (1 + K * N / (y * w)) := by
    nlinarith [mul_le_mul_of_nonneg_left hlog hy0.le]
  have hm := mul_le_mul_of_nonneg_left hf (show 0 ≤ K * w / 3 by positivity)
  dsimp [subsetEntropy]
  nlinarith

end MajorityDynamics.Literature.RandomGraph
