import MajorityDynamics.Binomial.DensityEstimates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Elementary size and mean bounds for the varying A.2 trial counts -/

noncomputable section
namespace MajorityDynamics.Binomial.Approximation

/-- Uniform real-variable geometry, before choosing an eventual density threshold. -/
theorem trial_geometry (T n p s ref m q : ℝ)
    (hT : 1 ≤ T) (hn : 0 < n) (hp : 0 < p) (hs : 0 < s)
    (hscale : s ^ 2 = p * n) (hlarge : 4 * T ^ 2 ≤ s)
    (hsmall : p ≤ 1 / (8 * T ^ 2))
    (hreflo : n / T ≤ ref) (hrefhi : ref ≤ T * n)
    (hm : |m - ref| ≤ T * n / s) (hq : |q - p| ≤ T * p / s) :
    n / (2 * T) ≤ m ∧ m ≤ 2 * T * n ∧
    n / (4 * T) ≤ m - p * ref ∧
    |m * q - p * ref| ≤ 3 * T ^ 2 * s ∧ m * q ≤ 4 * T * s ^ 2 := by
  have hT0 : 0 < T := by linarith
  have hT2 : T ≤ T ^ 2 := by nlinarith
  have hsT : T ≤ s := by nlinarith
  have hdev := (le_div_iff₀ hs).mp hm
  have hqdev := (le_div_iff₀ hs).mp hq
  have hmlo := (abs_le.mp hm).1
  have hmhi := (abs_le.mp hm).2
  have hnear : T * n / s ≤ n / (2 * T) := by
    apply (div_le_div_iff₀ hs (by positivity)).mpr
    nlinarith [mul_nonneg hn.le (show 0 ≤ s - 2 * T ^ 2 by linarith)]
  have hreflo' := (div_le_iff₀ hT0).mp hreflo
  have hlo : n / (2 * T) ≤ m := by
    have h := hmlo.trans' (neg_le_neg hnear)
    have heq : n / T = 2 * (n / (2 * T)) := by field_simp
    rw [heq] at hreflo
    linarith
  have hhalf : n / (2 * T) ≤ T * n := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg hn.le (show 0 ≤ 2 * T ^ 2 - 1 by nlinarith)]
  have hhi : m ≤ 2 * T * n := by linarith
  have hm0 : 0 ≤ m := (by positivity : 0 ≤ n / (2 * T)).trans hlo
  have hpbound : p * (8 * T ^ 2) ≤ 1 := (le_div_iff₀ (by positivity)).mp hsmall
  have hpref : p * ref ≤ n / (4 * T) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have h := mul_le_mul_of_nonneg_left hrefhi hp.le
    nlinarith [mul_nonneg hn.le (show 0 ≤ 1 - p * (4 * T ^ 2) by nlinarith)]
  have hremaining : n / (4 * T) ≤ m - p * ref := by
    have heq : n / (2 * T) = 2 * (n / (4 * T)) := by field_simp; ring
    rw [heq] at hlo
    linarith
  have hqclose : T * p / s ≤ p := by
    apply (div_le_iff₀ hs).mpr
    simpa [mul_comm] using mul_le_mul_of_nonneg_right hsT hp.le
  have hqhi : q ≤ 2 * p := by have h := (abs_le.mp hq).2; linarith
  have hmeanhi : m * q ≤ 4 * T * s ^ 2 := by
    calc
      m * q ≤ m * (2 * p) := mul_le_mul_of_nonneg_left hqhi hm0
      _ ≤ (2 * T * n) * (2 * p) := mul_le_mul_of_nonneg_right hhi (by positivity)
      _ = _ := by rw [hscale]; ring
  have hcenter : |m * q - p * ref| ≤ 3 * T ^ 2 * s := by
    have heq : m * q - p * ref = m * (q - p) + p * (m - ref) := by ring
    rw [heq]
    calc
      _ ≤ |m * (q - p)| + |p * (m - ref)| := abs_add_le _ _
      _ = m * |q - p| + p * |m - ref| := by rw [abs_mul, abs_mul, abs_of_nonneg hm0, abs_of_pos hp]
      _ ≤ (2 * T * n) * (T * p / s) + p * (T * n / s) :=
        add_le_add (mul_le_mul hhi hq (abs_nonneg _) (by positivity)) (mul_le_mul_of_nonneg_left hm hp.le)
      _ = (2 * T ^ 2 + T) * s := by field_simp; nlinarith [hscale]
      _ ≤ 3 * T ^ 2 * s := by nlinarith
  exact ⟨hlo, hhi, hremaining, hcenter, hmeanhi⟩

end MajorityDynamics.Binomial.Approximation
