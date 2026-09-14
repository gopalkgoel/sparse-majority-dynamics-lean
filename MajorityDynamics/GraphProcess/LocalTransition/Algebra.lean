import MajorityDynamics.GraphProcess.EnumerationBounds.Asymptotics
import Mathlib.Analysis.Real.Sqrt

noncomputable section
namespace MajorityDynamics.GraphProcess.LocalTransition

/-- The manuscript's child-block size error scale. -/
def sizeScale (N : ℕ) : ℝ := Real.sqrt (N : ℝ) * Real.log (N : ℝ)

/-- The manuscript's child-to-parent mass error scale. -/
def massScale (N : ℕ) (p : ℝ) : ℝ :=
  (N : ℝ)^2 * p / Real.sqrt (N : ℝ) * Real.log (N : ℝ)

/-- The manuscript's ordered next-edge error scale. -/
def edgeScale (N : ℕ) (p : ℝ) : ℝ :=
  (N : ℝ)^2 * p * Real.sqrt ((p*N)^((1:ℝ)/7)/(N : ℝ)) * Real.log (N : ℝ)

/-- Division by the common parent mass makes the product 1-Lipschitz
in the sum metric on the square `[0,m]²`. -/
theorem quotient_difference_le {m a b c d : ℝ} (hm : 0 < m)
    (ha0 : 0 ≤ a) (ham : a ≤ m) (_hb0 : 0 ≤ b) (_hbm : b ≤ m)
    (_hc0 : 0 ≤ c) (_hcm : c ≤ m) (hd0 : 0 ≤ d) (hdm : d ≤ m) :
    |a*b/m-c*d/m| ≤ |a-c|+|b-d| := by
  rw [← sub_div, abs_div, abs_of_pos hm]
  apply (div_le_iff₀ hm).mpr
  calc
    |a*b-c*d| = |a*(b-d)+(a-c)*d| := by congr 1; ring
    _ ≤ |a*(b-d)|+|(a-c)*d| := abs_add_le _ _
    _ = a*|b-d|+|a-c| *d := by rw [abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg hd0]
    _ ≤ m*|b-d|+|a-c| *m := add_le_add
      (mul_le_mul_of_nonneg_right ham (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hdm (abs_nonneg _))
    _ = (|a-c|+|b-d|)*m := by ring

/-- Exact conversion between the two error scales, retaining the original
ordered-edge convention. -/
theorem edgeScale_eq (N : ℕ) (p : ℝ) (hN : 0 < (N : ℝ)) (hp : 0 < p) :
    edgeScale N p = (p*N)^((1:ℝ)/14) * massScale N p := by
  have hx : 0 ≤ p*N := (mul_pos hp hN).le
  have hs : Real.sqrt ((p*N)^((1:ℝ)/7)) = (p*N)^((1:ℝ)/14) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
    norm_num
  unfold edgeScale massScale
  rw [Real.sqrt_div (Real.rpow_nonneg hx _), hs]
  ring

theorem sizeScale_nonneg (N : ℕ) (hN : 1 ≤ (N : ℝ)) : 0 ≤ sizeScale N :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg hN)

theorem massScale_nonneg (N : ℕ) (p : ℝ) (hN : 1 ≤ (N : ℝ)) (hp : 0 ≤ p) :
    0 ≤ massScale N p := by
  unfold massScale
  exact mul_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) hp) (Real.sqrt_nonneg _))
    (Real.log_nonneg hN)

theorem edgeScale_nonneg (N : ℕ) (p : ℝ) (hN : 1 ≤ (N : ℝ)) (hp : 0 ≤ p) :
    0 ≤ edgeScale N p := by
  unfold edgeScale
  exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hp) (Real.sqrt_nonneg _))
    (Real.log_nonneg hN)

/-- A fixed density-window threshold supplies every scalar condition used
in the deterministic local-transition calculation. -/
theorem uniform_numerical_regime {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      2 ≤ N ∧ 0 < p ∧ 0 ≤ Real.log (N : ℝ) ∧
        2 ≤ (p*N)^((1:ℝ)/14) := by
  obtain ⟨N₀,h₀⟩ := EnumerationBounds.eventually_window hθlo hθhi hT
    (L := (2:ℝ)^(14:ℝ)) (by positivity) (U := 1) zero_lt_one
    (M := 2) (by norm_num)
  refine ⟨N₀, ?_⟩
  intro N hN p hlo hhi
  obtain ⟨hN0,hp,hN2,hx,_⟩ := h₀ N hN p hlo hhi
  refine ⟨by exact_mod_cast hN2, hp, Real.log_nonneg (by linarith), ?_⟩
  have hh := Real.rpow_le_rpow (by positivity : 0 ≤ (2:ℝ)^(14:ℝ)) hx
    (by norm_num : (0:ℝ) ≤ 1/14)
  rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)] at hh
  norm_num at hh
  exact hh

end MajorityDynamics.GraphProcess.LocalTransition
