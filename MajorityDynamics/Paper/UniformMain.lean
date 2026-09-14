import MajorityDynamics.Paper.SparseMain
import MajorityDynamics.Paper.DenseUniform

/-! Full uniform-density endpoint, parallel to the unchanged paper theorem.
The auxiliary sparse result and the independently checked FKM dense estimate
meet at a constant multiple of N^{-1/2}. -/
noncomputable section
open MeasureTheory
open scoped Classical ENNReal
namespace MajorityDynamics.Paper

/-- For every T⁻¹ N^{-θ} ≤ p ≤ 1, with a single threshold independent of p,
τ and the deterministic initial coloring. FKM supplies the dense range. -/
theorem uniform_main : UniformMainTheorem := by
  intro θ T hθlo hθhi hT ε hε
  obtain ⟨L,hL,ND,hD⟩ := UniformInternal.dense_uniform T hT ε hε
  let B := max (2*T) (L+1)
  have hTB : T < B := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hB : 1 < B := hT.trans hTB
  have hLB : L ≤ B := (by linarith : L ≤ L+1).trans (le_max_right _ _)
  have hi : B⁻¹ ≤ T⁻¹ := (inv_le_inv₀ (by linarith) (by linarith)).mpr hTB.le
  obtain ⟨NS,hS⟩ := UniformInternal.sparse_main_closed_density θ B hθlo hθhi hB ε hε
  refine ⟨max NS ND, ?_⟩
  intro N hN p τ c hp hτ hτT hc
  by_cases hcap : (p:ℝ) ≤ B * (N:ℝ)^(-(1/2:ℝ))
  · exact hS N (by omega) p τ c
      ((mul_le_mul_of_nonneg_right hi (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans hp)
      hcap (hi.trans hτ) (hτT.trans hTB.le) hc
  · have hpd : L / Real.sqrt N ≤ (p:ℝ) := by
      have he : L / Real.sqrt N = L * (N:ℝ)^(-(1/2:ℝ)) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_neg (Nat.cast_nonneg N), div_eq_mul_inv]
      rw [he]
      exact (mul_le_mul_of_nonneg_right hLB (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans
        (not_le.mp hcap).le
    have hdense := hD N (by omega) p τ c hpd hτ hc
    refine (measure_mono ?_).trans hdense
    intro G hfail hfour
    apply hfail
    apply allplus_later_day G c (d := 5) (by norm_num) ?_ hfour
    have hα : 0 < 1-θ := by linarith
    have hfloor : 1 ≤ ⌊1/(1-θ)⌋₊ := by
      apply Nat.le_floor
      apply (le_div_iff₀ hα).2
      have hθ0 : 0 < θ := by linarith
      simpa using (show 1-θ ≤ 1 by linarith)
    unfold uniformConvergenceDay expansionDay
    omega

end MajorityDynamics.Paper
