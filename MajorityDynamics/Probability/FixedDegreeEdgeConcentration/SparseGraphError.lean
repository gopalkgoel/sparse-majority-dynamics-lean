import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.GraphError
noncomputable section
namespace MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Numerics
open Literature.EdgeProbabilities
theorem graph_error_absolute_sparse {N x K : ℝ} {n m : ℕ}
    (hN : 0 < N) (hx : 1 ≤ x) (hK : 1 ≤ K)
    (hn : N/K ≤ (n:ℝ)) (hD : graphAverage n m ≤ 2*K*x)
    (_hlog : Real.log n ≤ x) :
    graphErrorScale n m ≤ (2*K^3+8*K^6)*x/N^2 := by
  have hx0 : 0 < x := by linarith
  have hK0 : 0 < K := by linarith
  have hn0 : (0:ℝ) < n := (div_pos hN hK0).trans_le hn
  have hi : (n:ℝ)⁻¹ ≤ K/N := by
    rw [← one_div (n:ℝ)]
    have hh := (div_le_iff₀ hK0).mp hn
    exact (div_le_div_iff₀ hn0 hN).mpr (by nlinarith)
  have hh := mul_le_mul hD
    (pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (n:ℝ)⁻¹) hi 2)
    (by positivity : (0:ℝ) ≤ ((n:ℝ)⁻¹)^2) (by positivity : 0 ≤ 2*K*x)
  calc
    _ = graphAverage n m*((n:ℝ)⁻¹)^2 := by simp [graphErrorScale, div_eq_mul_inv]
    _ ≤ (2*K*x)*(K/N)^2 := hh
    _ = 2*K^3*x/N^2 := by ring
    _ ≤ (2*K^3+8*K^6)*x/N^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg N)
      nlinarith [show 0 ≤ 8*K^6*x by positivity]

theorem graph_error_relative_sparse {N p x K a b : ℝ} {n m : ℕ}
    (hN : 0 < N) (hx : 1 ≤ x) (hxp : x = p*N) (hK : 1 ≤ K)
    (hnl : N/K ≤ (n:ℝ)) (hnu : (n:ℝ) ≤ K*N)
    (hD : 0 < graphAverage n m) (hDu : graphAverage n m ≤ 2*K*x)
    (hlog : Real.log n ≤ x) (ha : x/(2*K) ≤ a) (hb : x/(2*K) ≤ b) :
    graphErrorScale n m ≤ ((2*K^3+8*K^6)*(8*K^4))*epsilon N p*
      (a*b/(graphAverage n m*(n:ℝ))) := by
  have hK0 : 0 < K := by linarith
  have hx0 : 0 < x := by linarith
  have hn0 : (0:ℝ) < n := (div_pos hN hK0).trans_le hnl
  have hw := graph_weight_lower hN hx0 hK0 hD hn0 hDu hnu ha hb
  have he : 1/N ≤ epsilon N p := by
    unfold epsilon
    rw [← hxp]
    exact div_le_div_of_nonneg_right (Real.one_le_rpow hx (by norm_num)) hN.le
  have he0 : 0 ≤ epsilon N p := (by positivity : 0 ≤ 1/N).trans he
  have habs := graph_error_absolute_sparse hN hx hK hnl hDu hlog
  calc
    _ ≤ (2*K^3+8*K^6)*x/N^2 := habs
    _ = ((2*K^3+8*K^6)*(8*K^4))*((1/N)*(x/(8*K^4*N))) := by field_simp
    _ ≤ ((2*K^3+8*K^6)*(8*K^4))*(epsilon N p*(a*b/(graphAverage n m*(n:ℝ)))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul he hw (by positivity : 0 ≤ x/(8*K^4*N)) he0
    _ = _ := by ring

end MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Numerics
