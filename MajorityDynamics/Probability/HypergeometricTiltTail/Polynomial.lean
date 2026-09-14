import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
namespace MajorityDynamics.Probability.HypergeometricTiltTail

theorem polynomial_prefactor_absorb {D T N τ : ℝ} (hD : 1 ≤ D) (hT : 0 ≤ T)
    (hN : 0 < N) (hg : 1 ≤ Real.log N) :
    (D*N)^3 * Real.exp (28*T*(|τ| *Real.log N+(Real.log N)^2)) ≤
      Real.exp ((28*T+3*(D+1))*(|τ| *Real.log N+(Real.log N)^2+Real.log N+1)) := by
  let g := Real.log N
  have hD0 : 0 ≤ D := by linarith
  have hg0 : 0 ≤ g := by dsimp [g]; linarith
  have hDe : D ≤ Real.exp D := by linarith [Real.add_one_le_exp D]
  have hbase : D*N ≤ Real.exp (D+g) := by
    rw [Real.exp_add]
    dsimp [g]
    rw [Real.exp_log hN]
    exact mul_le_mul_of_nonneg_right hDe hN.le
  have hpow := pow_le_pow_left₀ (mul_nonneg hD0 hN.le) hbase 3
  have heq : (Real.exp (D+g))^3 = Real.exp (3*(D+g)) := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [heq] at hpow
  calc
    _ ≤ Real.exp (3*(D+g))*Real.exp (28*T*(|τ| *g+g^2)) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
    _ = Real.exp (3*(D+g)+28*T*(|τ| *g+g^2)) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      change 3*(D+g)+28*T*(|τ| *g+g^2) ≤ (28*T+3*(D+1))*(|τ| *g+g^2+g+1)
      have ha : 0 ≤ |τ| *g+g^2 := by positivity
      have hb : 0 ≤ D*g := mul_nonneg hD0 hg0
      have hc : 0 ≤ T*(g+1) := mul_nonneg hT (by linarith)
      have hd : 0 ≤ (D+1)*(|τ| *g+g^2) := mul_nonneg (by linarith) ha
      nlinarith

end MajorityDynamics.Probability.HypergeometricTiltTail
