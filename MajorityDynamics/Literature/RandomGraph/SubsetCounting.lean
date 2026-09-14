import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import MajorityDynamics.Literature.RandomGraph.JumblednessAnalysis

/-! Entropy bounds for the number of vertex subsets of prescribed sizes. -/

namespace MajorityDynamics.Literature.RandomGraph

/-- The usual entropy upper bound for a binomial coefficient, derived from one
nonnegative term of the exponential series. -/
lemma choose_le_exp_entropy {N s : ℕ} (hs : 0 < s) (hsN : s ≤ N) :
    (N.choose s : ℝ) ≤ Real.exp ((s : ℝ) * (1 + Real.log ((N : ℝ) / s))) := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (hs.trans_le hsN)
  have hseries := Real.pow_div_factorial_le_exp (s : ℝ) hs0.le s
  have hchoose := Nat.choose_le_pow_div (α := ℝ) s N
  have hscale : (0 : ℝ) ≤ ((N : ℝ) / s) ^ s := by positivity
  have hbound := mul_le_mul_of_nonneg_left hseries hscale
  have heq : ((N : ℝ) / s) ^ s * ((s : ℝ) ^ s / s.factorial) =
      (N : ℝ) ^ s / s.factorial := by
    rw [div_pow]
    field_simp
  rw [heq] at hbound
  refine hchoose.trans (hbound.trans_eq ?_)
  have hp : ((N : ℝ) / s) ^ s =
      Real.exp ((s : ℝ) * Real.log ((N : ℝ) / s)) := by
    rw [Real.exp_nat_mul, Real.exp_log (div_pos hN0 hs0)]
  rw [hp, ← Real.exp_add]
  congr 1
  ring

/-- For `u ≤ w`, both choices of vertex subsets are controlled by the entropy
of the larger size. This is the combinatorial factor in the discrepancy union
bound, including pairs with nonempty intersection. -/
lemma choose_mul_choose_le_exp_entropy {N u w : ℕ}
    (hu : 0 < u) (huw : u ≤ w) (hwN : w ≤ N) :
    (N.choose u : ℝ) * (N.choose w : ℝ) ≤
      Real.exp (2 * (w : ℝ) * (1 + Real.log ((N : ℝ) / w))) := by
  have hw : 0 < w := hu.trans_le huw
  have hmono := subsetEntropy_mono (N := (N : ℝ)) (u := (u : ℝ)) (w := (w : ℝ))
    (by exact_mod_cast hu) (by exact_mod_cast huw) (by exact_mod_cast hwN)
  have hproduct := mul_le_mul (choose_le_exp_entropy hu (huw.trans hwN))
    (choose_le_exp_entropy hw hwN) (by positivity : (0 : ℝ) ≤ N.choose w)
    (Real.exp_pos _).le
  rw [← Real.exp_add] at hproduct
  refine hproduct.trans (Real.exp_le_exp.mpr ?_)
  dsimp [subsetEntropy] at hmono
  linarith

end MajorityDynamics.Literature.RandomGraph
