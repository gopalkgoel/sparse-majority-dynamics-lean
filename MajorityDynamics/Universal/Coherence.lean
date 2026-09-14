import MajorityDynamics.Universal.ResponseAlgebra
import MajorityDynamics.Analysis.GaussianSplit.WhiteningBasic

/-!
# Coherence of the universal response

The earlier signed response sums vanish by sibling cancellation. The last
signed sum is positive by induction, so the Gaussian positive-split theorem
applies to the coefficient vector fixed by the conditional covariance system.
All conditioning here is bridged to the original history and child events.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open MajorityDynamics.Analysis
open scoped RealInnerProductSpace

namespace MajorityDynamics.Universal

open GaussianSplit

/-- The Gaussian split observable is exactly the paper's linear statistic. -/
theorem linear_beta (n : ℕ) (s : History (n + 1)) (x : Row (n + 1)) :
    linear (WithLp.toLp 2 (β n s)) x = B n s x := by
  simp [linear, B, responseLinear, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- The defining covariance system tested against any linear form. -/
theorem beta_covarianceBilin (n : ℕ) (s : History (n + 1)) (v : Row (n + 1)) :
    covarianceBilin (historyLaw n s) (WithLp.toLp 2 (β n s)) v =
      ∑ t, v t * ε n t := by
  have hreg := historyLaw_regular n s
  let := hreg.probability
  rw [ConditionalGaussian.covarianceBilin_eq_covMatrix _ hreg.memLp_two]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  calc
    _ = v t * ∑ u, β n s u * conditionalCovariance n s u t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      change β n s u * v t * conditionalCovariance n s u t = _
      ring
    _ = v t * ε n t := by rw [β_spec]

/-- One coherence step from the positive current lead. The analytic premise
is supplied by the proved Gaussian split result at the final assembly. -/
theorem ε_child_pos_of_affine_split (hSplit : AffineSplitTheorem) (n : ℕ)
    (hlead : 0 < ∑ t, character (Fin.last n) t * ε n t)
    (s : History (n + 1)) : 0 < ε (n + 1) (append s false) := by
  let h : Fin n → Row (n + 1) := fun r =>
    sign (bits (n + 1) s r.succ) • characterVector r.castSucc
  have hE : affineHistory h (fun _ => 0) = historyCone s := by
    ext x
    simp only [affineHistory, mem_ofPred_eq, zero_add, mem_historyCone,
      h, linear, real_inner_smul_left, ← imbalance_eq_inner]
  have hC : affineHistory h (fun _ => 0) ∩
      {x | 0 < (0 : ℝ) + linear (characterVector (Fin.last n)) x} = childCone s false := by
    rw [hE]
    simp only [childCone, sign_false, one_mul, zero_add, linear, ← imbalance_eq_inner]
  have hhistory : ConditionalGaussian.condition
      (ConditionalGaussian.gaussianLaw (covariance (ν n)) (γ n s)) (historyCone s) =
        historyLaw n s := by
    exact (history_condition_eq s (ν n) (ν_positive n) (γ n s)).symm
  have hchild : ConditionalGaussian.condition
      (ConditionalGaussian.gaussianLaw (covariance (ν n)) (γ n s)) (childCone s false) =
        childLaw n s false := by
    exact (child_condition_eq s false (ν n) (ν_positive n) (γ n s)).symm
  have hzero : ∀ r, covarianceBilin
      (ConditionalGaussian.condition
        (ConditionalGaussian.gaussianLaw (covariance (ν n)) (γ n s))
        (affineHistory h (fun _ => 0))) (WithLp.toLp 2 (β n s)) (h r) = 0 := by
    intro r
    rw [hE, hhistory, beta_covarianceBilin]
    change (∑ t, (sign (bits (n + 1) s r.succ) * character r.castSucc t) * ε n t) = 0
    simp only [mul_assoc, ← Finset.mul_sum, ε_earlier_signed_sum, mul_zero]
  have hpos : 0 < covarianceBilin
      (ConditionalGaussian.condition
        (ConditionalGaussian.gaussianLaw (covariance (ν n)) (γ n s))
        (affineHistory h (fun _ => 0))) (WithLp.toLp 2 (β n s))
          (characterVector (Fin.last n)) := by
    rw [hE, hhistory, beta_covarianceBilin]
    exact hlead
  have hsplit := hSplit _ n (covariance (ν n)) (covariance_posDef _ (ν_positive n))
    (γ n s) h (fun _ => 0) (WithLp.toLp 2 (β n s)) (characterVector (Fin.last n)) 0
    (by rw [hE]; exact history_mass_pos s (ν n) (ν_positive n) (γ n s))
    (by rw [hC]; exact child_mass_pos s false (ν n) (ν_positive n) (γ n s)) hzero hpos
  rw [hC, hE, hchild, hhistory] at hsplit
  simp only [linear_beta] at hsplit
  rw [ε_recursion]
  exact mul_pos (ν_positive _ _) hsplit

/-- All-day coherence, reduced solely to the closed analytic split theorem. -/
theorem coherence_of_affine_split (hSplit : AffineSplitTheorem) :
    ∀ n (s : History (n + 1)),
      0 < ε (n + 1) (append s false) ∧ ε (n + 1) (append s true) < 0 := by
  intro n
  induction n with
  | zero =>
    intro s
    have hpos := ε_child_pos_of_affine_split hSplit 0
      (by rw [ε_initial_lead]; norm_num) s
    exact ⟨hpos, by rw [ε_sibling_neg]; exact neg_neg_of_pos hpos⟩
  | succ n ih =>
    intro s
    have hlead := ε_lead_pos_of_children (n + 1) (fun t => (ih t).1)
    have hpos := ε_child_pos_of_affine_split hSplit (n + 1) hlead s
    exact ⟨hpos, by rw [ε_sibling_neg]; exact neg_neg_of_pos hpos⟩

/-- The signed response lead is positive on every day, including day one. -/
theorem ε_lead_pos_of_affine_split (hSplit : AffineSplitTheorem) (n : ℕ) :
    0 < ∑ t, character (Fin.last n) t * ε n t := by
  cases n with
  | zero => rw [ε_initial_lead]; norm_num
  | succ n =>
    exact ε_lead_pos_of_children (n + 1) (fun s => (coherence_of_affine_split hSplit n s).1)

end MajorityDynamics.Universal
