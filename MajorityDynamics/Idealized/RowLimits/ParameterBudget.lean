import MajorityDynamics.Idealized.RowLimits.AssemblyInterfaces

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace MajorityDynamics.Idealized.RowLimits
open Universal Binomial Binomial.Approximation Analysis
variable {n : ℕ}

/-- Parameter errors from literal relative-size and earlier-history errors.
The decision shift is retained exactly and is not required to be bounded. -/
theorem normalized_parameter_budget {N : ℕ} (hN : 0 < N) (p : Probability)
    (sizes : Local.Sizes n) (hs : ∀ t, 0 < sizes t) (s : History (n+1))
    {e ξ R : ℝ} (he : 0 ≤ e) (hξ : 0 ≤ ξ) (hR : 0 ≤ R)
    (hsize : ∀ t, |(sizes t:ℝ)-(N:ℝ)*ν n t| ≤ (N:ℝ)*e)
    (hhist : ∀ j, |∑ t, historyMatrix s j t*(sizes t:ℝ)| ≤ ξ*(N:ℝ)/scale N p)
    (σ : Row (n+1)) (hσ : ∀ t, |σ t| ≤ R) :
    let E := e+1/(N:ℝ)+ξ+(p:ℝ)/scale N p
    let K := parameterErrorConstant n R
    (∀ t, |normalizedMean N sizes s σ t-σ t| ≤ K*E) ∧
    (∀ t, |normalizedVariance N sizes s t-ν n t| ≤ K*E) ∧
    (∀ j, |normalizedThreshold N p sizes s (historyMatrix s) j| ≤ K*E) ∧
    ∀ b j, |normalizedThreshold N p sizes s (childMatrix s b) j-
      childThreshold b (shift N p sizes) j| ≤ K*E := by
  dsimp only
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hpS : 0 ≤ (p:ℝ)/scale N p := div_nonneg p.property.1.le (Real.sqrt_nonneg _)
  have hK := parameterErrorConstant_bounds (n:=n) R hR
  have hK1 : 1 ≤ parameterErrorConstant n R := by linarith
  have hE : 0 ≤ e+1/(N:ℝ)+ξ+(p:ℝ)/scale N p := by positivity
  have hbase : e+1/(N:ℝ) ≤ e+1/(N:ℝ)+ξ+(p:ℝ)/scale N p := by linarith
  have hbal : ξ+(p:ℝ)/scale N p ≤ e+1/(N:ℝ)+ξ+(p:ℝ)/scale N p := by
    have hi : 0 ≤ 1/(N:ℝ) := by positivity
    linarith
  have hEbound : e+1/(N:ℝ)+ξ+(p:ℝ)/scale N p ≤
      parameterErrorConstant n R*(e+1/(N:ℝ)+ξ+(p:ℝ)/scale N p) :=
    le_mul_of_one_le_left hE hK1
  have hhistory (j) : |normalizedThreshold N p sizes s (historyMatrix s) j| ≤
      ξ+(p:ℝ)/scale N p := by
    have hd := normalizedThreshold_deletion N p sizes s hs (historyMatrix s) j
      (abs_historyMatrix s j s).le
    have hb := normalized_balance hN p (hhist j)
    have hh := abs_sub_le (normalizedThreshold N p sizes s (historyMatrix s) j)
      ((p:ℝ)*(∑ t, historyMatrix s j t*(sizes t:ℝ))/scale N p) 0
    simp only [sub_zero] at hh
    dsimp only [scale] at hh ⊢
    linarith
  refine ⟨?_,?_,fun j => (hhistory j).trans (hbal.trans hEbound),?_⟩
  · intro t
    have hraw := normalized_mean_error (N:ℝ) (sizes t) (σ t) (ν n t)
      (if s=t then 1 else 0) e R hn (ν_positive n t)
      (by split_ifs <;> norm_num) (hsize t) (hσ t)
    have hk : R/ν n t ≤ parameterErrorConstant n R := by
      have hv := ν_positive n t
      have hh := hK.2 t
      have hr : 0 ≤ R/ν n t := div_nonneg hR hv.le
      have hid : 2*R/ν n t = 2*(R/ν n t) := by ring
      rw [hid] at hh
      linarith
    change |σ t*(Local.trials sizes s t:ℝ)/((N:ℝ)*ν n t)-σ t| ≤ _
    rw [trials_cast sizes s t (hs t)]
    exact hraw.trans (mul_le_mul hk hbase (by positivity) (by linarith [hK.1]))
  · intro t
    have hraw := normalized_variance_error (N:ℝ) (sizes t) (ν n t)
      (if s=t then 1 else 0) e hn (by split_ifs <;> norm_num) (hsize t)
    change |(Local.trials sizes s t:ℝ)/(N:ℝ)-ν n t| ≤ _
    rw [trials_cast sizes s t (hs t)]
    exact hraw.trans (hbase.trans hEbound)
  · intro b j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · exact (normalizedThreshold_child_last p sizes s hs b).trans
        ((le_add_of_nonneg_left hξ).trans (hbal.trans hEbound))
    · simpa only [normalizedThreshold_child_castSucc,childThreshold_castSucc,sub_zero] using
        (hhistory i).trans (hbal.trans hEbound)

end MajorityDynamics.Idealized.RowLimits
