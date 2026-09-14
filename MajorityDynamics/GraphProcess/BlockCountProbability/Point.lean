import MajorityDynamics.GraphProcess.GoodArrayProbability.CentralBinomial

noncomputable section

namespace MajorityDynamics.GraphProcess.BlockCountProbability

open Binomial Binomial.Approximation
open MajorityDynamics.Probability.FixedSizeExponential

/-- A tracked quadratic entropy loss gives an exponential lower bound. The
constant is independent of the trial count, target and ambient size. -/
theorem point_lower_of_loss {N m k : ℕ} (q : Binomial.Probability) (D : ℝ)
    (hN : 1 ≤ N) (hk : 0 < k) (hkm : k < m) (hkN : (k : ℝ) ≤ (N : ℝ)^2)
    (hloss : ((k : ℝ)-m*(q : ℝ))^2 / (m*(q : ℝ)*(1-(q : ℝ))) ≤ D*N) :
    Real.exp (-(D+|Real.log centralAtomConstant|+1)*N) ≤ pointMass m k q := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : 0 < (N : ℝ) := by linarith
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk
  have hs : Real.sqrt (k : ℝ) ≤ N := by
    have := Real.sq_sqrt hk0.le
    have := Real.sqrt_nonneg (k : ℝ)
    nlinarith
  have hself : centralAtomConstant / N ≤
      pointMass m k (centralProbability hk hkm) :=
    (div_le_div_of_nonneg_left centralAtomConstant_pos.le
      (Real.sqrt_pos.2 hk0) hs).trans (central_binomial_point_mass_lower hk hkm)
  have hlogself := Real.log_le_log (div_pos centralAtomConstant_pos hN0) hself
  rw [Real.log_div centralAtomConstant_pos.ne' hN0.ne'] at hlogself
  have hlog := GoodArrayProbability.central_log_comparison hk hkm q
  have hlogN := Real.log_le_sub_one_of_pos hN0
  have habs := neg_abs_le (Real.log centralAtomConstant)
  have hscale := mul_nonneg (abs_nonneg (Real.log centralAtomConstant)) (sub_nonneg.2 hNR)
  have hbound : -(D+|Real.log centralAtomConstant|+1)*(N : ℝ) ≤
      Real.log (pointMass m k q) := by nlinarith
  simpa only [Real.exp_log (pointMass_pos hkm.le q)] using Real.exp_le_exp.mpr hbound

/-- The same estimate on the native binomial measure, with the open parameter
constructed from proved interior bounds. -/
theorem binomial_lower_of_loss {N m k : ℕ} (p : unitInterval) (D : ℝ)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hN : 1 ≤ N) (hk : 0 < k) (hkm : k < m) (hkN : (k : ℝ) ≤ (N : ℝ)^2)
    (hloss : ((k : ℝ)-m*(p : ℝ))^2 / (m*(p : ℝ)*(1-(p : ℝ))) ≤ D*N) :
    Real.exp (-(D+|Real.log centralAtomConstant|+1)*N) ≤
      (ProbabilityTheory.binomial m p).real {k} := by
  let q : Binomial.Probability := ⟨p, hp0, hp1⟩
  have hclosed : Binomial.closedProbability q = p := Subtype.ext rfl
  have h := point_lower_of_loss q D hN hk hkm hkN hloss
  simpa only [pointMass, hclosed] using h

end MajorityDynamics.GraphProcess.BlockCountProbability
