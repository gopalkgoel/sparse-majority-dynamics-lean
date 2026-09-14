import MajorityDynamics.GraphProcess.KernelInputs.Scales

noncomputable section
namespace MajorityDynamics.GraphProcess.KernelInputs

/-- Squaring the normalized kappa threshold produces the original `1/7`
power in the graph-tail exponent. -/
theorem normalized_square_lower {x tau : ℝ} (hx : 0 ≤ x)
    (htau : x^((1:ℝ)/14) ≤ |tau|) :
    x^((1:ℝ)/7) ≤ tau^2 := by
  have hsq : (x^((1:ℝ)/14))^2 = x^((1:ℝ)/7) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  have h := sq_le_sq₀ (Real.rpow_nonneg hx _) (abs_nonneg tau) |>.2 htau
  simpa only [hsq, sq_abs] using h

/-- The literal squared normalized deviation dominates the paper's tail scale. -/
theorem kappa_tail_exponent {a p h N c : ℝ}
    (hp : 0 < p) (hh : 0 < h) (hhN : h ≤ N) (hc : 0 ≤ c)
    (hbad : (p*N)^((4:ℝ)/7) < |a-p*h|) :
    c*(p*N)^((1:ℝ)/7) ≤ c*((a-p*h)/Real.sqrt (p*h))^2 := by
  apply mul_le_mul_of_nonneg_left _ hc
  exact normalized_square_lower (mul_nonneg hp.le (hh.le.trans hhN))
    (kappa_normalized_lower hp hh hhN hbad)

/-- Exact exponential-event conversion; no statistical tail estimate is assumed. -/
theorem kappa_tail_exp_le {a p h N c : ℝ}
    (hp : 0 < p) (hh : 0 < h) (hhN : h ≤ N) (hc : 0 ≤ c)
    (hbad : (p*N)^((4:ℝ)/7) < |a-p*h|) :
    Real.exp (-c*((a-p*h)/Real.sqrt (p*h))^2) ≤
      Real.exp (-c*(p*N)^((1:ℝ)/7)) := by
  apply Real.exp_le_exp.2
  have h := kappa_tail_exponent hp hh hhN hc hbad
  nlinarith

/-- An internal undirected quadratic center doubles to the ordered diagonal
center with the exact original total. -/
theorem internal_center_double {mOrdered mNatural L : ℝ}
    (hm : 0 < mNatural) (hordered : mOrdered = 2*mNatural) :
    2*(L^2/(4*mNatural)) = L^2/mOrdered := by
  rw [hordered]
  field_simp
  ring

/-- The internal cross-cut center uses the same ordered total. -/
theorem internal_cross_center {mOrdered mNatural L R : ℝ}
    (_hm : 0 < mNatural) (hordered : mOrdered = 2*mNatural) :
    L*R/(2*mNatural) = L*R/mOrdered := by
  rw [hordered]

end MajorityDynamics.GraphProcess.KernelInputs
