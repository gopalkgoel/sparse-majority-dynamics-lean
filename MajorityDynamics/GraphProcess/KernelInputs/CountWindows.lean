import MajorityDynamics.GraphProcess.KernelInputs.Scales

noncomputable section
namespace MajorityDynamics.GraphProcess.KernelInputs

private theorem count_scale_eq {r p : ℝ} (hr : 0 < r) (hp : 0 < p) :
    r^2*p/Real.sqrt (p*r) = r*Real.sqrt (p*r) := by
  have hs := Real.sq_sqrt (mul_pos hp hr).le
  have hz : Real.sqrt (p*r) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (mul_pos hp hr))
  apply (div_eq_iff hz).2
  nlinarith

/-- Original global count tolerance fits every original block scale, with a
fixed polynomial loss in `T`. -/
theorem count_scale_bound {N r p T : ℝ}
    (hT : 1 < T) (hp : 0 < p) (_hp1 : p ≤ 1)
    (hr : 2 ≤ r) (hNr : N/T ≤ r) (hrN : r ≤ N) :
    T*(N^2*p/Real.sqrt (p*N)) ≤ T^3*(r^2*p/Real.sqrt (p*r)) := by
  have hr0 : 0 < r := by linarith
  have hN0 : 0 < N := lt_of_lt_of_le hr0 hrN
  have hT0 : 0 < T := by linarith
  have hNT : N ≤ T*r := by nlinarith [(div_le_iff₀ hT0).1 hNr]
  have hs : Real.sqrt (p*N) ≤ T*Real.sqrt (p*r) := by
    have hssN := Real.sq_sqrt (mul_pos hp hN0).le
    have hssr := Real.sq_sqrt (mul_pos hp hr0).le
    have hT1 : T ≤ T^2 := by nlinarith
    have hpn : p*N ≤ T^2*(p*r) := by
      calc
        p*N ≤ p*(T*r) := mul_le_mul_of_nonneg_left hNT hp.le
        _ = T*(p*r) := by ring
        _ ≤ T^2*(p*r) := mul_le_mul_of_nonneg_right hT1 (mul_pos hp hr0).le
    have hn : 0 ≤ Real.sqrt (p*N) := Real.sqrt_nonneg _
    have ht : 0 ≤ T*Real.sqrt (p*r) := mul_nonneg hT0.le (Real.sqrt_nonneg _)
    apply (sq_le_sq₀ hn ht).1
    calc
      (Real.sqrt (p*N))^2 = p*N := hssN
      _ ≤ T^2*(p*r) := hpn
      _ = (T*Real.sqrt (p*r))^2 := by rw [mul_pow, hssr]
  rw [count_scale_eq hN0 hp, count_scale_eq hr0 hp]
  have hprod := mul_le_mul hNT hs (Real.sqrt_nonneg _) (mul_pos hT0 hr0).le
  have h := mul_le_mul_of_nonneg_left hprod hT0.le
  nlinarith

/-- The original cross-block total window gives the literal Appendix C count
window, uniformly in the source size `ell`. -/
theorem cross_count_window {N r p T ell m : ℝ}
    (hT : 1 < T) (hp : 0 < p) (hp1 : p ≤ 1)
    (hr : 2 ≤ r) (hNr : N/T ≤ r) (hrN : r ≤ N)
    (hm : |m-p*ell*r| ≤ T*(N^2*p/Real.sqrt (p*N))) :
    |m-p*ell*r| ≤ 2*T^3*(r^2*p/Real.sqrt (p*r)) := by
  have hs := count_scale_bound hT hp hp1 hr hNr hrN
  have hl : 0 ≤ r^2*p/Real.sqrt (p*r) := by positivity
  have hT3 : 0 ≤ T^3 := by positivity
  nlinarith

/-- Exact integer-halved internal totals retain the `r*(r-1)/2` center.
The missing diagonal term `p*r/2` is explicitly absorbed. -/
theorem internal_count_window {N r p T mOrdered mNatural : ℝ}
    (hT : 1 < T) (hp : 0 < p) (hp1 : p ≤ 1)
    (hr : 2 ≤ r) (hNr : N/T ≤ r) (hrN : r ≤ N)
    (hordered : mOrdered = 2*mNatural)
    (hm : |mOrdered-p*r^2| ≤ T*(N^2*p/Real.sqrt (p*N))) :
    |mNatural-p*r*(r-1)/2| ≤ 2*T^3*(r^2*p/Real.sqrt (p*r)) := by
  have hr0 : 0 < r := by linarith
  have hs := count_scale_bound hT hp hp1 hr hNr hrN
  have hsqrt : p ≤ Real.sqrt (p*r) := by
    apply (Real.le_sqrt hp.le (mul_pos hp hr0).le).2
    nlinarith [mul_nonneg hp.le (by linarith : 0 ≤ r-p)]
  have hpr : p*r ≤ r^2*p/Real.sqrt (p*r) := by
    rw [count_scale_eq hr0 hp]
    nlinarith [mul_le_mul_of_nonneg_left hsqrt hr0.le]
  have hid : 2*(mNatural-p*r*(r-1)/2) = (mOrdered-p*r^2)+p*r := by
    rw [hordered]
    ring
  have habs : 2*|mNatural-p*r*(r-1)/2| ≤ |mOrdered-p*r^2|+p*r := by
    have hh := abs_add_le (mOrdered-p*r^2) (p*r)
    rw [← hid, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2),
      abs_of_pos (mul_pos hp hr0)] at hh
    exact hh
  have hl : 0 ≤ r^2*p/Real.sqrt (p*r) := by positivity
  have hT3 : 1 ≤ T^3 := by nlinarith [sq_nonneg (T-1), mul_pos (by linarith : 0<T) (by nlinarith : 0<T^2-1)]
  have hL := mul_le_mul_of_nonneg_right hT3 hl
  nlinarith

end MajorityDynamics.GraphProcess.KernelInputs
