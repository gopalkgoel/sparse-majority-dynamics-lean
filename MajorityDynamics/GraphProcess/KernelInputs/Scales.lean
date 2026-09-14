import MajorityDynamics.GraphProcess.LocalTransition.Algebra

noncomputable section
namespace MajorityDynamics.GraphProcess.KernelInputs

/-- The literal Appendix C.1 error scale at a reference block of real size `r`. -/
def localEdgeScale (r p : ℝ) : ℝ :=
  r^2 * p * Real.sqrt ((p*r)^((1:ℝ)/7)/r) * Real.log r

/-- Positive-factor form of the local error, useful for comparison across blocks. -/
theorem localEdgeScale_eq {r p : ℝ} (hr : 0 < r) (hp : 0 < p) :
    localEdgeScale r p = r * Real.sqrt r * p *
      (p*r)^((1:ℝ)/14) * Real.log r := by
  have hs : Real.sqrt ((p*r)^((1:ℝ)/7)) = (p*r)^((1:ℝ)/14) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : 0 ≤ p*r)]
    norm_num
  have hsr := Real.sq_sqrt hr.le
  have hs0 : Real.sqrt r ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hr)
  unfold localEdgeScale
  rw [Real.sqrt_div (Real.rpow_nonneg (by positivity) _), hs]
  field_simp
  rw [hsr]

/-- Every local C.1 scale is bounded by the unchanged global edge scale. -/
theorem localEdgeScale_le_global {N : ℕ} {r p : ℝ}
    (hr : 1 ≤ r) (hrN : r ≤ N) (hp : 0 < p) :
    localEdgeScale r p ≤ LocalTransition.edgeScale N p := by
  have hr0 : 0 < r := by linarith
  have hN0 : 0 < (N : ℝ) := lt_of_lt_of_le hr0 hrN
  change localEdgeScale r p ≤ localEdgeScale (N : ℝ) p
  rw [localEdgeScale_eq hr0 hp, localEdgeScale_eq hN0 hp]
  have hpow : (p*r)^((1:ℝ)/14) ≤ (p*N)^((1:ℝ)/14) :=
    Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hrN hp.le) (by norm_num)
  have hbase : r * Real.sqrt r ≤ (N : ℝ) * Real.sqrt N :=
    mul_le_mul hrN (Real.sqrt_le_sqrt hrN) (Real.sqrt_nonneg _) hN0.le
  exact mul_le_mul
    (mul_le_mul (mul_le_mul_of_nonneg_right hbase hp.le) hpow
      (Real.rpow_nonneg (by positivity) _) (by positivity))
    (Real.log_le_log hr0 hrN) (Real.log_nonneg hr) (by positivity)

/-- Internal undirected errors double when expressed as ordered diagonal counts. -/
theorem doubled_localEdgeScale_le_global {N : ℕ} {r p T : ℝ}
    (hr : 1 ≤ r) (hrN : r ≤ N) (hp : 0 < p) (hT : 1 ≤ T) :
    2 * localEdgeScale r p ≤ 2*T * LocalTransition.edgeScale N p := by
  have h := localEdgeScale_le_global hr hrN hp
  have hn := LocalTransition.edgeScale_nonneg N p (hr.trans hrN) hp.le
  nlinarith

/-- Conversion of the literal local deviation event, including its multiplicative
constant, to the global edge scale. -/
theorem local_edge_event {N : ℕ} {r p C error : ℝ}
    (hr : 1 ≤ r) (hrN : r ≤ N) (hp : 0 < p) (hC : 0 ≤ C)
    (he : |error| ≤ C * localEdgeScale r p) :
    |error| ≤ C * LocalTransition.edgeScale N p :=
  he.trans (mul_le_mul_of_nonneg_left (localEdgeScale_le_global hr hrN hp) hC)

/-- The doubled diagonal event uses the actual factor two, not a redefined count. -/
theorem doubled_local_edge_event {N : ℕ} {r p C T error : ℝ}
    (hr : 1 ≤ r) (hrN : r ≤ N) (hp : 0 < p) (hC : 0 ≤ C) (hT : 1 ≤ T)
    (he : |error| ≤ C * localEdgeScale r p) :
    |2*error| ≤ (2*T*C) * LocalTransition.edgeScale N p := by
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hs := doubled_localEdgeScale_le_global hr hrN hp hT
  nlinarith [mul_le_mul_of_nonneg_left hs hC]

/-- Reconstruction with the normalization belonging to this particular side. -/
theorem normalized_reconstruct {a p h : ℝ} (hp : 0 < p) (hh : 0 < h) :
    a = p*h + ((a-p*h)/Real.sqrt (p*h)) * Real.sqrt (p*h) := by
  rw [div_mul_cancel₀ _ (ne_of_gt (Real.sqrt_pos.2 (mul_pos hp hh)))]
  ring

/-- A square-root degree window is exactly the corresponding normalized window. -/
theorem normalized_abs_le {a p h L : ℝ} (hp : 0 < p) (hh : 0 < h)
    (ha : |a-p*h| ≤ Real.sqrt (p*h) * L) :
    |(a-p*h)/Real.sqrt (p*h)| ≤ L := by
  rw [abs_div, abs_of_pos (Real.sqrt_pos.2 (mul_pos hp hh))]
  exact (div_le_iff₀ (Real.sqrt_pos.2 (mul_pos hp hh))).2 (by nlinarith)

/-- The strict original kappa-complement event implies the normalized C.2 tail
threshold. The normalization uses the actual child size `h`, not its parent. -/
theorem kappa_normalized_lower {a p h N : ℝ}
    (hp : 0 < p) (hh : 0 < h) (hhN : h ≤ N)
    (hbad : (p*N)^((4:ℝ)/7) < |a-p*h|) :
    (p*N)^((1:ℝ)/14) ≤ |(a-p*h)/Real.sqrt (p*h)| := by
  have hN : 0 < N := lt_of_lt_of_le hh hhN
  have hx : 0 < p*N := mul_pos hp hN
  have hs : 0 < Real.sqrt (p*h) := Real.sqrt_pos.2 (mul_pos hp hh)
  have hid : (p*N)^((1:ℝ)/14) * Real.sqrt (p*N) = (p*N)^((4:ℝ)/7) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
    norm_num
  have hb : (p*N)^((1:ℝ)/14) * Real.sqrt (p*h) ≤ (p*N)^((4:ℝ)/7) := by
    rw [← hid]
    exact mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hhN hp.le)) (Real.rpow_nonneg hx.le _)
  rw [abs_div, abs_of_pos hs]
  exact (le_div_iff₀ hs).2 (hb.trans hbad.le)

end MajorityDynamics.GraphProcess.KernelInputs
