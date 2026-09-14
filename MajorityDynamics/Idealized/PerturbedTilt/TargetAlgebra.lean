import MajorityDynamics.Idealized.PerturbedTilt.Basic

/-! The cancellation in E.5, Step 1, expressed as a smooth rational function
of five dimensionless variables. Local Lipschitz control is uniform in those
variables; no mean-map estimate or solving tilt is assumed here. -/
noncomputable section
open Filter Topology Metric
open scoped ContDiff
namespace MajorityDynamics.Idealized.PerturbedTilt

def targetFunction (u v es et : ℝ) (x : Fin 5 → ℝ) : ℝ :=
  x 1 / (x 0 + x 2 * (es + x 3)) * (es / u + et / v - (es + x 3) / x 0) +
    x 4 / (x 0 + x 2 * (es + x 3))

def targetPoint (u v : ℝ) : Fin 5 → ℝ := ![u, u * v, 0, 0, 0]

theorem targetFunction_at {u v : ℝ} (hu : u ≠ 0) (hv : v ≠ 0) (es et : ℝ) :
    targetFunction u v es et (targetPoint u v) = et := by
  simp [targetFunction, targetPoint]
  field_simp

theorem target_scalar_control {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (es et : ℝ) :
    ∃ a : ℝ, 0 < a ∧ ∃ K : ℝ, 0 < K ∧
      ∀ E : ℝ, 0 ≤ E → E < a → ∀ x : Fin 5 → ℝ,
        (∀ i, |x i - targetPoint u v i| ≤ E) →
        |targetFunction u v es et x - et| ≤ K * E := by
  have hd : ContDiffAt ℝ 1 (targetFunction u v es et) (targetPoint u v) := by
    unfold targetFunction
    have hden : targetPoint u v 0 + targetPoint u v 2 * (es + targetPoint u v 3) ≠ 0 := by
      simpa [targetPoint] using hu.ne'
    have hx : targetPoint u v 0 ≠ 0 := hu.ne'
    fun_prop
  obtain ⟨K, U, hU, hLip⟩ := hd.exists_lipschitzOnWith
  obtain ⟨a, ha, haU⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨a, ha, (K : ℝ) + 1, by positivity, ?_⟩
  intro E hE hEa x hx
  have hdist : dist x (targetPoint u v) ≤ E := by
    rw [dist_eq_norm]
    exact (pi_norm_le_iff_of_nonneg hE).mpr hx
  have hxU : x ∈ U := haU (hdist.trans_lt hEa)
  have hpU : targetPoint u v ∈ U := mem_of_mem_nhds hU
  have h := hLip.dist_le_mul x hxU (targetPoint u v) hpU
  rw [targetFunction_at hu.ne' hv.ne', Real.dist_eq] at h
  exact h.trans ((mul_le_mul_of_nonneg_left hdist K.coe_nonneg).trans (by nlinarith))

/-- Exact rescaling, including cancellation of the source-size response. -/
theorem target_rescale {N p b ns nt m e : ℝ} (hN : N ≠ 0) (hp : p ≠ 0)
    (hb : b ≠ 0) (hns : ns ≠ 0) (hnt : nt ≠ 0) (u v es et : ℝ) :
    targetFunction u v es et
      ![ns / N, m / (p * N ^ 2), b,
        (nt - ns) / (b * N) - es,
        (e - m * (1 + b * (es / u + et / v))) / (b * p * N ^ 2)] =
      (e / nt - m / ns) / (b * (p * N)) := by
  unfold targetFunction
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  have hden : ns / N + b * (es + ((nt - ns) / (b * N) - es)) = nt / N := by
    field_simp
    ring
  rw [hden]
  field_simp
  ring

end MajorityDynamics.Idealized.PerturbedTilt
