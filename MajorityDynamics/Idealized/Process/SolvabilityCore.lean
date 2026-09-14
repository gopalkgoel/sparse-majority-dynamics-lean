import MajorityDynamics.Analysis.Perturbation.Main
import MajorityDynamics.Analysis.Perturbation.CompactGeometry
import MajorityDynamics.Idealized.RowLimits.Comparison

/-!
# Quantitative stability at a fixed point of a strong bijection

The idealized process solves a perturbed mean equation near the universal
Gaussian tilt. A closed ball around its image is contained in the open target.
The proved D.3 theorem applies on this compact neighborhood, and inverse
Lipschitz continuity also controls displacement from the original tilt.
-/

noncomputable section
open Set Metric

namespace MajorityDynamics.Idealized.Process

open Analysis Analysis.Perturbation

/-- A uniform local solvability statement whose errors are coordinate bounds.
All constants precede the varying map, target and error. -/
theorem stable_inverse_coordinates {d : ℕ} (hd : 1 ≤ d)
    {B : Set (Space d)} (f : StrongBijection B) (γ : Space d) :
    ∃ R : ℝ, 0 < R ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε < δ →
      ∀ g : Space d → Space d, Continuous g →
        (∀ x, (∀ i, |x i| ≤ R) → ∀ i, |g x i - f.toFun x i| ≤ ε) →
        ∀ y : Space d, (∀ i, |y i - f.toFun γ i| ≤ ε) →
        ∃ x : Space d, g x = y ∧ (∀ i, |x i| ≤ R) ∧
          ∀ i, |x i - γ i| ≤ C * ε := by
  let v := f.toFun γ
  have hv : v ∈ B := f.mapsTo (mem_univ γ)
  obtain ⟨r, hr, hrB⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (f.isOpen_target.mem_nhds hv)
  let K : Set (Space d) := closedBall v r
  have hK : IsCompact K := isCompact_closedBall v r
  have hKB : K ⊆ B := hrB
  have hvK : v ∈ K := mem_closedBall_self hr.le
  let R := inverseRadius f K
  have hγR : ‖γ‖ + 1 ≤ R := by
    simpa only [v, f.left_inv] using
      norm_inv_add_one_le_inverseRadius f hK hKB hvK
  have hR : 0 < R := by linarith [norm_nonneg γ]
  let D : ℝ := (d : ℝ) + 1
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨ε₀, hε₀, C₀, hC₀, hsolve⟩ :=
    perturbation d hd B f K hK hKB D hD
  obtain ⟨L, hL, hLip⟩ := f.lipschitz_bounds hK hKB
  let δ := min ε₀ (min (r / D) (1 / C₀))
  let C := C₀ + L * D
  have hδ : 0 < δ := lt_min hε₀ (lt_min (div_pos hr hD) (div_pos zero_lt_one hC₀))
  have hC : 0 < C := by
    have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
    dsimp [C]
    exact add_pos hC₀ (mul_pos hLp hD)
  refine ⟨R, hR, δ, hδ, C, hC, ?_⟩
  intro ε hε hεδ g hg hgclose y hyclose
  have hyv : ‖y - v‖ ≤ D * ε := by
    simpa only [dist_eq_norm, D, v] using
      RowLimits.space_dist_le_of_coordinates hε.le hyclose
  have hεr : ε < r / D := hεδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hyK : y ∈ K := by
    change dist y v ≤ r
    rw [dist_eq_norm]
    exact hyv.trans (by nlinarith [(lt_div_iff₀ hD).mp hεr])
  have happrox : ∀ x, ‖x‖ ≤ inverseRadius f K → ‖g x - f.toFun x‖ ≤ D * ε := by
    intro x hx
    have hxc : ∀ i, |x i| ≤ R := fun i =>
      (show |x i| ≤ ‖x‖ by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i).trans hx
    simpa only [dist_eq_norm, D] using
      RowLimits.space_dist_le_of_coordinates hε.le (hgclose x hxc)
  obtain ⟨x, hx, hxinv⟩ := hsolve ε hε (hεδ.trans_le (min_le_left _ _))
    g hg happrox y hyK
  have hεC : C₀ * ε ≤ 1 := by
    have hh : ε < 1 / C₀ :=
      hεδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    nlinarith [(lt_div_iff₀ hC₀).mp hh]
  have hxR : ‖x‖ ≤ R := by
    have hyR := norm_inv_add_one_le_inverseRadius f hK hKB hyK
    have hn := norm_add_le (x - f.invFun y) (f.invFun y)
    rw [sub_add_cancel] at hn
    linarith
  have hinv : ‖f.invFun y - γ‖ ≤ L * (D * ε) := by
    have hh := (hLip y hyK v hvK).2
    rw [show f.invFun v = γ from f.left_inv γ] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hyv (by linarith))
  have hxγ : ‖x - γ‖ ≤ C * ε := by
    calc
      ‖x - γ‖ = ‖(x - f.invFun y) + (f.invFun y - γ)‖ := by congr 1; abel
      _ ≤ ‖x - f.invFun y‖ + ‖f.invFun y - γ‖ := norm_add_le _ _
      _ ≤ C₀ * ε + L * (D * ε) := add_le_add hxinv hinv
      _ = C * ε := by dsimp [C]; ring
  refine ⟨x, hx, ?_, ?_⟩
  · intro i
    exact (show |x i| ≤ ‖x‖ by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i).trans hxR
  · intro i
    exact (show |x i - γ i| ≤ ‖x - γ‖ by
      simpa only [Real.norm_eq_abs, PiLp.sub_apply] using
        PiLp.norm_apply_le (x - γ) i).trans hxγ

end MajorityDynamics.Idealized.Process
