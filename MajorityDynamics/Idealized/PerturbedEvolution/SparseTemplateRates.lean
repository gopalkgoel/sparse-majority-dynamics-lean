import MajorityDynamics.Idealized.PerturbedEvolution.TemplateRates
import MajorityDynamics.Idealized.PerturbedTilt.SparseAssembly
import MajorityDynamics.Idealized.PerturbedTilt.SparseAdmissibilityEdges

noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators
namespace MajorityDynamics.Idealized.PerturbedEvolution
open Universal LinearResponse PerturbedTilt RowLimits
open Binomial.Approximation (SparseRange scale)
set_option maxHeartbeats 3000000

theorem eventually_template_rates_sparse (θ T δ : ℝ) (hθlo : 1 / 2 < θ)
    (hθhi : θ < 1) (hT : 1 < T) (hδ : 0 < δ) (n ell : ℕ)
    :
    0 < sparseTiltRate θ δ ∧ ∀ᶠ N : ℕ in atTop,
      ∀ p : Binomial.Probability, SparseRange θ T N p → ResponseSmall θ N p n →
      let r := (N : ℝ) ^ (-sparseTiltRate θ δ)
      r ≤ 1 ∧
      (N : ℝ) ^ (-sparseResponseRate θ) ≤ r ∧
      1 / scale N p ≤ r ∧
      Real.log (N : ℝ) ^ ell / scale N p ≤ r ∧
      betaScale N p n ≤ r ∧ betaScale N p (n + 1) ≤ r ∧
      1 ≤ sizeScale N p (n + 1) * r := by
  obtain ⟨hd, hdr, _⟩ := sparseTiltRate_bounds (sparseResponseRate_pos hθhi) hδ
  refine ⟨hd, ?_⟩
  filter_upwards [eventually_basic_sparse θ T hθlo hθhi hT,
    eventually_small_sparse θ T hθlo hθhi hT n ell,
    eventually_small_sparse θ T hθlo hθhi hT n 0] with N hb he he0
  intro p hp hsub
  dsimp only
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr hb.1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hb.1
  have hS := (hb.2.2 p hp).1
  have hr : (N : ℝ) ^ (-sparseResponseRate θ) ≤ (N : ℝ) ^ (-sparseTiltRate θ δ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hnext : betaScale N p (n + 1) ≤ (N : ℝ) ^ (-sparseTiltRate θ δ) := by
    rw [betaScale_succ]
    apply le_trans _ hr
    simpa using (he0 p hp hsub).2.2.2
  have hcur : betaScale N p n ≤ betaScale N p (n + 1) := by
    rw [betaScale_succ]
    exact le_mul_of_one_le_right (betaScale_nonneg _ _ _) hS
  refine ⟨Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith), hr,
    (by simpa [scale] using (he0 p hp hsub).2.2.1.trans hr),
    (he p hp hsub).2.2.1.trans hr, hcur.trans hnext, hnext, ?_⟩
  have hdhalf : sparseTiltRate θ δ ≤ (1 : ℝ) / 2 := by
    have := (show sparseResponseRate θ = (1 - θ) / 16 from rfl)
    linarith
  have hroot : (N : ℝ) ^ (sparseTiltRate θ δ) ≤ Real.sqrt (N : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN1 hdhalf
  have hsize : Real.sqrt (N : ℝ) ≤ sizeScale N p (n + 1) := by
    unfold sizeScale
    exact le_mul_of_one_le_right (Real.sqrt_nonneg _) (one_le_pow₀ hS)
  have hpos := Real.rpow_pos_of_pos hN (sparseTiltRate θ δ)
  rw [Real.rpow_neg hN.le]
  apply (le_mul_inv_iff₀ hpos).mpr
  simpa using hroot.trans hsize

end MajorityDynamics.Idealized.PerturbedEvolution

