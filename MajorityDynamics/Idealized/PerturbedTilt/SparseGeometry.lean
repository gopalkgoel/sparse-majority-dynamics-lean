import MajorityDynamics.Idealized.PerturbedTilt.Geometry
import MajorityDynamics.Idealized.LinearResponse.SparseMain

noncomputable section
open Filter Topology
open scoped BigOperators
namespace MajorityDynamics.Idealized.PerturbedTilt
open Universal LinearResponse
open Binomial.Approximation (SparseRange scale)
set_option maxHeartbeats 2000000

theorem faithful_geometry_sparse (θ T δ : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hδ : 0 < δ) (n ell : ℕ) (D : ℕ) (hDlt : n + 1 < D) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Binomial.Probability, SparseRange θ T N p → ResponseSmall θ N p n →
      ∀ a : Process.Data, Process.Specification N p D ell a →
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ η : History (n + 1) → ℤ, ∀ e : History (n + 1) → History (n + 1) → ℤ,
      FaithfulNumericalData N (p : ℝ) T δ τ a n η e →
      (∀ t, 0 < η t) ∧ (∀ t, ((naturalSizes η t : ℕ) : ℝ) = (η t : ℝ)) ∧
      (∀ t, |(η t : ℝ) - ((a.state n).sizes t : ℝ)| ≤ comparisonConstant n T * sizeScale N (p : ℝ) n) ∧
      SizeFacts N p (comparisonConstant n T) n ell (a.state n).sizes (naturalSizes η) := by
  have hT0 : 0 < T := by linarith
  have hTU := comparisonConstant_ge n hT0.le
  have hU : 1 < comparisonConstant n T := hT.trans_le hTU
  filter_upwards [eventually_geometry_sparse θ (comparisonConstant n T) hθlo hθhi hU n ell 0 le_rfl,
    eventually_rpow_neg_le δ 1 hδ zero_lt_one] with N hgeo hpow
  intro p hp hsub a ha τ hτ hτT η e hf
  have hpU := RowLimits.sparseRange_enlarge hT0 hTU hp
  have hτ0 : 0 < τ := (inv_pos.mpr hT0).trans_le hτ
  have hc := faithful_size_close hT0.le hτ0.le hτT hpow hf
  have hbase := (hgeo p hpU hsub).2 a D ha hDlt
    (a.state n).sizes (fun t => by
      rw [sub_self, abs_zero]
      exact mul_nonneg (by linarith) (sizeScale_nonneg _ _ _))
  have hpos : ∀ t, 0 < η t := by
    intro t
    have h1 := (abs_le.mp (hc t)).1
    have h2 := hbase.ref_lower t
    have h3 := hbase.perturbation t
    have h4 : 0 ≤ (N : ℝ) * ν n t := mul_nonneg (Nat.cast_nonneg _) (ν_positive n t).le
    have : (0 : ℝ) < η t := by linarith
    exact_mod_cast this
  have hcast : ∀ t, ((naturalSizes η t : ℕ) : ℝ) = (η t : ℝ) := by
    intro t
    exact_mod_cast Int.toNat_of_nonneg (hpos t).le
  refine ⟨hpos, hcast, hc, ?_⟩
  apply (hgeo p hpU hsub).2 a D ha hDlt (naturalSizes η)
  intro t
  rw [hcast t]
  exact hc t

end MajorityDynamics.Idealized.PerturbedTilt

