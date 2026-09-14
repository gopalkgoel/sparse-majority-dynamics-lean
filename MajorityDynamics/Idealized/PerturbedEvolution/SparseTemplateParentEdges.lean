import MajorityDynamics.Idealized.PerturbedEvolution.TemplateParentEdges
import MajorityDynamics.Idealized.PerturbedTilt.SparseAssembly
import MajorityDynamics.Idealized.PerturbedTilt.SparseAdmissibilityEdges

noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators
namespace MajorityDynamics.Idealized.PerturbedEvolution
open Universal LinearResponse PerturbedTilt RowLimits
open Binomial.Approximation (SparseRange scale)
set_option maxHeartbeats 3000000

theorem faithful_parent_edge_relative_sparse (θ T δ : ℝ) (hθlo : 1 / 2 < θ)
    (hθhi : θ < 1) (hT : 1 < T) (hδ : 0 < δ) (n ell : ℕ)
    (D : ℕ) (hDlt : n + 1 < D) :
    ∃ J : ℝ, 0 < J ∧ ∀ᶠ N : ℕ in atTop,
      ∀ p : Binomial.Probability, SparseRange θ T N p → ResponseSmall θ N p n →
      ∀ a : Process.Data, Process.Specification N p D ell a →
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ η : History (n + 1) → ℤ, ∀ e : History (n + 1) → History (n + 1) → ℤ,
      FaithfulNumericalData N (p : ℝ) T δ τ a n η e →
      ∀ s t, |(e s t : ℝ) / (a.state n).edges s t - 1| ≤ J * betaScale N p n := by
  classical
  have hT0 : 0 < T := by linarith
  obtain ⟨v, hv, hvν⟩ := RowLimits.finite_common_positive (ν n) (ν_positive n)
  obtain ⟨K, hK, href⟩ := reference_coordinates_sparse θ T hθlo hθhi hT n ell
  obtain ⟨B, hB, hBf⟩ := finite_abs_bound
    (fun st : History (n + 1) × History (n + 1) =>
      ε n st.1 / ν n st.1 + ε n st.2 / ν n st.2)
  let c := v ^ 2 / 2
  have hc : 0 < c := by dsimp [c]; positivity
  let J := T * B + T / c
  have hJ : 0 < J := by dsimp [J]; positivity
  refine ⟨J, hJ, ?_⟩
  filter_upwards [href, eventually_gt_atTop (0 : ℕ),
    eventually_rpow_neg_le δ 1 hδ zero_lt_one,
    eventually_rpow_neg_le (sparseResponseRate θ) (c / K)
      (sparseResponseRate_pos hθhi) (by positivity)] with N hrefN hN hr hsmall
  intro p hp hsub a ha τ hτ hτT η e hf s t
  have hp0 := p.property.1
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hP : 0 < (p : ℝ) * (N : ℝ) ^ 2 := by positivity
  have hτ0 : 0 < τ := (inv_pos.mpr hT0).trans_le hτ
  have hnorm := (hrefN p hp hsub (a.state n)
    (ha.estimates n (Nat.lt_of_succ_lt hDlt))).2 s t
  have hpow : K * (N : ℝ) ^ (-sparseResponseRate θ) ≤ c := by
    have h := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ K by linarith)
    have hid : K * (c / K) = c := by field_simp
    rwa [hid] at h
  have hprod : v ^ 2 ≤ ν n s * ν n t := by
    simpa only [pow_two] using mul_le_mul (hvν s) (hvν t) hv.le (ν_positive n s).le
  have hnormlo : c ≤ (a.state n).edges s t / ((p : ℝ) * (N : ℝ) ^ 2) := by
    have h := (abs_le.mp hnorm).1
    dsimp [c] at *
    linarith only [h, hpow, hprod]
  have hm : c * ((p : ℝ) * (N : ℝ) ^ 2) ≤ (a.state n).edges s t :=
    (le_div_iff₀ hP).mp hnormlo
  have herror : |(e s t : ℝ) - (a.state n).edges s t *
      (1 + τ * betaScale N p n * (ε n s / ν n s + ε n t / ν n t))| ≤
      T * betaScale N p n * (N : ℝ) ^ (-δ) * ((p : ℝ) * (N : ℝ) ^ 2) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hf.edges s t
  exact parent_edge_relative_error hP hc hm hτ0.le hτT (betaScale_nonneg _ _ _)
    (Real.rpow_nonneg hNr.le _) hr (hBf (s, t)) hT0.le hB herror

end MajorityDynamics.Idealized.PerturbedEvolution

