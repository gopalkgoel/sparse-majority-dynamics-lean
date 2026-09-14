import MajorityDynamics.Idealized.PerturbedTilt.Geometry
import MajorityDynamics.Local.Admissibility

/-! Deterministic consequences of F1. Earlier-history cancellation is exact. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace MajorityDynamics.Idealized.PerturbedEvolution
open Universal LinearResponse PerturbedTilt
open Binomial.Approximation (Density)

theorem faithful_earlier_imbalance {n N : ℕ} {p T δ τ : ℝ} {a : Process.Data}
    {η : History (n + 1) → ℤ} {e : History (n + 1) → History (n + 1) → ℤ}
    (hsym : Process.StateSymmetric (a.state n))
    (hf : FaithfulNumericalData N p T δ τ a n η e) (r : Fin n) :
    |∑ t, character r.castSucc t * (η t : ℝ)| ≤
      (Fintype.card (History (n + 1)) : ℝ) *
        (T * sizeScale N p n * (N : ℝ) ^ (-δ)) := by
  have href : ∑ t, character r.castSucc t * ((a.state n).sizes t : ℝ) = 0 :=
    Process.symmetric_imbalance_eq_zero (a.state n) hsym r.castSucc
  have hsum : (∑ t, character r.castSucc t *
      ((η t : ℝ) - ((a.state n).sizes t : ℝ) - τ * sizeScale N p n * ε n t)) =
      ∑ t, character r.castSucc t * (η t : ℝ) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [href]
    have hid : (∑ t, character r.castSucc t * (τ * sizeScale N p n * ε n t)) =
        τ * sizeScale N p n * ∑ t, character r.castSucc t * ε n t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring
    rw [hid, ε_earlier_signed_sum, mul_zero, sub_zero, sub_zero]
  rw [← hsum]
  simpa only [one_mul] using abs_sum_mul_le'
    (fun t => character r.castSucc t)
    (fun t => (η t : ℝ) - ((a.state n).sizes t : ℝ) - τ * sizeScale N p n * ε n t)
    1 (T * sizeScale N p n * (N : ℝ) ^ (-δ))
    (fun t => (abs_character r.castSucc t).le) hf.sizes

theorem faithful_sizes_admissible (θ T δ : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hδ : 0 < δ) (n ell : ℕ)
    (hk : (n : ℝ) + 1 < 1 / (1 - θ)) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ p : Binomial.Probability, Density θ T N p →
      ∀ a : Process.Data, Process.Specification N p (responseHorizon θ) ell a →
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ η : History (n + 1) → ℤ, ∀ e : History (n + 1) → History (n + 1) → ℤ,
      FaithfulNumericalData N (p : ℝ) T δ τ a n η e →
      (∀ s, K⁻¹ * (N : ℝ) ≤ (η s : ℝ)) ∧
      (∀ r : Fin n, |∑ t, character r.castSucc t * (η t : ℝ)| ≤
        K * N / Real.sqrt ((p : ℝ) * N)) := by
  classical
  obtain ⟨v, hv, hvle⟩ := RowLimits.finite_common_positive (ν n) (ν_positive n)
  let d : ℝ := Fintype.card (History (n + 1))
  let K : ℝ := 1 + 4 / v + d * T
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hT0 : 0 < T := by linarith
  have hK : 1 ≤ K := by
    have : 0 ≤ 4 / v := by positivity
    have : 0 ≤ d * T := mul_nonneg hd hT0.le
    dsimp [K]; linarith
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hvK : K⁻¹ ≤ v / 4 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hKpos).mpr
    dsimp [K]
    have hcancel : (4 / v) * (v / 4) = 1 := by field_simp
    nlinarith [mul_nonneg hd hT0.le, mul_nonneg (mul_nonneg hd hT0.le) hv.le]
  refine ⟨K, hK, ?_⟩
  filter_upwards [faithful_geometry θ T δ hθlo hθhi hT hδ n ell hk,
    eventually_basic θ T hθlo hθhi hT,
    eventually_small θ T hθlo hθhi hT n 0 hk,
    eventually_rpow_neg_le (responseRate θ n) 1
      (responseRate_pos hθlo hθhi hk) zero_lt_one,
    eventually_rpow_neg_le δ 1 hδ zero_lt_one] with N hgeo hbasic hsmall hrate hδsmall
  intro p hp a ha τ hτ hτT η e hf
  obtain ⟨_, hcast, _, hsize⟩ := hgeo p hp a ha τ hτ hτT η e hf
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hbasic.1
  have hS : 0 < Real.sqrt ((p : ℝ) * N) := Real.sqrt_pos.mpr (mul_pos p.property.1 hNr)
  have hbeta : betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N) ≤ 1 := by
    simpa only [pow_zero, mul_one] using (hsmall p hp).2.2.2.trans hrate
  have hscale : sizeScale N (p : ℝ) n * (N : ℝ) ^ (-δ) ≤
      N / Real.sqrt ((p : ℝ) * N) := by
    rw [sizeScale_eq N hbasic.1]
    apply (le_div_iff₀ hS).mpr
    have hprod := mul_le_mul hbeta hδsmall (Real.rpow_nonneg hNr.le _) (by norm_num : (0 : ℝ) ≤ 1)
    have := mul_le_mul_of_nonneg_right hprod hNr.le
    nlinarith
  refine ⟨?_, ?_⟩
  · intro s
    have hl := hsize.sizes_lower s
    rw [hcast s] at hl
    have := mul_le_mul_of_nonneg_right hvK hNr.le
    have := mul_le_mul_of_nonneg_left (hvle s) hNr.le
    nlinarith
  · intro r
    have hb := faithful_earlier_imbalance
      (ha.symmetry n (Nat.lt_of_succ_lt (level_succ_lt_horizon hk))) hf r
    have hm := mul_le_mul_of_nonneg_left hscale (mul_nonneg hd hT0.le)
    have hDK : d * T ≤ K := by
      have : 0 ≤ 4 / v := by positivity
      dsimp [K]; linarith
    have hfin := mul_le_mul_of_nonneg_right hDK (div_nonneg hNr.le hS.le)
    dsimp [d] at hm hfin
    calc
      _ ≤ _ := hb
      _ = (Fintype.card (History (n + 1)) : ℝ) * T * (sizeScale N (p : ℝ) n * (N : ℝ) ^ (-δ)) := by ring
      _ ≤ _ := hm.trans hfin
      _ = _ := by ring

end MajorityDynamics.Idealized.PerturbedEvolution
