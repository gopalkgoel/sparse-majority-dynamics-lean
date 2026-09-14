import MajorityDynamics.Idealized.PerturbedTilt.Basic

/-! F1 implies every size, conversion, and support prerequisite uniformly. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace MajorityDynamics.Idealized.PerturbedTilt
open Universal LinearResponse
open Binomial.Approximation (Density)

def comparisonConstant (n : ℕ) (T : ℝ) : ℝ := T * (1 + ∑ s, |ε n s|)

theorem comparisonConstant_ge (n : ℕ) {T : ℝ} (hT : 0 ≤ T) : T ≤ comparisonConstant n T := by
  have h : 0 ≤ ∑ s, |ε n s| := by positivity
  unfold comparisonConstant
  nlinarith

theorem density_mono {θ T U : ℝ} {N : ℕ} {p : Binomial.Probability}
    (hT : 0 < T) (hTU : T ≤ U) (hp : Density θ T N p) : Density θ U N p := by
  have hpow : 0 ≤ (N : ℝ) ^ (-θ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨?_, hp.2.trans_le (mul_le_mul_of_nonneg_right hTU hpow)⟩
  have hInv : U⁻¹ ≤ T⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le hT hTU
  exact (mul_le_mul_of_nonneg_right hInv hpow).trans_lt hp.1

theorem faithful_size_close {n N : ℕ} {p T δ τ : ℝ} {a : Process.Data}
    {η : History (n + 1) → ℤ} {e : History (n + 1) → History (n + 1) → ℤ}
    (hT : 0 ≤ T) (hτ : 0 ≤ τ) (hτT : τ ≤ T) (hpow : (N : ℝ) ^ (-δ) ≤ 1)
    (h : FaithfulNumericalData N p T δ τ a n η e) :
    ∀ t, |(η t : ℝ) - ((a.state n).sizes t : ℝ)| ≤ comparisonConstant n T * sizeScale N p n := by
  classical
  intro t
  have hS := sizeScale_nonneg N p n
  have heps := Finset.single_le_sum (fun s _ => abs_nonneg (ε n s)) (Finset.mem_univ t)
  have h1 := abs_sub_le ((η t : ℝ) - ((a.state n).sizes t : ℝ))
    (τ * sizeScale N p n * ε n t) 0
  simp only [sub_zero, abs_mul, abs_of_nonneg hτ, abs_of_nonneg hS] at h1
  have h2 := mul_le_mul_of_nonneg_right hτT (mul_nonneg hS (abs_nonneg (ε n t)))
  have h3 := mul_le_mul_of_nonneg_left hpow (mul_nonneg hT hS)
  have h4 := mul_le_mul_of_nonneg_left heps (mul_nonneg hT hS)
  dsimp [comparisonConstant]
  nlinarith [h.sizes t]

theorem faithful_geometry (θ T δ : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hδ : 0 < δ) (n ell : ℕ) (hk : (n : ℝ) + 1 < 1 / (1 - θ)) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Binomial.Probability, Density θ T N p →
      ∀ a : Process.Data, Process.Specification N p (responseHorizon θ) ell a →
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ η : History (n + 1) → ℤ, ∀ e : History (n + 1) → History (n + 1) → ℤ,
      FaithfulNumericalData N (p : ℝ) T δ τ a n η e →
      (∀ t, 0 < η t) ∧ (∀ t, ((naturalSizes η t : ℕ) : ℝ) = (η t : ℝ)) ∧
      (∀ t, |(η t : ℝ) - ((a.state n).sizes t : ℝ)| ≤ comparisonConstant n T * sizeScale N (p : ℝ) n) ∧
      SizeFacts N p (comparisonConstant n T) n ell (a.state n).sizes (naturalSizes η) := by
  have hT0 : 0 < T := by linarith
  have hTU := comparisonConstant_ge n hT0.le
  have hU : 1 < comparisonConstant n T := hT.trans_le hTU
  filter_upwards [eventually_geometry θ (comparisonConstant n T) hθlo hθhi hU n ell 0 le_rfl hk,
    eventually_rpow_neg_le δ 1 hδ zero_lt_one] with N hgeo hpow
  intro p hp a ha τ hτ hτT η e hf
  have hpU := density_mono hT0 hTU hp
  have hτ0 : 0 < τ := (inv_pos.mpr hT0).trans_le hτ
  have hc := faithful_size_close hT0.le hτ0.le hτT hpow hf
  have hbase := (hgeo p hpU).2 a (responseHorizon θ) ha (level_succ_lt_horizon hk)
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
  apply (hgeo p hpU).2 a (responseHorizon θ) ha (level_succ_lt_horizon hk) (naturalSizes η)
  intro t
  rw [hcast t]
  exact hc t

end MajorityDynamics.Idealized.PerturbedTilt
