import MajorityDynamics.Idealized.PerturbedTilt.Target

/-! Uniform error rates used by the deterministic template comparison. -/
noncomputable section
open Filter Topology
namespace MajorityDynamics.Idealized.PerturbedEvolution
open LinearResponse PerturbedTilt
open Binomial.Approximation (Density scale)

theorem betaScale_succ (N : ℕ) (p : ℝ) (n : ℕ) :
    betaScale N p (n + 1) = betaScale N p n * Real.sqrt (p * N) := by
  unfold betaScale
  rw [pow_succ]
  ring

theorem sizeScale_succ_eq (N : ℕ) (hN : 0 < N) (p : ℝ) (n : ℕ) :
    sizeScale N p (n + 1) = N * betaScale N p (n + 1) := by
  rw [sizeScale_eq N hN p (n + 1), mul_comm]

/-- The solved-tilt rate is already smaller than all response error rates. -/
theorem eventually_template_rates (θ T δ : ℝ) (hθlo : 1 / 2 < θ)
    (hθhi : θ < 1) (hT : 1 < T) (hδ : 0 < δ) (n ell : ℕ)
    (hk : (n : ℝ) + 1 < 1 / (1 - θ)) :
    0 < tiltRate θ δ n ∧ ∀ᶠ N : ℕ in atTop,
      ∀ p : Binomial.Probability, Density θ T N p →
      let r := (N : ℝ) ^ (-tiltRate θ δ n)
      r ≤ 1 ∧
      (N : ℝ) ^ (-responseRate θ n) ≤ r ∧
      1 / scale N p ≤ r ∧
      Real.log (N : ℝ) ^ ell / scale N p ≤ r ∧
      betaScale N p n ≤ r ∧ betaScale N p (n + 1) ≤ r ∧
      1 ≤ sizeScale N p (n + 1) * r := by
  obtain ⟨hd, hdr, _⟩ := tiltRate_bounds (responseRate_pos hθlo hθhi hk) hδ
  refine ⟨hd, ?_⟩
  filter_upwards [eventually_basic θ T hθlo hθhi hT,
    eventually_small θ T hθlo hθhi hT n ell hk,
    eventually_small θ T hθlo hθhi hT n 0 hk] with N hb he he0
  intro p hp
  dsimp only
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr hb.1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hb.1
  have hS := (hb.2.2 p hp).1
  have hr : (N : ℝ) ^ (-responseRate θ n) ≤ (N : ℝ) ^ (-tiltRate θ δ n) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hnext : betaScale N p (n + 1) ≤ (N : ℝ) ^ (-tiltRate θ δ n) := by
    rw [betaScale_succ]
    apply le_trans _ hr
    simpa using (he0 p hp).2.2.2
  have hcur : betaScale N p n ≤ betaScale N p (n + 1) := by
    rw [betaScale_succ]
    exact le_mul_of_one_le_right (betaScale_nonneg _ _ _) hS
  refine ⟨Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith), hr,
    (by simpa [scale] using (he0 p hp).2.2.1.trans hr),
    (he p hp).2.2.1.trans hr, hcur.trans hnext, hnext, ?_⟩
  have hdhalf : tiltRate θ δ n ≤ (1 : ℝ) / 2 := by
    have := responseRate_le_complement (θ := θ) (n := n)
    linarith
  have hroot : (N : ℝ) ^ (tiltRate θ δ n) ≤ Real.sqrt (N : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN1 hdhalf
  have hsize : Real.sqrt (N : ℝ) ≤ sizeScale N p (n + 1) := by
    unfold sizeScale
    exact le_mul_of_one_le_right (Real.sqrt_nonneg _) (one_le_pow₀ hS)
  have hpos := Real.rpow_pos_of_pos hN (tiltRate θ δ n)
  rw [Real.rpow_neg hN.le]
  apply (le_mul_inv_iff₀ hpos).mpr
  simpa using hroot.trans hsize

end MajorityDynamics.Idealized.PerturbedEvolution
