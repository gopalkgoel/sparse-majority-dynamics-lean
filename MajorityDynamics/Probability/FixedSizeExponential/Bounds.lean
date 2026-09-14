import MajorityDynamics.Probability.FixedSizeExponential.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Uniform smallness and quadratic-error estimates for Lemma C.5. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace MajorityDynamics.Probability.FixedSizeExponential

/-- Eventual smallness of all weights in the literal real-density range. -/
theorem eventually_weight_regime :
    ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
      ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ p : ℝ, SparseDensity θ T n p →
        0 < p ∧ p < 1 ∧ 1 ≤ Real.log (n : ℝ) ∧
          (Real.log (n : ℝ)) ^ 2 ≤ p * n ∧
          T * Real.log (n : ℝ) / Real.sqrt (p * n) ≤ 1 := by
  intro θ T hθlo hθhi hT
  have hθ : 0 < θ := by linarith
  have hT0 : 0 < T := by linarith
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun n : ℕ => T * (n : ℝ) ^ (-θ)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hθ).comp hnat).const_mul T
  have hlog := ((isLittleO_log_rpow_rpow_atTop 2 (by linarith : 0 < 1 - θ)).comp_tendsto
    hnat).bound (inv_pos.mpr (by positivity : 0 < T ^ 3))
  have hlogpos := (Real.tendsto_log_atTop.comp hnat).eventually
    (eventually_ge_atTop (1 : ℝ))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp
    ((eventually_ge_atTop (1 : ℕ)).and
      ((hupper.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))).and
        (hlogpos.and hlog)))
  refine ⟨n₀, ?_⟩
  intro n hn p hp
  obtain ⟨hn1, huppern, hlogn', hlogn⟩ := hn₀ n hn
  obtain ⟨hplo, hphi⟩ := hp
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hp0 : 0 < p :=
    (mul_pos (inv_pos.mpr hT0) (Real.rpow_pos_of_pos hnR _)).trans hplo
  have hp1 : p < 1 := hphi.trans huppern
  have hlogsq :
      (Real.log (n : ℝ)) ^ 2 ≤ (T ^ 3)⁻¹ * (n : ℝ) ^ (1 - θ) := by
    simpa only [Function.comp_apply, Real.rpow_two,
      Real.norm_of_nonneg (sq_nonneg (Real.log (n : ℝ))),
      Real.norm_of_nonneg (Real.rpow_nonneg hnR.le _)] using hlogn
  have hplower : T⁻¹ * (n : ℝ) ^ (1 - θ) < p * n := by
    have h := mul_lt_mul_of_pos_right hplo hnR
    have heq : (n : ℝ) ^ (1 - θ) = (n : ℝ) ^ (-θ) * n := by
      rw [show 1 - θ = -θ + 1 by ring, Real.rpow_add_one hnR.ne']
    rwa [mul_assoc, ← heq] at h
  have hTsq : T ^ 2 * (Real.log (n : ℝ)) ^ 2 ≤ p * n := by
    calc
      _ ≤ T ^ 2 * ((T ^ 3)⁻¹ * (n : ℝ) ^ (1 - θ)) :=
        mul_le_mul_of_nonneg_left hlogsq (sq_nonneg T)
      _ = T⁻¹ * (n : ℝ) ^ (1 - θ) := by field_simp
      _ ≤ p * n := hplower.le
  have hsq : (Real.log (n : ℝ)) ^ 2 ≤ p * n := by
    have hT2 : 1 ≤ T ^ 2 := by nlinarith
    have hmono : (Real.log (n : ℝ)) ^ 2 ≤ T ^ 2 * (Real.log (n : ℝ)) ^ 2 := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hT2
        (sq_nonneg (Real.log (n : ℝ)))
    exact hmono.trans hTsq
  have hpn : 0 < p * n := mul_pos hp0 hnR
  have hsqrt : (Real.sqrt (p * n)) ^ 2 = p * n := Real.sq_sqrt hpn.le
  have hnum : 0 ≤ T * Real.log (n : ℝ) := by positivity
  have hnum_sq : (T * Real.log (n : ℝ)) ^ 2 ≤ p * n := by
    nlinarith [hTsq]
  have hnum_sqrt : T * Real.log (n : ℝ) ≤ Real.sqrt (p * n) := by
    nlinarith [Real.sqrt_nonneg (p * n)]
  refine ⟨hp0, hp1, hlogn', hsq, ?_⟩
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hpn)).2
  simpa only [one_mul] using hnum_sqrt

/-- The quadratic term in the independent MGF is uniformly logarithmic. -/
theorem weighted_square_bound {n : ℕ} {p q T : ℝ} (hp : 0 < p) (hq : 0 ≤ q)
    (hqT : q ≤ T * p) (hpn : 0 < p * n) (hlog : 0 ≤ Real.log (n : ℝ))
    (a : Fin n → ℝ)
    (ha : ∀ i, |a i| ≤ T * Real.log (n : ℝ) / Real.sqrt (p * n)) :
    q * ∑ i, (a i) ^ 2 ≤ T ^ 3 * (Real.log (n : ℝ)) ^ 2 := by
  have hT : 0 ≤ T := nonneg_of_mul_nonneg_left (hq.trans hqT) hp
  have hsqrt : (Real.sqrt (p * n)) ^ 2 = p * n := Real.sq_sqrt hpn.le
  have hsqrt0 : 0 < Real.sqrt (p * n) := Real.sqrt_pos.mpr hpn
  let B : ℝ := T * Real.log (n : ℝ) / Real.sqrt (p * n)
  have hB : 0 ≤ B := div_nonneg (mul_nonneg hT hlog) hsqrt0.le
  have hai (i : Fin n) : (a i) ^ 2 ≤ B ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg (a i)) hB).2 (ha i)
    simpa only [sq_abs] using h
  have hsum : ∑ i, (a i) ^ 2 ≤ (n : ℝ) * B ^ 2 := by
    calc
      ∑ i, (a i) ^ 2 ≤ ∑ i, B ^ 2 := Finset.sum_le_sum (fun i _ => hai i)
      _ = (n : ℝ) * B ^ 2 := by simp
  have hsum0 : 0 ≤ ∑ i, (a i) ^ 2 := by positivity
  calc
    q * ∑ i, (a i) ^ 2 ≤ (T * p) * ∑ i, (a i) ^ 2 := by
      exact mul_le_mul_of_nonneg_right hqT hsum0
    _ ≤ (T * p) * ((n : ℝ) * B ^ 2) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = T ^ 3 * (Real.log (n : ℝ)) ^ 2 := by
      dsimp [B]
      rw [div_pow, hsqrt]
      have hn0 : (n : ℝ) ≠ 0 := (mul_ne_zero_iff.mp hpn.ne').2
      field_simp [hp.ne', hn0]


end MajorityDynamics.Probability.FixedSizeExponential
