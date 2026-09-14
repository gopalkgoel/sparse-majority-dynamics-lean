import MajorityDynamics.Idealized.LinearResponse.Selection
import MajorityDynamics.Binomial.DensityEstimates
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Uniform absorption of every logarithmic error into `N^{-κ}`. -/

noncomputable section
open Filter Topology
open scoped BigOperators

namespace MajorityDynamics.Idealized.LinearResponse

open MajorityDynamics.Binomial.Approximation

/-- A fixed power of the logarithm is eventually below any positive power. -/
theorem eventually_log_pow_le_rpow (m : ℕ) {a K : ℝ} (ha : 0 < a) (hK : 0 < K) :
    ∀ᶠ N : ℕ in atTop, (Real.log (N : ℝ)) ^ m ≤ K * (N : ℝ) ^ a := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h := ((isLittleO_log_rpow_rpow_atTop (m : ℝ) ha).comp_tendsto hn).bound hK
  filter_upwards [eventually_ge_atTop (1 : ℕ), h] with N hN h
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  simpa only [Function.comp_apply, Real.rpow_natCast, norm_pow, Real.norm_of_nonneg hlog,
    Real.norm_of_nonneg (Real.rpow_nonneg hN0 _)] using h

/-- `c N^{-a} log^m N ≤ N^{-κ}` eventually when `κ < a`. -/
theorem eventually_poly_log_le (c a κ : ℝ) (m : ℕ) (hc : 0 ≤ c) (hκa : κ < a) :
    ∀ᶠ N : ℕ in atTop, c * (N : ℝ) ^ (-a) * (Real.log (N : ℝ)) ^ m ≤ (N : ℝ) ^ (-κ) := by
  have hpos : 0 < a - κ := sub_pos.mpr hκa
  have hK : 0 < 1 / (c + 1) := by positivity
  filter_upwards [eventually_log_pow_le_rpow m hpos hK, eventually_ge_atTop (1 : ℕ)]
    with N hlog hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hprod : (N : ℝ) ^ (-a) * (N : ℝ) ^ (a - κ) = (N : ℝ) ^ (-κ) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  have hratio : c / (c + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  calc
    c * (N : ℝ) ^ (-a) * (Real.log (N : ℝ)) ^ m
        ≤ c * (N : ℝ) ^ (-a) * (1 / (c + 1) * (N : ℝ) ^ (a - κ)) :=
      mul_le_mul_of_nonneg_left hlog (mul_nonneg hc (Real.rpow_nonneg hN0.le _))
    _ = c / (c + 1) * ((N : ℝ) ^ (-a) * (N : ℝ) ^ (a - κ)) := by ring
    _ = c / (c + 1) * (N : ℝ) ^ (-κ) := by rw [hprod]
    _ ≤ 1 * (N : ℝ) ^ (-κ) := mul_le_mul_of_nonneg_right hratio (Real.rpow_nonneg hN0.le _)
    _ = (N : ℝ) ^ (-κ) := one_mul _

/-- Two-sided bounds on `√(pN)` in the density window. -/
theorem sqrt_pN_bounds {N : ℕ} (hN : 0 < N) {θ T : ℝ} (hT : 0 < T) {p : Binomial.Probability}
    (hp : Density θ T N p) :
    (Real.sqrt T)⁻¹ * (N : ℝ) ^ ((1 - θ) / 2) ≤ Real.sqrt ((p : ℝ) * N) ∧
      Real.sqrt ((p : ℝ) * N) ≤ Real.sqrt T * (N : ℝ) ^ ((1 - θ) / 2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpow : (N : ℝ) ^ (1 - θ) = (N : ℝ) ^ (-θ) * N := by
    rw [show (1 - θ) = -θ + 1 by ring, Real.rpow_add_one hN0.ne']
  have hlo : T⁻¹ * (N : ℝ) ^ (1 - θ) < (p : ℝ) * N := by
    rw [hpow, ← mul_assoc]
    exact mul_lt_mul_of_pos_right hp.1 hN0
  have hhi : (p : ℝ) * N < T * (N : ℝ) ^ (1 - θ) := by
    rw [hpow, ← mul_assoc]
    exact mul_lt_mul_of_pos_right hp.2 hN0
  have hhalf : Real.sqrt ((N : ℝ) ^ (1 - θ)) = (N : ℝ) ^ ((1 - θ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]
    congr 1
    ring
  constructor
  · have h := Real.sqrt_le_sqrt hlo.le
    rwa [Real.sqrt_mul (inv_nonneg.mpr hT.le), Real.sqrt_inv, hhalf] at h
  · have h := Real.sqrt_le_sqrt hhi.le
    rwa [Real.sqrt_mul hT.le, hhalf] at h

/-- Basic uniform facts used throughout: positivity, logarithm, scale. -/
theorem eventually_basic (θ T : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ N : ℕ in atTop, 0 < N ∧ 2 ≤ Real.log (N : ℝ) ∧
      ∀ p : Binomial.Probability, Density θ T N p →
        1 ≤ Real.sqrt ((p : ℝ) * N) ∧ Real.sqrt ((p : ℝ) * N) ≤ N ∧ (p : ℝ) ≤ 1 / 8 := by
  have hT0 : 0 < T := by linarith
  have hlog : ∀ᶠ N : ℕ in atTop, 2 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  filter_upwards [eventually_gt_atTop (0 : ℕ), hlog,
    RowLimits.density_scale_lower_power θ T 1 0 hθhi hT0 zero_lt_one,
    density_small_parameters θ T hθlo hT0] with N hN hlog hscale hsmall
  refine ⟨hN, hlog, ?_⟩
  intro p hp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨by simpa [scale] using hscale p hp, ?_, (hsmall p hp).1⟩
  apply (Real.sqrt_le_left hN0.le).mpr
  have hh := mul_le_mul_of_nonneg_right p.property.2.le hN0.le
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith [hh, hN1, hN0]

/-- The four elementary error shapes, each absorbed into `N^{-κ}` with `κ`
the fixed response rate. -/
theorem eventually_small (θ T : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) (n m : ℕ)
    (hk : (n : ℝ) + 1 < 1 / (1 - θ)) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Binomial.Probability, Density θ T N p →
      Real.sqrt (p : ℝ) * Real.log (N : ℝ) ^ m ≤ (N : ℝ) ^ (-responseRate θ n) ∧
      (p : ℝ) * Real.log (N : ℝ) ^ m ≤ (N : ℝ) ^ (-responseRate θ n) ∧
      Real.log (N : ℝ) ^ m / Real.sqrt ((p : ℝ) * N) ≤ (N : ℝ) ^ (-responseRate θ n) ∧
      betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N) * Real.log (N : ℝ) ^ m ≤
        (N : ℝ) ^ (-responseRate θ n) := by
  have hT0 : 0 < T := by linarith
  have hden : 0 < 1 - θ := sub_pos.mpr hθhi
  have hκθ : responseRate θ n < θ / 2 := by
    have := responseRate_le_theta (θ := θ) (n := n)
    linarith
  have hθ0 : 0 < θ := by linarith [hθlo]
  have hκθ' : responseRate θ n < θ := by linarith
  have hκc : responseRate θ n < (1 - θ) / 2 := by
    have := responseRate_le_complement (θ := θ) (n := n)
    linarith
  have hkprod : ((n : ℝ) + 1) * (1 - θ) < 1 := (lt_div_iff₀ hden).mp hk
  have hκ1 : responseRate θ n < (1 - ((n : ℝ) + 1) * (1 - θ)) / 2 := by
    have := responseRate_le_first (θ := θ) (n := n)
    linarith
  have hsT : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    eventually_poly_log_le (Real.sqrt T) (θ / 2) (responseRate θ n) m hsT hκθ,
    eventually_poly_log_le T θ (responseRate θ n) m hT0.le hκθ',
    eventually_poly_log_le (Real.sqrt T) ((1 - θ) / 2) (responseRate θ n) m hsT hκc,
    eventually_poly_log_le (Real.sqrt T ^ (n + 1)) ((1 - ((n : ℝ) + 1) * (1 - θ)) / 2)
      (responseRate θ n) m (pow_nonneg hsT _) hκ1] with N hN h1 h2 h3 h4
  intro p hp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (N : ℝ) ^ m := pow_nonneg (Real.log_nonneg (by exact_mod_cast hN)) m
  obtain ⟨hslo, hshi⟩ := sqrt_pN_bounds hN hT0 hp
  have hsN : Real.sqrt (N : ℝ) = (N : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- √p ≤ √T N^{-θ/2}
    have hsqrt : Real.sqrt (p : ℝ) ≤ Real.sqrt T * (N : ℝ) ^ (-(θ / 2)) := by
      have h := Real.sqrt_le_sqrt hp.2.le
      rw [Real.sqrt_mul hT0.le, Real.sqrt_eq_rpow ((N : ℝ) ^ (-θ)), ← Real.rpow_mul hN0.le] at h
      rwa [show -θ * (1 / 2) = -(θ / 2) by ring] at h
    calc
      _ ≤ Real.sqrt T * (N : ℝ) ^ (-(θ / 2)) * Real.log (N : ℝ) ^ m :=
        mul_le_mul_of_nonneg_right hsqrt hlog
      _ ≤ _ := h1
  · calc
      (p : ℝ) * Real.log (N : ℝ) ^ m ≤ T * (N : ℝ) ^ (-θ) * Real.log (N : ℝ) ^ m :=
        mul_le_mul_of_nonneg_right hp.2.le hlog
      _ ≤ _ := h2
  · have hinv : Real.log (N : ℝ) ^ m / Real.sqrt ((p : ℝ) * N) ≤
        Real.sqrt T * (N : ℝ) ^ (-((1 - θ) / 2)) * Real.log (N : ℝ) ^ m := by
      have hsT0 : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
      have hlo0 : 0 < (Real.sqrt T)⁻¹ * (N : ℝ) ^ ((1 - θ) / 2) := by positivity
      have hspos : 0 < Real.sqrt ((p : ℝ) * N) := lt_of_lt_of_le hlo0 hslo
      rw [div_le_iff₀ hspos, Real.rpow_neg hN0.le]
      have hkey : Real.sqrt T * ((N : ℝ) ^ ((1 - θ) / 2))⁻¹ *
          ((Real.sqrt T)⁻¹ * (N : ℝ) ^ ((1 - θ) / 2)) = 1 := by
        rw [mul_mul_mul_comm, mul_inv_cancel₀ hsT0.ne',
          inv_mul_cancel₀ (Real.rpow_pos_of_pos hN0 _).ne', mul_one]
      calc
        Real.log (N : ℝ) ^ m = Real.log (N : ℝ) ^ m *
            (Real.sqrt T * ((N : ℝ) ^ ((1 - θ) / 2))⁻¹ *
              ((Real.sqrt T)⁻¹ * (N : ℝ) ^ ((1 - θ) / 2))) := by rw [hkey, mul_one]
        _ ≤ Real.log (N : ℝ) ^ m *
            (Real.sqrt T * ((N : ℝ) ^ ((1 - θ) / 2))⁻¹ * Real.sqrt ((p : ℝ) * N)) := by
          apply mul_le_mul_of_nonneg_left _ hlog
          apply mul_le_mul_of_nonneg_left hslo
          positivity
        _ = _ := by ring
    exact hinv.trans h3
  · have hpow : Real.sqrt ((p : ℝ) * N) ^ (n + 1) ≤
        Real.sqrt T ^ (n + 1) * (N : ℝ) ^ ((1 - θ) / 2 * ((n + 1 : ℕ) : ℝ)) := by
      rw [Real.rpow_mul_natCast hN0.le, ← mul_pow]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hshi (n + 1)
    have hexp : (1 - θ) / 2 * ((n + 1 : ℕ) : ℝ) =
        -((1 - ((n : ℝ) + 1) * (1 - θ)) / 2) + 1 / 2 := by
      push_cast
      ring
    have hβ : betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N) =
        Real.sqrt ((p : ℝ) * N) ^ (n + 1) / Real.sqrt (N : ℝ) := by
      unfold betaScale
      rw [pow_succ]
      ring
    have hsqrtN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
    have hbound : betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N) ≤
        Real.sqrt T ^ (n + 1) * (N : ℝ) ^ (-((1 - ((n : ℝ) + 1) * (1 - θ)) / 2)) := by
      rw [hβ, div_le_iff₀ hsqrtN, hsN, mul_assoc, ← Real.rpow_add hN0]
      rw [hexp] at hpow
      exact hpow
    calc
      _ ≤ Real.sqrt T ^ (n + 1) * (N : ℝ) ^ (-((1 - ((n : ℝ) + 1) * (1 - θ)) / 2)) *
          Real.log (N : ℝ) ^ m := mul_le_mul_of_nonneg_right hbound hlog
      _ ≤ _ := h4

end MajorityDynamics.Idealized.LinearResponse
