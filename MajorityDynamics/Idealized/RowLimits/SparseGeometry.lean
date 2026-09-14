import MajorityDynamics.Idealized.RowLimits.GeometryLocal
import MajorityDynamics.Binomial.SparseRange
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Topology Set
open scoped BigOperators
namespace MajorityDynamics.Idealized.RowLimits
open Universal Analysis Binomial Binomial.Approximation
variable {n : ℕ}
theorem density_scale_lower_power_sparse (θ T K : ℝ) (L : ℕ)
    (hθ : θ < 1) (hT : 0 < T) (hK : 0 < K) :
    ∀ᶠ n : ℕ in atTop, ∀ p : Probability, SparseRange θ T n p →
      K * (Real.log n) ^ L ≤ scale n p := by
  have hn := tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog := ((isLittleO_log_rpow_rpow_atTop ((2 * L : ℕ) : ℝ)
    (by linarith : 0 < 1 - θ)).comp_tendsto hn).bound
      (show 0 < (T * K ^ 2)⁻¹ by positivity)
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlog] with n hn1 hbound
  intro p hp
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn1
  have hμ : 0 ≤ (p : ℝ) * n := mul_nonneg p.property.1.le hn0.le
  have hpow : (n : ℝ) ^ (1 - θ) = (n : ℝ) ^ (-θ) * n := by
    rw [show 1 - θ = -θ + 1 by ring, Real.rpow_add_one hn0.ne']
  have hlogpos : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hbound' : (Real.log n) ^ (2 * L) ≤
      (T * K ^ 2)⁻¹ * (n : ℝ) ^ (1 - θ) := by
    simpa only [Function.comp_apply, Real.rpow_natCast, norm_pow,
      Real.norm_of_nonneg hlogpos,
      Real.norm_of_nonneg (Real.rpow_nonneg hn0.le _)] using hbound
  have hd := mul_lt_mul_of_pos_right hp.1 hn0
  rw [mul_assoc, ← hpow] at hd
  have hsq : (K * (Real.log n) ^ L) ^ 2 ≤ (p : ℝ) * n := by
    have hh := mul_le_mul_of_nonneg_left hbound' (sq_nonneg K)
    have heq : K ^ 2 * ((T * K ^ 2)⁻¹ * (n : ℝ) ^ (1 - θ)) =
        T⁻¹ * (n : ℝ) ^ (1 - θ) := by field_simp
    rw [heq, show 2 * L = L * 2 by omega, pow_mul] at hh
    nlinarith
  exact (Real.le_sqrt (by positivity) hμ).mpr hsq
theorem eventually_size_error_small_sparse (θ T ε : ℝ) (L : ℕ)
    (hθ : θ < 1) (hT : 0 < T) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∀ p : Probability, SparseRange θ T n p →
      (Real.log n) ^ L / scale n p + 1 / n < ε := by
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) := by
    exact tendsto_one_div_atTop_nhds_zero_nat
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    density_scale_lower_power_sparse θ T (4 / ε) L hθ hT (by positivity),
    hinv.eventually (eventually_lt_nhds (show (0 : ℝ) < ε / 2 by positivity))]
    with n hn hscale hi
  refine ⟨by omega, ?_⟩
  intro p hp
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < scale n p := Real.sqrt_pos.mpr (mul_pos p.property.1 hn0)
  have hb : (Real.log n) ^ L / scale n p ≤ ε / 4 := by
    apply (div_le_iff₀ hs).mpr
    have hh := hscale p hp
    have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ ε / 4 by positivity)
    have hid : ε / 4 * (4 / ε * (Real.log n) ^ L) = (Real.log n) ^ L := by field_simp
    rwa [hid] at hh'
  linarith
theorem eventual_trial_geometry_sparse (θ T : ℝ) (ell : ℕ)
    (hθ : θ < 1) (hT : 0 < T) :
    ∀ᶠ N : ℕ in atTop, 0 < N ∧ ∀ p : Probability, SparseRange θ T N p →
      ∀ ξ : ℝ, ∀ s : History (n + 1), ∀ sizes : Local.Sizes n,
        AdmissibleSizes N p ell T ξ s sizes → ∀ t,
          0 < Local.trials sizes s t ∧
          (N : ℝ) * ν n t / 2 < (Local.trials sizes s t : ℝ) ∧
          (Local.trials sizes s t : ℝ) < 2 * N * ν n t ∧
          |normalizedVariance N sizes s t - ν n t| ≤
            Real.log N ^ ell / scale N p + 1 / N := by
  classical
  have he : ∀ᶠ N : ℕ in atTop, ∀ t : History (n + 1),
      0 < N ∧ ∀ p : Probability, SparseRange θ T N p →
        Real.log N ^ ell / scale N p + 1 / N < ν n t / 2 :=
    Filter.eventually_all.mpr (fun t => eventually_size_error_small_sparse θ T (ν n t / 2)
      ell hθ hT (div_pos (ν_positive n t) (by norm_num)))
  filter_upwards [he, eventually_ge_atTop (1 : ℕ)] with N he hN
  refine ⟨by omega, ?_⟩
  intro p hp ξ s sizes had t
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hδ : |(if s = t then 1 else 0 : ℝ)| ≤ 1 := by split_ifs <;> norm_num
  have hraw := corrected_trial_interval (N : ℝ) (sizes t) (ν n t)
    (if s = t then 1 else 0) (Real.log N ^ ell / scale N p) hn (ν_positive n t)
    hδ (admissible_close had t) ((he t).2 p hp)
  have hsz : 0 < sizes t := by
    have hpv : 0 < (N : ℝ) * ν n t / 2 := div_pos (mul_pos hn (ν_positive n t)) (by norm_num)
    have hd : 0 ≤ (if s = t then 1 else 0 : ℝ) := by split_ifs <;> norm_num
    have : (0 : ℝ) < sizes t := by linarith [hraw.1]
    exact_mod_cast this
  have hc := trials_cast sizes s t hsz
  have htr : (0 : ℝ) < Local.trials sizes s t := by rw [hc]; nlinarith [hraw.1, ν_positive n t]
  refine ⟨by exact_mod_cast htr, ?_, ?_, ?_⟩
  · simpa only [hc] using hraw.1
  · simpa only [hc] using hraw.2
  · dsimp [normalizedVariance]
    rw [hc]
    exact normalized_variance_error _ _ _ _ _ hn hδ (admissible_close had t)

end MajorityDynamics.Idealized.RowLimits
