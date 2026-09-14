import MajorityDynamics.Idealized.CriticalDay.UniformStopping
import MajorityDynamics.Binomial.SparseRange

/-! Uniform scalar stopping for the actual response scale. This selects a
bounded day from the varying density, not a density-dependent threshold. -/
noncomputable section
open Filter Topology
namespace MajorityDynamics.Idealized.CriticalDay
open Binomial.Approximation LinearResponse

theorem degree_power_band_bounds {N : ℕ} {p θ η T r : ℝ}
    (hN : 0 < N) (hT : 0 < T) (hr : 0 ≤ r)
    (hlo : T⁻¹ * (N : ℝ) ^ (-θ) < p)
    (hhi : p < T * (N : ℝ) ^ (-η)) :
    (T⁻¹) ^ r * (N : ℝ) ^ ((1 - θ) * r - 1 / 2) ≤
        (p * N) ^ r / Real.sqrt N ∧
      (p * N) ^ r / Real.sqrt N ≤
        T ^ r * (N : ℝ) ^ ((1 - η) * r - 1 / 2) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hid (a : ℝ) : (N : ℝ) ^ (-a) * N = (N : ℝ) ^ (1 - a) := by
    rw [← Real.rpow_add_one hn.ne']
    congr 1
    ring
  have hp : 0 < p := (by positivity : 0 < T⁻¹ * (N : ℝ) ^ (-θ)).trans hlo
  have hl := mul_le_mul_of_nonneg_right hlo.le hn.le
  have hu := mul_le_mul_of_nonneg_right hhi.le hn.le
  rw [mul_assoc, hid] at hl hu
  have he (A a : ℝ) (hA : 0 ≤ A) :
      (A * (N : ℝ) ^ (1 - a)) ^ r / Real.sqrt N =
        A ^ r * (N : ℝ) ^ ((1 - a) * r - 1 / 2) := by
    rw [Real.mul_rpow hA (by positivity), ← Real.rpow_mul hn.le,
      Real.sqrt_eq_rpow, mul_div_assoc, ← Real.rpow_sub hn]
  constructor
  · rw [← he (T⁻¹) θ (by positivity)]
    exact div_le_div_of_nonneg_right (Real.rpow_le_rpow (by positivity) hl hr)
      (Real.sqrt_nonneg _)
  · rw [← he T η hT.le]
    exact div_le_div_of_nonneg_right (Real.rpow_le_rpow (by positivity) hu hr)
      (Real.sqrt_nonneg _)

theorem response_scale_rpow {N : ℕ} {p : ℝ} (hp : 0 ≤ p) (j : ℕ) :
    betaScale N p j * Real.sqrt (p * N) =
      (p * N) ^ (((j : ℝ) + 1) / 2) / Real.sqrt N := by
  rw [betaScale, div_mul_eq_mul_div, ← pow_succ, Real.sqrt_eq_rpow,
    ← Real.rpow_mul_natCast (mul_nonneg hp (Nat.cast_nonneg N))]
  congr 2
  push_cast
  ring

theorem first_response_weight {N : ℕ} {p : ℝ} (hp : 0 < p) (hN : 0 < N) :
    (betaScale N p 0 * Real.sqrt (p * N)) *
        (Real.sqrt (p * N)) ^ (3 / 4 : ℝ) =
      (p * N) ^ (7 / 8 : ℝ) / Real.sqrt N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : 0 < p * N := mul_pos hp hn
  rw [response_scale_rpow hp.le, Real.sqrt_eq_rpow (p * N), ← Real.rpow_mul hx.le,
    div_mul_eq_mul_div, ← Real.rpow_add hx]
  congr 2
  norm_num

theorem eventually_stopping_scales (θ T : ℝ) (H : ℕ)
    (hθ : θ < 1) (hT : 1 < T) (hH : 1 < (H : ℝ) * (1 - θ)) :
    ∀ᶠ N : ℕ in atTop, 0 < N ∧ ∀ p : Binomial.Probability,
      SparseRange θ T N p →
      1 ≤ scale N p ∧
      (betaScale N p 0 * scale N p) * (scale N p) ^ (3 / 4 : ℝ) < 1 ∧
      1 ≤ betaScale N p H * scale N p := by
  have hT0 : 0 < T := by linarith
  have hn := tendsto_natCast_atTop_atTop (R := ℝ)
  have hu : Tendsto (fun N : ℕ => T ^ (7 / 8 : ℝ) *
      (N : ℝ) ^ (-1 / 16 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_div, mul_zero] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 16)).comp hn).const_mul
        (T ^ (7 / 8 : ℝ))
  have hex : 0 < (1 - θ) * (((H : ℝ) + 1) / 2) - 1 / 2 := by nlinarith
  have hl : Tendsto (fun N : ℕ => (T⁻¹) ^ (((H : ℝ) + 1) / 2) *
      (N : ℝ) ^ ((1 - θ) * (((H : ℝ) + 1) / 2) - 1 / 2)) atTop atTop :=
    ((tendsto_rpow_atTop hex).comp hn).const_mul_atTop (by positivity)
  have hx : Tendsto (fun N : ℕ => T⁻¹ * (N : ℝ) ^ (1 - θ)) atTop atTop :=
    ((tendsto_rpow_atTop (by linarith : 0 < 1 - θ)).comp hn).const_mul_atTop (by positivity)
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    hu.eventually (eventually_lt_nhds zero_lt_one), hl.eventually_ge_atTop 1,
    hx.eventually_ge_atTop 1] with N hN hu hl hx
  refine ⟨by omega, ?_⟩
  intro p hp
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp0 : 0 < (p : ℝ) := p.property.1
  have hbase : 1 ≤ (p : ℝ) * N := by
    have hh := mul_le_mul_of_nonneg_right hp.1.le hn0.le
    have he : (N : ℝ) ^ (-θ) * N = (N : ℝ) ^ (1 - θ) := by
      rw [← Real.rpow_add_one hn0.ne']; congr 1; ring
    rw [mul_assoc, he] at hh
    exact hx.trans hh
  refine ⟨?_, ?_, ?_⟩
  · exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by simpa using hbase)
  · rw [show scale N p = Real.sqrt ((p : ℝ) * N) from rfl,
      first_response_weight hp0 (by omega)]
    have hh := (degree_power_band_bounds (by omega) hT0
      (by norm_num : (0 : ℝ) ≤ 7 / 8) hp.1 hp.2).2
    norm_num at hh
    exact hh.trans_lt (by simpa only [neg_div] using hu)
  · rw [show scale N p = Real.sqrt ((p : ℝ) * N) from rfl, response_scale_rpow hp0.le]
    exact hl.trans (degree_power_band_bounds (by omega) hT0 (by positivity) hp.1 hp.2).1

/-- The first crossing occurs by H with response in the safe terminal window.
All earlier response scales are bounded by s^(-3/4). -/
theorem uniform_stopping_index (θ T : ℝ) (H : ℕ)
    (hθ : θ < 1) (hT : 1 < T) (hH : 1 < (H : ℝ) * (1 - θ)) :
    ∀ᶠ N : ℕ in atTop, 0 < N ∧ ∀ p : Binomial.Probability,
      SparseRange θ T N p →
      let s := scale N p
      let t := s ^ (1 / 4 : ℝ)
      1 ≤ t ∧ t ^ 4 = s ∧ ∃ j : ℕ, 0 < j ∧ j ≤ H ∧
        1 ≤ (betaScale N p j * s) * t ^ 3 ∧ betaScale N p j * s < t ∧
        ∀ i < j, betaScale N p i * s < s ^ (-3 / 4 : ℝ) := by
  filter_upwards [eventually_stopping_scales θ T H hθ hT hH] with N hN
  refine ⟨hN.1, ?_⟩
  intro p hp
  obtain ⟨hs, h0, hlast⟩ := hN.2 p hp
  dsimp only
  have hs0 : 0 < scale N p := zero_lt_one.trans_le hs
  have ht3 : (scale N p ^ (1 / 4 : ℝ)) ^ (3 : ℕ) = scale N p ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_mul_natCast hs0.le]
    norm_num
  refine ⟨Real.one_le_rpow hs (by norm_num), ?_, ?_⟩
  · rw [← Real.rpow_mul_natCast hs0.le]
    norm_num
  have hfirst : betaScale N p 0 * scale N p < scale N p ^ (-3 / 4 : ℝ) := by
    rw [neg_div, Real.rpow_neg hs0.le, ← one_div]
    exact (lt_div_iff₀ (Real.rpow_pos_of_pos hs0 _)).mpr h0
  have hterminal : scale N p ^ (-3 / 4 : ℝ) ≤ betaScale N p H * scale N p :=
    (Real.rpow_le_one_of_one_le_of_nonpos hs (by norm_num)).trans hlast
  obtain ⟨j, hj0, hjH, hjlo, hjhi, hprev⟩ := first_geometric_crossing
    (fun j => betaScale N p j * scale N p) H hs0 hfirst hterminal
    (by intro j; dsimp [betaScale, scale]; rw [pow_succ]; ring)
  refine ⟨j, hj0, hjH, ?_, ?_, hprev⟩
  · rw [ht3]
    have hh := mul_le_mul_of_nonneg_right hjlo
      (Real.rpow_nonneg hs0.le (3 / 4 : ℝ))
    rw [← Real.rpow_add hs0] at hh
    norm_num at hh
    exact hh
  · have he : scale N p * scale N p ^ (-3 / 4 : ℝ) = scale N p ^ (1 / 4 : ℝ) := by
      nth_rw 1 [← Real.rpow_one (scale N p)]
      rw [← Real.rpow_add hs0]
      norm_num
    exact hjhi.trans_eq he

end MajorityDynamics.Idealized.CriticalDay
