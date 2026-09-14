import MajorityDynamics.Probability.NeighborhoodBulk.BipartiteSparse
import MajorityDynamics.Probability.NeighborhoodBulk.BipartiteBandEnumeration
import MajorityDynamics.Probability.NeighborhoodBulk.SparseRegularity

noncomputable section
open Filter
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodBulk
open FixedDegreeSampling
open MajorityDynamics.Combinatorics.DegreeRatios
open MajorityDynamics.Literature.DegreeEnumeration

theorem eventually_graph_input_scale_sparse (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ,
      MajorityDynamics.Combinatorics.DegreeRatios.SparseDensityWindow θ T n p →
        ∀ (m : ℤ) (d : Fin n → ℤ), GraphInput T n p m d →
          GraphBandWindow θ (1/2) (4 * T) n m.toNat := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_graph_probability_range_sparse θ T hθlo hθhi hT,
    eventually_density_log_le_rpow_sparse θ T 2 (1 / 2) hθhi (by linarith)
      (by norm_num) (by norm_num)] with n hn hprob hsmall
  intro p hp m d hd
  have hn0 : 0 < n := by omega
  have hn0r : (0 : ℝ) < n := by exact_mod_cast hn0
  have hp0 := (hprob p hp).1
  have hx : 0 < p * n := mul_pos hp0 hn0r
  have hc := graph_input_centered hn0 hp0 hd
  have hs : 2 * Real.log n ≤ Real.sqrt (p * n) := by
    simpa only [Real.sqrt_eq_rpow] using hsmall p hp
  have hav := average_ge_half hx.le hc.1 hs
  have havhi : graphAverage n m.toNat ≤ 3 * (p * n) / 2 := by
    have hh := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg (p * n))
    nlinarith [(abs_le.mp hc.1).2, Real.sq_sqrt hx.le]
  have hmlo : p * (n : ℝ) ^ 2 / 4 ≤ m.toNat := by
    have hh := (le_div_iff₀ hn0r).mp hav
    nlinarith
  have hmhi : (m.toNat : ℝ) ≤ 3 * p * (n : ℝ) ^ 2 / 4 := by
    have hh := (div_le_iff₀ hn0r).mp havhi
    nlinarith
  have he : (n : ℝ) ^ (-θ) * (n : ℝ) ^ 2 = (n : ℝ) ^ (2 - θ) := by
    rw [← Real.rpow_two, ← Real.rpow_add hn0r]
    congr 1
    ring
  have hlo := mul_le_mul_of_nonneg_right hp.1.le (sq_nonneg (n : ℝ))
  have hhi := mul_le_mul_of_nonneg_right hp.2.le (sq_nonneg (n : ℝ))
  rw [mul_assoc, he] at hlo
  have hehi : (n : ℝ)^(-(1/2 : ℝ)) * (n : ℝ)^2 = (n : ℝ)^(2-(1/2 : ℝ)) := by
    rw [← Real.rpow_two, ← Real.rpow_add hn0r]
    congr 1
    ring
  rw [mul_assoc, hehi] at hhi
  constructor
  · have hi : (4 * T)⁻¹ = T⁻¹ / 4 := by ring
    rw [hi]
    nlinarith
  · have hpow : 0 ≤ T * (n : ℝ) ^ (2 - (1/2 : ℝ)) := by positivity
    nlinarith

theorem eventually_bipartite_input_scale_sparse (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ,
      MajorityDynamics.Combinatorics.DegreeRatios.SparseDensityWindow θ T n p →
        ∀ (ell m : ℤ) (a : Fin ell.toNat → ℤ) (b : Fin n → ℤ),
          BipartiteInput T n p ell m a b →
            BipartiteBandWindow θ (1/2) (4 * T ^ 2) n ell.toNat m.toNat := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_graph_probability_range_sparse θ T hθlo hθhi hT,
    eventually_density_log_le_rpow_sparse θ T 2 (1 / 2) hθhi (by linarith)
      (by norm_num) (by norm_num)] with n hn hprob hsmall
  intro p hp ell m a b hd
  have hT0 : 0 < T := by linarith
  have hn0 : 0 < n := by omega
  have hn0r : (0 : ℝ) < n := by exact_mod_cast hn0
  have hp0 := (hprob p hp).1
  have hx : 0 < p * n := mul_pos hp0 hn0r
  have hellr : (0 : ℝ) < ell := (div_pos hn0r hT0).trans_le hd.1
  have hell : 0 < ell := by exact_mod_cast hellr
  have heleq : (ell.toNat : ℝ) = ell := by exact_mod_cast Int.toNat_of_nonneg hell.le
  have helln : (0 : ℝ) < ell.toNat := by simpa only [heleq] using hellr
  have hc := bipartite_input_centered hn0 hell hp0 hd
  have hs : 2 * Real.log n ≤ Real.sqrt (p * n) := by
    simpa only [Real.sqrt_eq_rpow] using hsmall p hp
  have hav := average_ge_half hx.le hc.1.1 hs
  have havhi : leftAverage ell.toNat m.toNat ≤ 3 * (p * n) / 2 := by
    have hh := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg (p * n))
    nlinarith [(abs_le.mp hc.1.1).2, Real.sq_sqrt hx.le]
  have hmlo : p * n * (ell : ℝ) / 2 ≤ m.toNat := by
    have hh := (le_div_iff₀ helln).mp hav
    rw [heleq] at hh
    nlinarith
  have hmhi : (m.toNat : ℝ) ≤ 3 * p * n * (ell : ℝ) / 2 := by
    have hh := (div_le_iff₀ helln).mp havhi
    rw [heleq] at hh
    nlinarith
  have he : (n : ℝ) ^ (-θ) * (n : ℝ) ^ 2 = (n : ℝ) ^ (2 - θ) := by
    rw [← Real.rpow_two, ← Real.rpow_add hn0r]
    congr 1
    ring
  have hlo := mul_le_mul_of_nonneg_right hp.1.le (sq_nonneg (n : ℝ))
  have hhi := mul_le_mul_of_nonneg_right hp.2.le (sq_nonneg (n : ℝ))
  rw [mul_assoc, he] at hlo
  have hehi : (n : ℝ)^(-(1/2 : ℝ)) * (n : ℝ)^2 = (n : ℝ)^(2-(1/2 : ℝ)) := by
    rw [← Real.rpow_two, ← Real.rpow_add hn0r]
    congr 1
    ring
  rw [mul_assoc, hehi] at hhi
  have hK : T ≤ 4 * T ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heleq]
    exact (div_le_div_of_nonneg_left hn0r.le hT0 hK).trans hd.1
  · rw [heleq]
    exact hd.2.1.trans (mul_le_mul_of_nonneg_right hK hn0r.le)
  · have hh := mul_le_mul_of_nonneg_left hd.1 (by positivity : 0 ≤ p * n / 2)
    have hhalf : p * (n : ℝ) ^ 2 / (2 * T) ≤ (m.toNat : ℝ) := by
      have hi : p * n / 2 * ((n : ℝ) / T) = p * (n : ℝ) ^ 2 / (2 * T) := by ring
      rw [hi] at hh
      nlinarith
    have hlow := mul_le_mul_of_nonneg_right hlo (show 0 ≤ (2 * T)⁻¹ by positivity)
    have hpow : 0 ≤ (n : ℝ) ^ (2 - θ) := Real.rpow_nonneg hn0r.le _
    have hi : T⁻¹ * (n : ℝ) ^ (2 - θ) * (2 * T)⁻¹ =
        2 * ((4 * T ^ 2)⁻¹ * (n : ℝ) ^ (2 - θ)) := by ring
    rw [hi] at hlow
    have hm' : p * (n : ℝ) ^ 2 * (2 * T)⁻¹ ≤ m.toNat := by simpa only [div_eq_mul_inv] using hhalf
    have hnonneg : 0 ≤ (4 * T ^ 2)⁻¹ * (n : ℝ) ^ (2 - θ) := by positivity
    linarith
  · have hh := mul_le_mul_of_nonneg_left hd.2.1 (by positivity : 0 ≤ 3 * p * n / 2)
    have hm' : (m.toNat : ℝ) ≤ 3 * T * p * (n : ℝ) ^ 2 / 2 := by nlinarith
    have hu := mul_le_mul_of_nonneg_left hhi (show 0 ≤ 3 * T / 2 by positivity)
    have hnonneg : 0 ≤ T ^ 2 * (n : ℝ) ^ (2 - (1/2 : ℝ)) := by positivity
    nlinarith

end MajorityDynamics.Probability.NeighborhoodBulk
