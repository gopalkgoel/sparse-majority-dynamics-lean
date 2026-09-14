import MajorityDynamics.Probability.NeighborhoodBulk.ResidualScales
import MajorityDynamics.Probability.NeighborhoodBulk.BipartiteBandEnumeration
import MajorityDynamics.Probability.NeighborhoodBulk.SparseInputScales
import MajorityDynamics.Probability.NeighborhoodBulk.SparseBipartiteResidual

noncomputable section
open Filter
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodBulk
open FixedDegreeSampling
open MajorityDynamics.Combinatorics.DegreeRatios
open MajorityDynamics.Literature.DegreeEnumeration

theorem eventually_graph_scale_large_total_sparse (θ K : ℝ) (hθ : θ < 1) (hK : 0 < K) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, GraphBandWindow θ (1/2) K n m → 2 * n ≤ m := by
  have hpow := ((tendsto_rpow_atTop (sub_pos.mpr hθ)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop (2 * K))
  filter_upwards [eventually_ge_atTop (1 : ℕ), hpow] with n hn hp
  intro m hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have he : (n : ℝ) ^ (2 - θ) = (n : ℝ) ^ (1 - θ) * n := by
    rw [← Real.rpow_add_one hn0.ne']
    congr 1
    ring
  have hlo : (2 : ℝ) ≤ K⁻¹ * (n : ℝ) ^ (1 - θ) := by
    have hh := mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hK.le)
    have hi : K⁻¹ * (2 * K) = (2 : ℝ) := by field_simp
    rw [hi] at hh
    exact hh
  have hm' := hm.1
  rw [he, ← mul_assoc] at hm'
  have hh := (mul_le_mul_of_nonneg_right hlo hn0.le).trans hm'
  exact_mod_cast hh

theorem graph_scale_delete_sparse {θ K : ℝ} {n m d : ℕ} (_hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hK : 0 < K) (hn : 3 ≤ n) (hm : GraphBandWindow θ (1/2) K n m) (hlarge : 2 * n ≤ m)
    (hd : d ≤ n) : GraphBandWindow θ (1/2) (4 * K) (n - 1) (m - d) := by
  have hdm : d ≤ m := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hN : (0 : ℝ) < (n - 1 : ℕ) := by exact_mod_cast (by omega : 0 < n - 1)
  have hNle : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : n - 1 ≤ n)
  have hnN : (n : ℝ) ≤ 2 * (n - 1 : ℕ) := by exact_mod_cast (by omega : n ≤ 2 * (n - 1))
  have hhalf : (m : ℝ) / 2 ≤ (m - d : ℕ) := by
    have hh : 2 * d ≤ m := by omega
    have hh' : (2 : ℝ) * d ≤ m := by exact_mod_cast hh
    rw [Nat.cast_sub hdm]
    linarith
  have hpowlo := Real.rpow_le_rpow hN.le hNle (show 0 ≤ 2 - θ by linarith)
  have hpowhi : (n : ℝ) ^ (2 - (1/2 : ℝ)) ≤ 4 * ((n - 1 : ℕ) : ℝ) ^ (2 - (1/2 : ℝ)) := by
    calc
      _ ≤ (2 * ((n - 1 : ℕ) : ℝ)) ^ (2 - (1/2 : ℝ)) :=
        Real.rpow_le_rpow hn0.le hnN (by linarith)
      _ = (2 : ℝ) ^ (2 - (1/2 : ℝ)) * ((n - 1 : ℕ) : ℝ) ^ (2 - (1/2 : ℝ)) :=
        Real.mul_rpow (by norm_num) hN.le
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hN.le _)
        have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (show 2 - (1/2 : ℝ) ≤ 2 by linarith)
        simpa only [Real.rpow_two, show (2 : ℝ)^2 = 4 by norm_num] using hh
  constructor
  · have hmul := mul_le_mul_of_nonneg_left hpowlo (inv_nonneg.mpr hK.le)
    have hi : (4 * K)⁻¹ = K⁻¹ / 4 := by ring
    rw [hi]
    have hnonneg : 0 ≤ K⁻¹ * ((n - 1 : ℕ) : ℝ) ^ (2 - θ) := by positivity
    nlinarith [hm.1]
  · have hmul := mul_le_mul_of_nonneg_left hpowhi hK.le
    have hle : ((m - d : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m d
    nlinarith [hm.2]

theorem bipartite_scale_delete_sparse {θ K : ℝ} {n ell m d : ℕ} (hK : 0 < K)
    (hell : 2 ≤ ell) (hm : BipartiteBandWindow θ (1/2) K n ell m) (hlarge : 2 * n ≤ m)
    (hd : d ≤ n) : BipartiteBandWindow θ (1/2) (2 * K) n (ell - 1) (m - d) := by
  have hdm : d ≤ m := by omega
  have hell2 : (ell : ℝ) ≤ 2 * (ell - 1 : ℕ) := by exact_mod_cast (by omega : ell ≤ 2 * (ell - 1))
  have hhalf : (m : ℝ) / 2 ≤ (m - d : ℕ) := by
    have hh : (2 : ℝ) * d ≤ m := by exact_mod_cast (by omega : 2 * d ≤ m)
    rw [Nat.cast_sub hdm]
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hi : (n : ℝ) / (2 * K) = ((n : ℝ) / K) / 2 := by ring
    rw [hi]
    linarith [hm.1]
  · have he : ((ell - 1 : ℕ) : ℝ) ≤ ell := by exact_mod_cast Nat.sub_le ell 1
    have hnonneg : 0 ≤ K * (n : ℝ) := by positivity
    nlinarith [hm.2.1]
  · have hi : (2 * K)⁻¹ = K⁻¹ / 2 := by ring
    rw [hi]
    nlinarith [hm.2.2.1]
  · have he : ((m - d : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m d
    have hnonneg : 0 ≤ K * (n : ℝ) ^ (2 - (1/2 : ℝ)) := by positivity
    nlinarith [hm.2.2.2]

theorem eventually_graph_residual_scale_sparse (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, SparseDensityWindow θ T n p →
      ∀ (m : ℤ) (d : Fin n → ℤ), GraphInput T n p m d → ∀ v : Fin n,
        GraphBandWindow θ (1/2) (16 * T) (n - 1) (m.toNat - (d v).toNat) := by
  filter_upwards [eventually_graph_input_scale_sparse θ T hθlo hθhi hT,
    eventually_graph_scale_large_total_sparse θ (4 * T) hθhi (by linarith),
    eventually_ge_atTop (3 : ℕ)] with n hscale hlarge hn
  intro p hp m d hd v
  have hs := hscale p hp m d hd
  have hdegree : (d v).toNat ≤ n := by have := (hd.1 v).2; omega
  simpa only [show 4 * (4 * T) = 16 * T by ring] using
    graph_scale_delete_sparse (by linarith) hθhi (by linarith : 0 < 4 * T) hn hs
      (hlarge m.toNat hs) hdegree

theorem eventually_bipartite_residual_scale_sparse (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, SparseDensityWindow θ T n p →
      ∀ (ell m : ℤ) (a : Fin ell.toNat → ℤ) (b : Fin n → ℤ),
        BipartiteInput T n p ell m a b → ∀ v : Fin ell.toNat,
          BipartiteBandWindow θ (1/2) (8 * T ^ 2) n (ell.toNat - 1) (m.toNat - (a v).toNat) := by
  filter_upwards [eventually_bipartite_input_scale_sparse θ T hθlo hθhi hT,
    eventually_graph_scale_large_total_sparse θ (4 * T ^ 2) hθhi (by positivity),
    eventually_bipartite_degree_room_sparse θ T hθlo hθhi hT] with n hscale hlarge hroom
  intro p hp ell m a b hd v
  have hs := hscale p hp ell m a b hd
  have hr := hroom p hp ell m a b hd
  have hdegree : (a v).toNat ≤ n := by have := (hd.2.2.1 v).2; omega
  simpa only [show 2 * (4 * T ^ 2) = 8 * T ^ 2 by ring] using
    bipartite_scale_delete_sparse (by positivity : 0 < 4 * T ^ 2) (by linarith [hr.1]) hs
      (hlarge m.toNat hs.2.2) hdegree


end MajorityDynamics.Probability.NeighborhoodBulk

