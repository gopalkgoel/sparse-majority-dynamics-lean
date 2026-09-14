import MajorityDynamics.Probability.NeighborhoodBulk.WeightBridges
import MajorityDynamics.Combinatorics.DegreeRatios.SparseUniform
import MajorityDynamics.Probability.NeighborhoodBulk.SparseRegularity
import MajorityDynamics.Probability.NeighborhoodBulk.ProfileBudget

/-! Uniform sparse-range preparation, preserving the original finite bounds. -/
noncomputable section
open Filter
open scoped Classical BigOperators
namespace MajorityDynamics.Probability.NeighborhoodBulk
open FixedDegreeSampling
open MajorityDynamics.Combinatorics.DegreeRatios
open MajorityDynamics.Literature.DegreeEnumeration

theorem eventually_graph_profile_sparse (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, SparseDensityWindow θ T n p →
      ∀ (m : ℤ) (d : Fin n → ℤ), GraphInput T n p m d →
        ∀ (v : Fin n) (R : Finset (Fin n)), v ∉ R → R.card = (d v).toNat →
          0 < bernoulliProduct (Finset.univ.erase v) R (fun i => (d i : ℝ) / ((n : ℝ) - 1)) ∧
          |Real.log (bernoulliProduct (Finset.univ.erase v) R (fun i => (d i : ℝ) / ((n : ℝ) - 1))) -
              (d v : ℝ) * Real.log p + p * n - graphWeight p d v R| ≤
            32 * (T + 1) * Real.log n ^ 2 := by
  filter_upwards [eventually_sparse_large_parameters θ T hθlo hθhi hT, eventually_ge_atTop (3 : ℕ),
    eventually_density_log_le_rpow_sparse θ T 2 (1 / 2) hθhi (by linarith) (by norm_num) (by norm_num)]
      with n hlarge hn hsmall
  intro p hp m d hd v R hv hR
  have hl := hlarge p hp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hx : 0 < p * n := mul_pos hl.2.2.1 hn0
  have hs : 2 * Real.log n ≤ Real.sqrt (p * n) := by simpa only [Real.sqrt_eq_rpow] using hsmall p hp
  have hdev : ∀ i, |(d i : ℝ) - p * n| ≤ Real.sqrt (p * n) * Real.log n := fun i =>
    (standardizedDegree_bound_iff p n (d i) (Real.log n) hx).mp (hd.2.2.2 i)
  have hsubset : R ⊆ Finset.univ.erase v := by
    intro i hi
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro he
    exact hv (he ▸ hi)
  have hcard : ((Finset.univ.erase v : Finset (Fin n)).card) = n - 1 := by simp
  have hk : (R.card : ℝ) = (d v : ℝ) := by
    rw [hR]
    exact_mod_cast Int.toNat_of_nonneg (hd.1 v).1
  have hh := profile_product_log_budget (Finset.univ.erase v) R (fun i => (d i : ℝ)) n T p n ((n : ℝ) - 1)
    (Real.log n) hT.le hl.2.2.1 hl.2.2.2.1 (by exact_mod_cast (by omega : 2 ≤ n)) le_rfl
    (by linarith) hl.2.1 hs (hl.2.2.2.2.1.trans (by nlinarith [hl.2.1, sq_nonneg (Real.log (n : ℝ)-1)])) (div_le_self hn0.le hT.le)
    (by rw [hcard]; omega) (by rw [hcard]; omega) hsubset
    (by rw [hk]; exact degree_le_twice_mean p n (Real.log n) (d v) hx.le hs (hdev v))
    (fun i _ => hdev i)
  simpa only [hk, graph_linearWeight p d v R hx] using hh

theorem eventually_bipartite_profile_sparse (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, SparseDensityWindow θ T n p →
      ∀ (ell m : ℤ) (a : Fin ell.toNat → ℤ) (b : Fin n → ℤ),
        BipartiteInput T n p ell m a b →
          ∀ (v : Fin ell.toNat) (R : Finset (Fin n)), R.card = (a v).toNat →
            0 < bernoulliProduct Finset.univ R (fun j => (b j : ℝ) / ell) ∧
            |Real.log (bernoulliProduct Finset.univ R (fun j => (b j : ℝ) / ell)) -
                (a v : ℝ) * Real.log p + p * n - bipartiteWeight p ell b R| ≤
              32 * (T + 1) * Real.log n ^ 2 := by
  filter_upwards [eventually_sparse_large_parameters θ T hθlo hθhi hT, eventually_ge_atTop (1 : ℕ),
    eventually_density_log_le_rpow_sparse θ T 2 (1 / 2) hθhi (by linarith) (by norm_num) (by norm_num),
    eventually_density_log_le_side_rpow_sparse θ T 2 (1 / 2) hθhi (by linarith) (by norm_num)
      (by norm_num)] with n hlarge hn hsmall hsmall'
  intro p hp ell m a b hd v R hR
  have hl := hlarge p hp
  have hT0 : 0 < T := by linarith
  have hell64 : (64 : ℝ) ≤ ell := ((le_div_iff₀ hT0).mpr hl.1).trans hd.1
  have hx : 0 < p * n := mul_pos hl.2.2.1 (by exact_mod_cast hn)
  have hy : 0 < p * ell := mul_pos hl.2.2.1 (by linarith)
  have hs : 2 * Real.log n ≤ Real.sqrt (p * n) := by simpa only [Real.sqrt_eq_rpow] using hsmall p hp
  have hsy : 2 * Real.log n ≤ Real.sqrt (p * ell) := by
    simpa only [Real.sqrt_eq_rpow] using hsmall' p hp ell hd.1
  have hdev : ∀ j, |(b j : ℝ) - p * ell| ≤ Real.sqrt (p * ell) * Real.log n := fun j =>
    (standardizedDegree_bound_iff p ell (b j) (Real.log n) hy).mp (hd.2.2.2.2.2.2.2.2 j)
  have hk : (R.card : ℝ) = (a v : ℝ) := by
    rw [hR]
    exact_mod_cast Int.toNat_of_nonneg (hd.2.2.1 v).1
  have hdevv := (standardizedDegree_bound_iff p n (a v) (Real.log n) hx).mp
    (hd.2.2.2.2.2.2.2.1 v)
  have hh := profile_product_log_budget Finset.univ R (fun j => (b j : ℝ)) n T p ell ell (Real.log n)
    hT.le hl.2.2.1 hl.2.2.2.1 (by linarith) (by linarith) le_rfl hl.2.1 hsy
    (hl.2.2.2.2.1.trans (by nlinarith [hl.2.1, sq_nonneg (Real.log (n : ℝ)-1)])) hd.1 (by simp) (by simp) (Finset.subset_univ _)
    (by rw [hk]; exact degree_le_twice_mean p n (Real.log n) (a v) hx.le hs hdevv)
    (fun j _ => hdev j)
  simpa only [hk, bipartite_linearWeight p ell b R hy] using hh

end MajorityDynamics.Probability.NeighborhoodBulk

