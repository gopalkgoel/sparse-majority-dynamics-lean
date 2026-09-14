import MajorityDynamics.Probability.NeighborhoodBulk.BipartiteResidual
import MajorityDynamics.Combinatorics.DegreeRatios.SparseUniform
import MajorityDynamics.Probability.NeighborhoodBulk.SparseRegularity
import MajorityDynamics.Probability.NeighborhoodBulk.SparseResidualRegularity

/-! Uniform sparse-range preparation, preserving the original finite bounds. -/
noncomputable section
open Filter
open scoped Classical BigOperators
namespace MajorityDynamics.Probability.NeighborhoodBulk
open FixedDegreeSampling
open MajorityDynamics.Combinatorics.DegreeRatios
open MajorityDynamics.Literature.DegreeEnumeration

theorem eventually_bipartite_degree_room_sparse (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, SparseDensityWindow θ T n p →
      ∀ (ell m : ℤ) (a : Fin ell.toNat → ℤ) (b : Fin n → ℤ),
        BipartiteInput T n p ell m a b → 4 ≤ ell.toNat ∧
          (∀ i, 2 ≤ (a i).toNat ∧ (a i).toNat ≤ n - 2) ∧
          ∀ j, 2 ≤ (b j).toNat ∧ (b j).toNat ≤ ell.toNat - 2 := by
  filter_upwards [eventually_sparse_large_parameters θ T hθlo hθhi hT, eventually_ge_atTop (4 : ℕ),
    eventually_density_log_le_rpow_sparse θ T 2 (1 / 2) hθhi (by linarith) (by norm_num) (by norm_num),
    eventually_density_log_le_side_rpow_sparse θ T 2 (1 / 2) hθhi (by linarith) (by norm_num)
      (by norm_num)] with n hlarge hn hsmall hsmall'
  intro p hp ell m a b hd
  have hl := hlarge p hp
  have hT0 : 0 < T := by linarith
  have hell64 : (64 : ℝ) ≤ ell := ((le_div_iff₀ hT0).mpr hl.1).trans hd.1
  have hell : 0 < ell := by exact_mod_cast (by linarith : (0 : ℝ) < ell)
  have heleq : (ell.toNat : ℝ) = ell := by exact_mod_cast Int.toNat_of_nonneg hell.le
  have hell4 : 4 ≤ ell.toNat := by
    have hh : (4 : ℝ) ≤ ell.toNat := by rw [heleq]; linarith
    exact_mod_cast hh
  have hx : 0 < p * n := mul_pos hl.2.2.1 (by exact_mod_cast (by omega : 0 < n))
  have hy : 0 < p * ell := mul_pos hl.2.2.1 (by exact_mod_cast hell)
  refine ⟨hell4, ?_, ?_⟩
  · intro i
    apply natural_degree_room n (a i).toNat p (Real.log n) hn hl.2.2.1 hl.2.2.2.1 hl.2.1
      (by simpa only [Real.sqrt_eq_rpow] using hsmall p hp)
    have he : ((a i).toNat : ℝ) = (a i : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (hd.2.2.1 i).1
    rw [he]
    exact (standardizedDegree_bound_iff p n (a i) (Real.log n) hx).mp (hd.2.2.2.2.2.2.2.1 i)
  · intro j
    apply natural_degree_room ell.toNat (b j).toNat p (Real.log n) hell4 hl.2.2.1 hl.2.2.2.1 hl.2.1
      (by simpa only [heleq, Real.sqrt_eq_rpow] using hsmall' p hp ell hd.1)
    have he : ((b j).toNat : ℝ) = (b j : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (hd.2.2.2.1 j).1
    rw [he, heleq]
    exact (standardizedDegree_bound_iff p ell (b j) (Real.log n) hy).mp (hd.2.2.2.2.2.2.2.2 j)

theorem eventually_bipartite_residual_regular_sparse (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, SparseDensityWindow θ T n p →
      ∀ (ell m : ℤ) (a : Fin ell.toNat → ℤ) (b : Fin n → ℤ),
        BipartiteInput T n p ell m a b →
          ∀ (v : Fin ell.toNat) (S : Finset (Fin n)), S.card = (a v).toNat →
            bipartiteAdmissible (fun i => (a i).toNat) (fun j => (b j).toNat) v S ∧
              BipartiteSourceData (7 / 12) (ell.toNat - 1) n (m.toNat - (a v).toNat)
                (leftResidualFin (fun i => (a i).toNat) v) (residualRightDegree (fun j => (b j).toNat) S) ∧
              CenteredControl (leftResidualFin (fun i => (a i).toNat) v)
                (leftAverage (ell.toNat - 1) (m.toNat - (a v).toNat)) (p * n) (2 * Real.log n) ∧
              CenteredControl (residualRightDegree (fun j => (b j).toNat) S)
                (rightAverage n (m.toNat - (a v).toNat)) (p * ell) (2 * Real.log n) := by
  filter_upwards [eventually_sparse_large_parameters θ T hθlo hθhi hT,
    eventually_ge_atTop (3 : ℕ), eventually_bipartite_degree_room_sparse θ T hθlo hθhi hT,
    eventually_density_log_le_rpow_sparse θ T 4 (1 / 2) hθhi (by linarith) (by norm_num) (by norm_num),
    eventually_density_log_le_rpow_sparse θ T 8 (7 / 12 - 1 / 2) hθhi (by linarith) (by norm_num) (by norm_num),
    eventually_density_log_le_side_rpow_sparse θ T 4 (1 / 2) hθhi (by linarith) (by norm_num) (by norm_num),
    eventually_density_log_le_side_rpow_sparse θ T 8 (7 / 12 - 1 / 2) hθhi (by linarith) (by norm_num)
      (by norm_num)] with n hlarge hn hroom hsmall hspread hsmall' hspread'
  intro p hp ell m a b hd v S hS
  have hl := hlarge p hp
  have hr := hroom p hp ell m a b hd
  have hsum := bipartite_input_nat_sums hd
  have hn0 : 0 < n := by omega
  have helln : 0 < ell.toNat := by linarith [hr.1]
  have hell : 0 < ell := by omega
  have hx : 0 < p * n := mul_pos hl.2.2.1 (by exact_mod_cast hn0)
  have hy : 0 < p * ell := mul_pos hl.2.2.1 (by exact_mod_cast hell)
  have hR : bipartiteAdmissible (fun i => (a i).toNat) (fun j => (b j).toNat) v S :=
    ⟨hS, fun j _ => (show 1 ≤ 2 by omega).trans (hr.2.2 j).1⟩
  have hres := bipartite_residual_sums (fun i => (a i).toNat) (fun j => (b j).toNat)
    v S hR m.toNat hsum.2.1 hsum.2.2
  have hleft : (∑ i, leftResidualFin (fun j => (a j).toNat) v i) = m.toNat - (a v).toNat := by
    have hh := leftResidualFin_sum (fun j => (a j).toNat) v
    rw [hsum.2.1] at hh
    omega
  have hdevA : ∀ i, |((a i).toNat : ℝ) - p * n| ≤ Real.sqrt (p * n) * Real.log n := by
    intro i
    have he : ((a i).toNat : ℝ) = (a i : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (hd.2.2.1 i).1
    rw [he]
    exact (standardizedDegree_bound_iff p n (a i) (Real.log n) hx).mp (hd.2.2.2.2.2.2.2.1 i)
  have hdevB : ∀ j, |((b j).toNat : ℝ) - p * ell| ≤ Real.sqrt (p * ell) * Real.log n := by
    intro j
    have he : ((b j).toNat : ℝ) = (b j : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (hd.2.2.2.1 j).1
    rw [he]
    exact (standardizedDegree_bound_iff p ell (b j) (Real.log n) hy).mp (hd.2.2.2.2.2.2.2.2 j)
  have hdevB' := residualRightDegree_deviation (fun j => (b j).toNat) S hR.2
    (p * ell) (Real.sqrt (p * ell) * Real.log n) hdevB
  have hN : 0 < ell.toNat - 1 := by omega
  have : Nonempty (Fin (ell.toNat - 1)) := Fin.pos_iff_nonempty.mp hN
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn0
  have hsumA : (∑ i, (leftResidualFin (fun j => (a j).toNat) v i : ℝ)) =
      Fintype.card (Fin (ell.toNat - 1)) * leftAverage (ell.toNat - 1) (m.toNat - (a v).toNat) := by
    simp only [Fintype.card_fin, leftAverage]
    rw [mul_div_cancel₀ _ (by exact_mod_cast hN.ne' : ((ell.toNat - 1 : ℕ) : ℝ) ≠ 0)]
    exact_mod_cast hleft
  have hsumB : (∑ j, (residualRightDegree (fun i => (b i).toNat) S j : ℝ)) =
      Fintype.card (Fin n) * rightAverage n (m.toNat - (a v).toNat) := by
    simp only [Fintype.card_fin, rightAverage]
    rw [mul_div_cancel₀ _ (by exact_mod_cast hn0.ne' : (n : ℝ) ≠ 0)]
    exact_mod_cast hres.2.2
  have hcA := deletion_centered_bounds
    (fun i => (leftResidualFin (fun j => (a j).toNat) v i : ℝ)) (p * n)
    (leftAverage (ell.toNat - 1) (m.toNat - (a v).toNat)) (Real.log n) hx hl.2.1
    (by simpa only [Real.sqrt_eq_rpow] using hsmall p hp) (hspread p hp) hsumA
    (fun i => (hdevA ((remainingEquiv v).symm i)).trans (by linarith))
  have hcB := deletion_centered_bounds
    (fun j => (residualRightDegree (fun i => (b i).toNat) S j : ℝ)) (p * ell)
    (rightAverage n (m.toNat - (a v).toNat)) (Real.log n) hy hl.2.1
    (by simpa only [Real.sqrt_eq_rpow] using hsmall' p hp ell hd.1)
    (hspread' p hp ell hd.1) hsumB hdevB'
  refine ⟨hR, ⟨?_, ?_, hleft, hres.2.2, hcA.2.2.2, hcB.2.2.2⟩,
    ⟨hcA.1, hcA.2.1, hcA.2.2.1⟩, hcB.1, hcB.2.1, hcB.2.2.1⟩
  · intro i
    have hi := (hr.2.1 ((remainingEquiv v).symm i)).2
    change (a ((remainingEquiv v).symm i)).toNat ≤ n
    omega
  · intro j
    have hj := (hr.2.2 j).2
    change (b j).toNat - _ ≤ ell.toNat - 1
    omega

theorem eventually_bipartite_residual_source_sparse (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, SparseDensityWindow θ T n p →
      ∀ (ell m : ℤ) (a : Fin ell.toNat → ℤ) (b : Fin n → ℤ),
        BipartiteInput T n p ell m a b →
          ∀ (v : Fin ell.toNat) (S : Finset (Fin n)), S.card = (a v).toNat →
            bipartiteAdmissible (fun i => (a i).toNat) (fun j => (b j).toNat) v S ∧
              BipartiteSourceData (7 / 12) (ell.toNat - 1) n (m.toNat - (a v).toNat)
                (leftResidualFin (fun i => (a i).toNat) v) (residualRightDegree (fun j => (b j).toNat) S) := by
  filter_upwards [eventually_bipartite_residual_regular_sparse θ T hθlo hθhi hT] with n hn
  intro p hp ell m a b hd v S hS
  exact ⟨(hn p hp ell m a b hd v S hS).1, (hn p hp ell m a b hd v S hS).2.1⟩

end MajorityDynamics.Probability.NeighborhoodBulk

