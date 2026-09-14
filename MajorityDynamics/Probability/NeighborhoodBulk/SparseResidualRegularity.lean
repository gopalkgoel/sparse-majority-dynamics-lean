import MajorityDynamics.Probability.NeighborhoodBulk.ResidualRegularity
import MajorityDynamics.Combinatorics.DegreeRatios.SparseUniform
import MajorityDynamics.Probability.NeighborhoodBulk.SparseRegularity

/-! Uniform sparse-range preparation, preserving the original finite bounds. -/
noncomputable section
open Filter
open scoped Classical BigOperators
namespace MajorityDynamics.Probability.NeighborhoodBulk
open FixedDegreeSampling
open MajorityDynamics.Combinatorics.DegreeRatios
open MajorityDynamics.Literature.DegreeEnumeration

theorem eventually_graph_degree_room_sparse (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, SparseDensityWindow θ T n p →
      ∀ (m : ℤ) (d : Fin n → ℤ), GraphInput T n p m d →
        ∀ i, 2 ≤ (d i).toNat ∧ (d i).toNat ≤ n - 2 := by
  filter_upwards [eventually_sparse_large_parameters θ T hθlo hθhi hT,
    eventually_ge_atTop (4 : ℕ),
    eventually_density_log_le_rpow_sparse θ T 2 (1 / 2) hθhi (by linarith)
      (by norm_num) (by norm_num)] with n hlarge hn hsmall
  intro p hp m d hd i
  have hl := hlarge p hp
  have hx : 0 < p * n := mul_pos hl.2.2.1 (by exact_mod_cast (by omega : 0 < n))
  have hs : 2 * Real.log n ≤ Real.sqrt (p * n) := by simpa only [Real.sqrt_eq_rpow] using hsmall p hp
  apply natural_degree_room n (d i).toNat p (Real.log n) hn hl.2.2.1 hl.2.2.2.1 hl.2.1 hs
  have he : ((d i).toNat : ℝ) = (d i : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (hd.1 i).1
  rw [he]
  exact (standardizedDegree_bound_iff p n (d i) (Real.log n) hx).mp (hd.2.2.2 i)

theorem eventually_graph_residual_regular_sparse (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, SparseDensityWindow θ T n p →
      ∀ (m : ℤ) (d : Fin n → ℤ), GraphInput T n p m d →
        ∀ (v : Fin n) (S : Finset (Fin n)), v ∉ S → S.card = (d v).toNat →
          graphAdmissible (fun i => (d i).toNat) v S ∧
            GraphSourceData (7 / 12) (n - 1) (m.toNat - (d v).toNat)
              (graphResidualFin (fun i => (d i).toNat) v S) ∧
            CenteredControl (graphResidualFin (fun i => (d i).toNat) v S)
              (graphAverage (n - 1) (m.toNat - (d v).toNat)) (p * n) (2 * Real.log n) := by
  filter_upwards [eventually_sparse_large_parameters θ T hθlo hθhi hT,
    eventually_ge_atTop (3 : ℕ), eventually_graph_degree_room_sparse θ T hθlo hθhi hT,
    eventually_density_log_le_rpow_sparse θ T 4 (1 / 2) hθhi (by linarith) (by norm_num) (by norm_num),
    eventually_density_log_le_rpow_sparse θ T 8 (7 / 12 - 1 / 2) hθhi (by linarith) (by norm_num)
      (by norm_num)] with n hlarge hn hroom hsmall hspread
  intro p hp m d hd v S hv hS
  have hl := hlarge p hp
  have hx : 0 < p * n := mul_pos hl.2.2.1 (by exact_mod_cast (by omega : 0 < n))
  have hR : graphAdmissible (fun i => (d i).toNat) v S :=
    ⟨hv, hS, fun i _ => (show 1 ≤ 2 by omega).trans (hroom p hp m d hd i).1⟩
  have hs := graphResidualFin_sum (fun i => (d i).toNat) v S hR m.toNat (graph_input_nat_sum hd).2
  have hdev : ∀ i, |((d i).toNat : ℝ) - p * n| ≤ Real.sqrt (p * n) * Real.log n := by
    intro i
    have he : ((d i).toNat : ℝ) = (d i : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (hd.1 i).1
    rw [he]
    exact (standardizedDegree_bound_iff p n (d i) (Real.log n) hx).mp (hd.2.2.2 i)
  have hdev' := graphResidualFin_deviation (fun i => (d i).toNat) v S hR
    (p * n) (Real.sqrt (p * n) * Real.log n) hdev
  have : Nonempty (Fin (n - 1)) := Fin.pos_iff_nonempty.mp (by omega)
  have hc := deletion_centered_bounds
    (fun i => (graphResidualFin (fun j => (d j).toNat) v S i : ℝ)) (p * n)
    (graphAverage (n - 1) (m.toNat - (d v).toNat)) (Real.log n) hx hl.2.1
    (by simpa only [Real.sqrt_eq_rpow] using hsmall p hp) (hspread p hp) ?_ hdev'
  · refine ⟨hR, ⟨?_, hs, hc.2.2.2⟩, hc.1, hc.2.1, hc.2.2.1⟩
    intro i
    have hi := (hroom p hp m d hd ((remainingEquiv v).symm i)).2
    change (d ((remainingEquiv v).symm i)).toNat - _ ≤ n - 1 - 1
    omega
  · simp only [Fintype.card_fin, graphAverage]
    have hN : 0 < n - 1 := by omega
    rw [mul_div_cancel₀ _ (by exact_mod_cast hN.ne' : ((n - 1 : ℕ) : ℝ) ≠ 0)]
    exact_mod_cast hs

theorem eventually_graph_residual_source_sparse (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, SparseDensityWindow θ T n p →
      ∀ (m : ℤ) (d : Fin n → ℤ), GraphInput T n p m d →
        ∀ (v : Fin n) (S : Finset (Fin n)), v ∉ S → S.card = (d v).toNat →
          graphAdmissible (fun i => (d i).toNat) v S ∧
            GraphSourceData (7 / 12) (n - 1) (m.toNat - (d v).toNat)
              (graphResidualFin (fun i => (d i).toNat) v S) := by
  filter_upwards [eventually_graph_residual_regular_sparse θ T hθlo hθhi hT] with n hn
  intro p hp m d hd v S hv hS
  exact ⟨(hn p hp m d hd v S hv hS).1, (hn p hp m d hd v S hv hS).2.1⟩

end MajorityDynamics.Probability.NeighborhoodBulk

