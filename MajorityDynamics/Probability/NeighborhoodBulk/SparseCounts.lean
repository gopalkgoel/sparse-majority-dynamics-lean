import MajorityDynamics.Probability.NeighborhoodBulk.CountControl
import MajorityDynamics.Probability.NeighborhoodBulk.SparseResidualScales
import MajorityDynamics.Probability.NeighborhoodBulk.SparseCorrections

/-! Actual and residual degree-family counts across the uniform sparse band. -/
noncomputable section
open Filter
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodBulk
open FixedDegreeSampling
open MajorityDynamics.Combinatorics.DegreeRatios
open MajorityDynamics.Literature.DegreeEnumeration

theorem eventually_graph_residual_enumeration_sparse (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, SparseDensityWindow θ T n p →
      ∀ (m : ℤ) (d : Fin n → ℤ), GraphInput T n p m d →
        ∀ (v : Fin n) (S : Finset (Fin n)), v ∉ S → S.card = (d v).toNat →
          let d' := graphResidualFin (fun i => (d i).toNat) v S
          let m' := m.toNat - (d v).toNat
          RelativeApproximation (1 / 2) ((graphDegreeLaw (Fin (n - 1)) m').real {d'})
            ((graphBinomialLaw (Fin (n - 1)) m').real {d'} * graphCorrection m' d') ∧
          (graphFamily (residualDegree (fun i => (d i).toNat) v S)).Nonempty := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (graph_enumeration_band θ (1/2) (16 * T) (by norm_num) hθlo.le hθhi (by linarith))
  filter_upwards [eventually_ge_atTop (N + 1),
    eventually_graph_residual_source_sparse θ T hθlo hθhi hT,
    eventually_graph_residual_scale_sparse θ T hθlo hθhi hT] with n hn hsource hscale
  intro p hp m d hd v S hv hS
  have hdata := (hsource p hp m d hd v S hv hS).2
  have ha := hN (n - 1) (by omega) _ (hscale p hp m d hd v) _ hdata
  refine ⟨ha, ?_⟩
  have hf := graphFamily_nonempty_of_enumeration _ hdata (by norm_num) ha
  have hc : 0 < graphCount (graphResidualFin (fun i => (d i).toNat) v S) :=
    (Set.ncard_pos (Set.toFinite _)).mpr hf
  rw [graphResidualFin_count] at hc
  exact (Set.ncard_pos (Set.toFinite _)).mp hc

theorem eventually_bipartite_residual_enumeration_sparse (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, SparseDensityWindow θ T n p →
      ∀ (ell m : ℤ) (a : Fin ell.toNat → ℤ) (b : Fin n → ℤ),
        BipartiteInput T n p ell m a b →
          ∀ (v : Fin ell.toNat) (S : Finset (Fin n)), S.card = (a v).toNat →
            let a' := leftResidualFin (fun i => (a i).toNat) v
            let b' := residualRightDegree (fun j => (b j).toNat) S
            let m' := m.toNat - (a v).toNat
            RelativeApproximation (1 / 2)
              ((bipartiteDegreeLaw (Fin (ell.toNat - 1)) (Fin n) m').real {(a', b')})
              ((bipartiteBinomialLaw (Fin (ell.toNat - 1)) (Fin n) m').real {(a', b')} *
                bipartiteCorrection m' a' b') ∧
            (bipartiteFamily (fun u : Remaining v => (a u).toNat) b').Nonempty := by
  filter_upwards [bipartite_enumeration_band θ (1/2) (8 * T ^ 2) (by norm_num) hθlo.le hθhi (by nlinarith),
    eventually_bipartite_residual_source_sparse θ T hθlo hθhi hT,
    eventually_bipartite_residual_scale_sparse θ T hθlo hθhi hT] with n he hsource hscale
  intro p hp ell m a b hd v S hS
  have hdata := (hsource p hp ell m a b hd v S hS).2
  have ha := he _ _ (hscale p hp ell m a b hd v) _ _ hdata
  refine ⟨ha, ?_⟩
  have hf := bipartiteFamily_nonempty_of_enumeration _ _ hdata (by norm_num) ha
  have hc : 0 < bipartiteCount (leftResidualFin (fun i => (a i).toNat) v)
      (residualRightDegree (fun j => (b j).toNat) S) := (Set.ncard_pos (Set.toFinite _)).mpr hf
  rw [bipartiteResidualFin_count] at hc
  exact (Set.ncard_pos (Set.toFinite _)).mp hc

theorem eventually_graph_residual_correction_sparse (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, SparseDensityWindow θ T n p →
      ∀ (m : ℤ) (d : Fin n → ℤ), GraphInput T n p m d →
        ∀ (v : Fin n) (S : Finset (Fin n)), v ∉ S → S.card = (d v).toNat →
          let d' := graphResidualFin (fun i => (d i).toNat) v S
          let m' := m.toNat - (d v).toNat
          Real.exp (-16400 * Real.log n ^ 4) ≤ graphCorrection m' d' ∧
            graphCorrection m' d' ≤ Real.exp (16400 * Real.log n ^ 4) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_graph_band_domain θ (1/2) (16 * T) (1/2) (by norm_num) (by linarith) (by norm_num))
  filter_upwards [eventually_ge_atTop (N + 1), eventually_ge_atTop (3 : ℕ),
    eventually_sparse_large_parameters θ T hθlo hθhi hT,
    eventually_graph_residual_regular_sparse θ T hθlo hθhi hT,
    eventually_graph_residual_scale_sparse θ T hθlo hθhi hT] with n hnN hn hlarge hregular hscale
  intro p hp m d hd v S hv hS
  have hl := hlarge p hp
  have hcontrol := (hregular p hp m d hd v S hv hS).2.2
  have hρ := (hN (n - 1) (by omega) _ (hscale p hp m d hd v)).2.1
  have hx : 0 < p * n := mul_pos hl.2.2.1 (by exact_mod_cast (by omega : 0 < n))
  have hh := graph_correction_of_control _ (p * n) (2 * Real.log n) (by omega) hx
    (by linarith [hl.2.1]) hρ hcontrol
  norm_num [mul_pow, ← mul_assoc] at hh
  simpa only [neg_mul] using hh

theorem eventually_bipartite_residual_correction_sparse (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, SparseDensityWindow θ T n p →
      ∀ (ell m : ℤ) (a : Fin ell.toNat → ℤ) (b : Fin n → ℤ),
        BipartiteInput T n p ell m a b →
          ∀ (v : Fin ell.toNat) (S : Finset (Fin n)), S.card = (a v).toNat →
            let a' := leftResidualFin (fun i => (a i).toNat) v
            let b' := residualRightDegree (fun j => (b j).toNat) S
            let m' := m.toNat - (a v).toNat
            Real.exp (-4624 * Real.log n ^ 4) ≤ bipartiteCorrection m' a' b' ∧
              bipartiteCorrection m' a' b' ≤ Real.exp (4624 * Real.log n ^ 4) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_sparse_large_parameters θ T hθlo hθhi hT,
    eventually_bipartite_residual_regular_sparse θ T hθlo hθhi hT,
    eventually_bipartite_residual_scale_sparse θ T hθlo hθhi hT,
    eventually_bipartite_degree_room_sparse θ T hθlo hθhi hT,
    eventually_bipartite_band_domain θ (1/2) (8 * T ^ 2) (1/2) (by norm_num) (by nlinarith)
      (by norm_num)] with n hn hlarge hregular hscale hroom hdom
  intro p hp ell m a b hd v S hS
  have hl := hlarge p hp
  have hr := hroom p hp ell m a b hd
  have hc := (hregular p hp ell m a b hd v S hS).2.2
  have hρ := (hdom _ _ (hscale p hp ell m a b hd v)).2.2.1.le
  have helln : 0 < ell.toNat - 1 := by omega
  have hell : 0 < ell := by omega
  have hx : 0 < p * n := mul_pos hl.2.2.1 (by exact_mod_cast hn)
  have hy : 0 < p * ell := mul_pos hl.2.2.1 (by exact_mod_cast hell)
  have hh := bipartite_correction_of_control _ _ (p * n) (p * ell) (2 * Real.log n)
    helln (by omega) hx hy (by linarith [hl.2.1]) hρ hc.1 hc.2
  norm_num [mul_pow, ← mul_assoc] at hh
  simpa only [neg_mul] using hh

theorem eventually_graph_count_control_sparse (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, SparseDensityWindow θ T n p →
      ∀ (m : ℤ) (d : Fin n → ℤ), GraphInput T n p m d →
        let dn := fun i => (d i).toNat
        0 < graphCountModel m.toNat dn ∧ 0 < (graphCount dn : ℝ) ∧
          |Real.log (graphCount dn : ℝ) - Real.log (graphCountModel m.toNat dn)| ≤
            1025 * Real.log n ^ 4 + 1 := by
  filter_upwards [eventually_graph_source_data_sparse θ T hθlo hθhi hT,
    eventually_graph_input_scale_sparse θ T hθlo hθhi hT,
    graph_enumeration_band θ (1/2) (4 * T) (by norm_num) hθlo.le hθhi (by linarith),
    eventually_graph_correction_bounds_sparse θ T hθlo hθhi hT] with n hdata hscale he hc
  intro p hp m d hd
  have hs := hdata p hp m d hd
  apply graph_source_count_control _ hs (he _ (hscale p hp m d hd) _ hs)
  simpa only [neg_mul] using hc p hp m d hd

theorem eventually_graph_residual_count_control_sparse (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, SparseDensityWindow θ T n p →
      ∀ (m : ℤ) (d : Fin n → ℤ), GraphInput T n p m d →
        ∀ (v : Fin n) (R : Finset (Fin n)), v ∉ R → R.card = (d v).toNat →
          let dn := graphResidualFin (fun i => (d i).toNat) v R
          let mr := m.toNat - (d v).toNat
          0 < graphCountModel mr dn ∧ 0 < (graphCount dn : ℝ) ∧
            |Real.log (graphCount dn : ℝ) - Real.log (graphCountModel mr dn)| ≤
              16400 * Real.log n ^ 4 + 1 := by
  filter_upwards [eventually_graph_residual_source_sparse θ T hθlo hθhi hT,
    eventually_graph_residual_enumeration_sparse θ T hθlo hθhi hT,
    eventually_graph_residual_correction_sparse θ T hθlo hθhi hT] with n hs he hc
  intro p hp m d hd v R hv hR
  apply graph_source_count_control _ (hs p hp m d hd v R hv hR).2
    (he p hp m d hd v R hv hR).1
  simpa only [neg_mul] using hc p hp m d hd v R hv hR

theorem eventually_bipartite_count_control_sparse (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, SparseDensityWindow θ T n p →
      ∀ (ell m : ℤ) (a : Fin ell.toNat → ℤ) (b : Fin n → ℤ),
        BipartiteInput T n p ell m a b →
          let an := fun i => (a i).toNat
          let bn := fun j => (b j).toNat
          0 < bipartiteCountModel m.toNat an bn ∧ 0 < (bipartiteCount an bn : ℝ) ∧
            |Real.log (bipartiteCount an bn : ℝ) - Real.log (bipartiteCountModel m.toNat an bn)| ≤
              289 * Real.log n ^ 4 + 1 := by
  filter_upwards [eventually_bipartite_source_data_sparse θ T hθlo hθhi hT,
    eventually_bipartite_input_scale_sparse θ T hθlo hθhi hT,
    bipartite_enumeration_band θ (1/2) (4 * T ^ 2) (by norm_num) hθlo.le hθhi (by nlinarith),
    eventually_bipartite_correction_bounds_sparse θ T hθlo hθhi hT] with n hdata hscale he hc
  intro p hp ell m a b hd
  have hs := hdata p hp ell m a b hd
  apply bipartite_source_count_control _ _ hs (he _ _ (hscale p hp ell m a b hd) _ _ hs)
  simpa only [neg_mul] using hc p hp ell m a b hd

theorem eventually_bipartite_residual_count_control_sparse (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, SparseDensityWindow θ T n p →
      ∀ (ell m : ℤ) (a : Fin ell.toNat → ℤ) (b : Fin n → ℤ),
        BipartiteInput T n p ell m a b →
          ∀ (v : Fin ell.toNat) (R : Finset (Fin n)), R.card = (a v).toNat →
            let an := leftResidualFin (fun i => (a i).toNat) v
            let bn := residualRightDegree (fun j => (b j).toNat) R
            let mr := m.toNat - (a v).toNat
            0 < bipartiteCountModel mr an bn ∧ 0 < (bipartiteCount an bn : ℝ) ∧
              |Real.log (bipartiteCount an bn : ℝ) - Real.log (bipartiteCountModel mr an bn)| ≤
                4624 * Real.log n ^ 4 + 1 := by
  filter_upwards [eventually_bipartite_residual_source_sparse θ T hθlo hθhi hT,
    eventually_bipartite_residual_enumeration_sparse θ T hθlo hθhi hT,
    eventually_bipartite_residual_correction_sparse θ T hθlo hθhi hT] with n hs he hc
  intro p hp ell m a b hd v R hR
  apply bipartite_source_count_control _ _ (hs p hp ell m a b hd v R hR).2
    (he p hp ell m a b hd v R hR).1
  simpa only [neg_mul] using hc p hp ell m a b hd v R hR

end MajorityDynamics.Probability.NeighborhoodBulk

