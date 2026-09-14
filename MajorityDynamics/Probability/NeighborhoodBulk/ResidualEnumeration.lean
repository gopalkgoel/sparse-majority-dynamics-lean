import MajorityDynamics.Probability.NeighborhoodBulk.ResidualScales

noncomputable section
open Filter
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodBulk
open FixedDegreeSampling
open MajorityDynamics.Combinatorics.DegreeRatios
open MajorityDynamics.Literature.DegreeEnumeration

theorem eventually_graph_residual_enumeration (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, DensityWindow θ T n p →
      ∀ (m : ℤ) (d : Fin n → ℤ), GraphInput T n p m d →
        ∀ (v : Fin n) (S : Finset (Fin n)), v ∉ S → S.card = (d v).toNat →
          let d' := graphResidualFin (fun i => (d i).toNat) v S
          let m' := m.toNat - (d v).toNat
          RelativeApproximation (1 / 2) ((graphDegreeLaw (Fin (n - 1)) m').real {d'})
            ((graphBinomialLaw (Fin (n - 1)) m').real {d'} * graphCorrection m' d') ∧
          (graphFamily (residualDegree (fun i => (d i).toNat) v S)).Nonempty := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (graph_enumeration_sparse θ (16 * T) (by linarith) hθhi (by linarith))
  filter_upwards [eventually_ge_atTop (N + 1),
    eventually_graph_residual_source θ T hθlo hθhi hT,
    eventually_graph_residual_scale θ T hθlo hθhi hT] with n hn hsource hscale
  intro p hp m d hd v S hv hS
  have hdata := (hsource p hp m d hd v S hv hS).2
  have ha := hN (n - 1) (by omega) _ (hscale p hp m d hd v) _ hdata
  refine ⟨ha, ?_⟩
  have hf := graphFamily_nonempty_of_enumeration _ hdata (by norm_num) ha
  have hc : 0 < graphCount (graphResidualFin (fun i => (d i).toNat) v S) :=
    (Set.ncard_pos (Set.toFinite _)).mpr hf
  rw [graphResidualFin_count] at hc
  exact (Set.ncard_pos (Set.toFinite _)).mp hc

theorem eventually_bipartite_residual_enumeration (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, DensityWindow θ T n p →
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
  filter_upwards [bipartite_enumeration_sparse θ (8 * T ^ 2) (by linarith) hθhi (by nlinarith),
    eventually_bipartite_residual_source θ T hθlo hθhi hT,
    eventually_bipartite_residual_scale θ T hθlo hθhi hT] with n he hsource hscale
  intro p hp ell m a b hd v S hS
  have hdata := (hsource p hp ell m a b hd v S hS).2
  have ha := he _ _ (hscale p hp ell m a b hd v) _ _ hdata
  refine ⟨ha, ?_⟩
  have hf := bipartiteFamily_nonempty_of_enumeration _ _ hdata (by norm_num) ha
  have hc : 0 < bipartiteCount (leftResidualFin (fun i => (a i).toNat) v)
      (residualRightDegree (fun j => (b j).toNat) S) := (Set.ncard_pos (Set.toFinite _)).mpr hf
  rw [bipartiteResidualFin_count] at hc
  exact (Set.ncard_pos (Set.toFinite _)).mp hc

end MajorityDynamics.Probability.NeighborhoodBulk
