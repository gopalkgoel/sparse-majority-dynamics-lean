import MajorityDynamics.Probability.NeighborhoodBulk.ResidualCorrections
import MajorityDynamics.Probability.NeighborhoodBulk.LogComparison
import MajorityDynamics.Probability.NeighborhoodBulk.ModelRatios

noncomputable section
open Filter
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodBulk
open FixedDegreeSampling
open MajorityDynamics.Literature.DegreeEnumeration
open MajorityDynamics.Combinatorics.DegreeRatios

theorem graph_source_count_control {n m : ℕ} {α K : ℝ} (d : Fin n → ℕ)
    (hd : GraphSourceData α n m d)
    (he : RelativeApproximation (1 / 2) ((graphDegreeLaw (Fin n) m).real {d})
      ((graphBinomialLaw (Fin n) m).real {d} * graphCorrection m d))
    (hc : Real.exp (-K) ≤ graphCorrection m d ∧ graphCorrection m d ≤ Real.exp K) :
    0 < graphCountModel m d ∧ 0 < (graphCount d : ℝ) ∧
      |Real.log (graphCount d : ℝ) - Real.log (graphCountModel m d)| ≤ K + 1 := by
  have hcap : m ≤ n.choose 2 := by
    rw [Nat.choose_two_right]
    have := graph_degree_total_capacity d hd.1 hd.2.1
    omega
  have hM := graphCountModel_pos d hcap hd.1 hd.2.1
  exact ⟨hM, count_log_control hM (Real.exp_pos _)
    (graph_count_relative d hcap hd.1 hd.2.1 he) hc.1 hc.2⟩

theorem bipartite_source_count_control {ell n m : ℕ} {α K : ℝ}
    (a : Fin ell → ℕ) (b : Fin n → ℕ) (hd : BipartiteSourceData α ell n m a b)
    (he : RelativeApproximation (1 / 2) ((bipartiteDegreeLaw (Fin ell) (Fin n) m).real {(a,b)})
      ((bipartiteBinomialLaw (Fin ell) (Fin n) m).real {(a,b)} * bipartiteCorrection m a b))
    (hc : Real.exp (-K) ≤ bipartiteCorrection m a b ∧ bipartiteCorrection m a b ≤ Real.exp K) :
    0 < bipartiteCountModel m a b ∧ 0 < (bipartiteCount a b : ℝ) ∧
      |Real.log (bipartiteCount a b : ℝ) - Real.log (bipartiteCountModel m a b)| ≤ K + 1 := by
  have hcap : m ≤ ell * n := by
    calc
      m = ∑ i, a i := hd.2.2.1.symm
      _ ≤ ∑ _ : Fin ell, n := Finset.sum_le_sum (fun i _ => hd.1 i)
      _ = ell * n := by simp
  have hM := bipartiteCountModel_pos a b hcap hd.1 hd.2.1
  exact ⟨hM, count_log_control hM (Real.exp_pos _)
    (bipartite_count_relative a b hcap hd.2.2.1 hd.2.2.2.1 he) hc.1 hc.2⟩

theorem eventually_graph_count_control (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, DensityWindow θ T n p →
      ∀ (m : ℤ) (d : Fin n → ℤ), GraphInput T n p m d →
        let dn := fun i => (d i).toNat
        0 < graphCountModel m.toNat dn ∧ 0 < (graphCount dn : ℝ) ∧
          |Real.log (graphCount dn : ℝ) - Real.log (graphCountModel m.toNat dn)| ≤
            1025 * Real.log n ^ 4 + 1 := by
  filter_upwards [eventually_graph_source_data θ T hθlo hθhi hT,
    eventually_graph_input_scale θ T hθlo hθhi hT,
    graph_enumeration_sparse θ (4 * T) (by linarith) hθhi (by linarith),
    eventually_graph_correction_bounds θ T hθlo hθhi hT] with n hdata hscale he hc
  intro p hp m d hd
  have hs := hdata p hp m d hd
  apply graph_source_count_control _ hs (he _ (hscale p hp m d hd) _ hs)
  simpa only [neg_mul] using hc p hp m d hd

theorem eventually_graph_residual_count_control (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, DensityWindow θ T n p →
      ∀ (m : ℤ) (d : Fin n → ℤ), GraphInput T n p m d →
        ∀ (v : Fin n) (R : Finset (Fin n)), v ∉ R → R.card = (d v).toNat →
          let dn := graphResidualFin (fun i => (d i).toNat) v R
          let mr := m.toNat - (d v).toNat
          0 < graphCountModel mr dn ∧ 0 < (graphCount dn : ℝ) ∧
            |Real.log (graphCount dn : ℝ) - Real.log (graphCountModel mr dn)| ≤
              16400 * Real.log n ^ 4 + 1 := by
  filter_upwards [eventually_graph_residual_source θ T hθlo hθhi hT,
    eventually_graph_residual_enumeration θ T hθlo hθhi hT,
    eventually_graph_residual_correction θ T hθlo hθhi hT] with n hs he hc
  intro p hp m d hd v R hv hR
  apply graph_source_count_control _ (hs p hp m d hd v R hv hR).2
    (he p hp m d hd v R hv hR).1
  simpa only [neg_mul] using hc p hp m d hd v R hv hR

theorem eventually_bipartite_count_control (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, DensityWindow θ T n p →
      ∀ (ell m : ℤ) (a : Fin ell.toNat → ℤ) (b : Fin n → ℤ),
        BipartiteInput T n p ell m a b →
          let an := fun i => (a i).toNat
          let bn := fun j => (b j).toNat
          0 < bipartiteCountModel m.toNat an bn ∧ 0 < (bipartiteCount an bn : ℝ) ∧
            |Real.log (bipartiteCount an bn : ℝ) - Real.log (bipartiteCountModel m.toNat an bn)| ≤
              289 * Real.log n ^ 4 + 1 := by
  filter_upwards [eventually_bipartite_source_data θ T hθlo hθhi hT,
    eventually_bipartite_input_scale θ T hθlo hθhi hT,
    bipartite_enumeration_sparse θ (4 * T ^ 2) (by linarith) hθhi (by nlinarith),
    eventually_bipartite_correction_bounds θ T hθlo hθhi hT] with n hdata hscale he hc
  intro p hp ell m a b hd
  have hs := hdata p hp ell m a b hd
  apply bipartite_source_count_control _ _ hs (he _ _ (hscale p hp ell m a b hd) _ _ hs)
  simpa only [neg_mul] using hc p hp ell m a b hd

theorem eventually_bipartite_residual_count_control (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, DensityWindow θ T n p →
      ∀ (ell m : ℤ) (a : Fin ell.toNat → ℤ) (b : Fin n → ℤ),
        BipartiteInput T n p ell m a b →
          ∀ (v : Fin ell.toNat) (R : Finset (Fin n)), R.card = (a v).toNat →
            let an := leftResidualFin (fun i => (a i).toNat) v
            let bn := residualRightDegree (fun j => (b j).toNat) R
            let mr := m.toNat - (a v).toNat
            0 < bipartiteCountModel mr an bn ∧ 0 < (bipartiteCount an bn : ℝ) ∧
              |Real.log (bipartiteCount an bn : ℝ) - Real.log (bipartiteCountModel mr an bn)| ≤
                4624 * Real.log n ^ 4 + 1 := by
  filter_upwards [eventually_bipartite_residual_source θ T hθlo hθhi hT,
    eventually_bipartite_residual_enumeration θ T hθlo hθhi hT,
    eventually_bipartite_residual_correction θ T hθlo hθhi hT] with n hs he hc
  intro p hp ell m a b hd v R hR
  apply bipartite_source_count_control _ _ (hs p hp ell m a b hd v R hR).2
    (he p hp ell m a b hd v R hR).1
  simpa only [neg_mul] using hc p hp ell m a b hd v R hR

end MajorityDynamics.Probability.NeighborhoodBulk
