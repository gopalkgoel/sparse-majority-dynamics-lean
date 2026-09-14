import MajorityDynamics.Probability.NeighborhoodTail.Factors
import MajorityDynamics.Probability.NeighborhoodBulk.Main
import MajorityDynamics.Probability.HypergeometricTiltTail.Main

/-! Theorem C.2: actual graph and bipartite fixed-degree neighborhood point tails.
The constants and threshold precede every varying input. -/
noncomputable section
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodTail
open FixedDegreeSampling NeighborhoodBulk HypergeometricTiltTail
open MajorityDynamics.Combinatorics.DegreeRatios

theorem graph_neighborhood_tail : GraphNeighborhoodTailTheorem := by
  intro θ T hθlo hθhi hT
  obtain ⟨B, Nb, hB, hNb, hb⟩ := graph_neighborhood_bulk θ T hθlo hθhi hT
  obtain ⟨c, hc, Nf, hf⟩ := uniform_factor hθlo hθhi hT hB.le
  refine ⟨c, max Nb Nf, hc, hNb.trans (le_max_left _ _), ?_⟩
  intro n hn p hw
  have hb' := hb n ((le_max_left _ _).trans hn) p hw
  have hn3 : 3 ≤ n := hNb.trans ((le_max_left _ _).trans hn)
  have hnpos : 0 < n := by omega
  have hTpos : 0 < T := by linarith
  refine ⟨hb'.1, hb'.2.1, ?_⟩
  intro m d hd
  obtain ⟨hne, he⟩ := hb'.2.2 m d hd
  refine ⟨hne, ?_⟩
  intro v S hS hSc t ht htd hτ
  have hLlo : (n : ℝ) / T ≤ n := by
    apply (div_le_iff₀ hTpos).mpr
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  have hLhi : (n : ℝ) ≤ T * n := by
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  have hfactor := hf n ((le_max_right _ _).trans hn) p hw.1 hw.2
    (Fin n) (Finset.univ.erase v) (S.erase v) (erase_subset_population v S)
    (Or.inr (by simp)) S.card hS (by linarith) (erased_part_card_close v S)
    n hLlo hLhi (fun i => standardizedDegree p n (d i)) (fun i _ => hd.2.2.2 i)
    (d v) t (degreeWindow_of_standardized hb'.1 hnpos (hd.2.2.2 v)) ht htd hτ
  exact (he v S hS hSc t ht htd).2.trans
    (by simpa only [graphComparison_eq_factor p d v S ht htd] using hfactor)

theorem bipartite_neighborhood_tail : BipartiteNeighborhoodTailTheorem := by
  intro θ T hθlo hθhi hT
  obtain ⟨B, Nb, hB, hNb, hb⟩ := bipartite_neighborhood_bulk θ T hθlo hθhi hT
  obtain ⟨c, hc, Nf, hf⟩ := uniform_factor hθlo hθhi hT hB.le
  refine ⟨c, max Nb Nf, hc, hNb.trans (le_max_left _ _), ?_⟩
  intro n hn p hw
  have hb' := hb n ((le_max_left _ _).trans hn) p hw
  have hn3 : 3 ≤ n := hNb.trans ((le_max_left _ _).trans hn)
  have hnpos : 0 < n := by omega
  refine ⟨hb'.1, hb'.2.1, ?_⟩
  intro ell m a b hd
  obtain ⟨hne, he⟩ := hb'.2.2 ell m a b hd
  refine ⟨hne, ?_⟩
  intro v S hS hSc t ht htd hτ
  have hfactor := hf n ((le_max_right _ _).trans hn) p hw.1 hw.2
    (Fin n) Finset.univ S (Finset.subset_univ S) (Or.inl (by simp))
    S.card hS (by linarith) (by simp)
    ell hd.1 hd.2.1 (fun j => standardizedDegree p ell (b j))
    (fun j _ => hd.2.2.2.2.2.2.2.2 j)
    (a v) t (degreeWindow_of_standardized hb'.1 hnpos (hd.2.2.2.2.2.2.2.1 v)) ht htd hτ
  exact (he v S hS hSc t ht htd).2.trans
    (by simpa only [bipartiteComparison_eq_factor p ell b (a v) S ht htd] using hfactor)

theorem GraphConclusion.mono {c C T p : ℝ} {n : ℕ}
    (h : GraphConclusion C T n p) (hc : c ≤ C) : GraphConclusion c T n p := by
  intro m d hd
  obtain ⟨hne, he⟩ := h m d hd
  refine ⟨hne, ?_⟩
  intro v S hS hSc t ht htd hτ
  apply (he v S hS hSc t ht htd hτ).trans
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (((t : ℝ) - p * S.card) / Real.sqrt (p * S.card))]

theorem BipartiteConclusion.mono {c C T p : ℝ} {n : ℕ}
    (h : BipartiteConclusion C T n p) (hc : c ≤ C) : BipartiteConclusion c T n p := by
  intro ell m a b hd
  obtain ⟨hne, he⟩ := h ell m a b hd
  refine ⟨hne, ?_⟩
  intro v S hS hSc t ht htd hτ
  apply (he v S hS hSc t ht htd hτ).trans
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (((t : ℝ) - p * S.card) / Real.sqrt (p * S.card))]

theorem neighborhood_tail : NeighborhoodTailTheorem := by
  intro θ T hθlo hθhi hT
  obtain ⟨cg, Ng, hcg, hNg, hg⟩ := graph_neighborhood_tail θ T hθlo hθhi hT
  obtain ⟨cb, Nb, hcb, _, hb⟩ := bipartite_neighborhood_tail θ T hθlo hθhi hT
  refine ⟨min cg cb, max Ng Nb, lt_min hcg hcb, hNg.trans (le_max_left _ _), ?_⟩
  intro n hn p hw
  have hgraph := hg n ((le_max_left _ _).trans hn) p hw
  have hbip := hb n ((le_max_right _ _).trans hn) p hw
  exact ⟨hgraph.1, hgraph.2.1, hgraph.2.2.mono (min_le_left _ _),
    hbip.2.2.mono (min_le_right _ _)⟩

end MajorityDynamics.Probability.NeighborhoodTail
