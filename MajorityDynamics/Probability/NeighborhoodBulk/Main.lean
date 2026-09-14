import MajorityDynamics.Probability.NeighborhoodBulk.AtomBounds
import MajorityDynamics.Probability.NeighborhoodBulk.Summation

/-! Lemma C.4, with literal integer inputs and the actual uniform sampling laws.
All thresholds and constants precede the data; graphicality is a conclusion. -/
noncomputable section
open Filter
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodBulk
open FixedDegreeSampling
open MajorityDynamics.Combinatorics.DegreeRatios

theorem graph_neighborhood_bulk : GraphNeighborhoodBulkTheorem := by
  intro θ T hθlo hθhi hT
  obtain ⟨C, hC, hbound⟩ := graph_atom_bounds θ T hθlo hθhi hT
  have hev : ∀ᶠ n : ℕ in atTop, 3 ≤ n ∧ ∀ p : ℝ, DensityWindow θ T n p →
      0 < p ∧ p < 1 ∧ GraphConclusion C T n p := by
    filter_upwards [eventually_ge_atTop (3 : ℕ), hbound,
      eventually_graph_probability_range θ T hθlo hθhi hT,
      eventually_graph_input_nonempty θ T hθlo hθhi hT] with n hn hb hp hnemp
    refine ⟨hn, ?_⟩
    intro p hw
    refine ⟨(hp p hw).1, (hp p hw).2, ?_⟩
    intro m d hd
    refine ⟨hnemp p hw m d hd, ?_⟩
    intro v S _ _ t ht htd
    rw [graph_event_sum d v S t ht htd, graph_comparison_sum]
    apply multiplicative_sum
    intro R₁ h₁ R₂ h₂
    obtain ⟨hs₁, hc₁⟩ := Finset.mem_powersetCard.mp h₁
    obtain ⟨hs₂, hc₂⟩ := Finset.mem_powersetCard.mp h₂
    apply hb p hw m d hd v (R₁ ∪ R₂)
    · intro hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact (Finset.mem_erase.mp (hs₁ hv)).1 rfl
      · exact (Finset.mem_sdiff.mp (hs₂ hv)).2 (Finset.mem_insert_self _ _)
    · have hdis := (graph_partition_disjoint v S).mono hs₁ hs₂
      rw [Finset.card_union_of_disjoint hdis, hc₁, hc₂]
      omega
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  exact ⟨C, N, hC, (hN N le_rfl).1, fun n hn => (hN n hn).2⟩

theorem bipartite_neighborhood_bulk : BipartiteNeighborhoodBulkTheorem := by
  intro θ T hθlo hθhi hT
  obtain ⟨C, hC, hbound⟩ := bipartite_atom_bounds θ T hθlo hθhi hT
  have hev : ∀ᶠ n : ℕ in atTop, 3 ≤ n ∧ ∀ p : ℝ, DensityWindow θ T n p →
      0 < p ∧ p < 1 ∧ BipartiteConclusion C T n p := by
    filter_upwards [eventually_ge_atTop (3 : ℕ), hbound,
      eventually_graph_probability_range θ T hθlo hθhi hT,
      eventually_bipartite_input_nonempty θ T hθlo hθhi hT] with n hn hb hp hnemp
    refine ⟨hn, ?_⟩
    intro p hw
    refine ⟨(hp p hw).1, (hp p hw).2, ?_⟩
    intro ell m a b hd
    refine ⟨hnemp p hw ell m a b hd, ?_⟩
    intro v S _ _ t ht htd
    rw [bipartite_event_sum a b v S t ht htd, bipartite_comparison_sum]
    apply multiplicative_sum
    intro R₁ h₁ R₂ h₂
    obtain ⟨hs₁, hc₁⟩ := Finset.mem_powersetCard.mp h₁
    obtain ⟨hs₂, hc₂⟩ := Finset.mem_powersetCard.mp h₂
    apply hb p hw ell m a b hd v (R₁ ∪ R₂)
    have hdis : Disjoint R₁ R₂ := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      exact (Finset.mem_sdiff.mp (hs₂ hj)).2 (hs₁ hi)
    rw [Finset.card_union_of_disjoint hdis, hc₁, hc₂]
    omega
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  exact ⟨C, N, hC, (hN N le_rfl).1, fun n hn => (hN n hn).2⟩

theorem graphComparison_nonneg {n : ℕ} (p : ℝ) (d : Fin n → ℤ) (v : Fin n)
    (S : Finset (Fin n)) (t : ℤ) : 0 ≤ graphComparison p d v S t := by
  rw [graph_comparison_sum]
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))

theorem bipartiteComparison_nonneg {n : ℕ} (p : ℝ) (ell : ℤ) (b : Fin n → ℤ)
    (dv : ℤ) (S : Finset (Fin n)) (t : ℤ) : 0 ≤ bipartiteComparison p ell b dv S t := by
  rw [bipartite_comparison_sum]
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))

theorem MultiplicativeBound.mono {C D P Q : ℝ} {n : ℕ}
    (h : MultiplicativeBound C n P Q) (hQ : 0 ≤ Q) (hCD : C ≤ D) :
    MultiplicativeBound D n P Q := by
  have he := bound_enlarge hQ (mul_le_mul_of_nonneg_right hCD (by positivity : 0 ≤ Real.log n ^ 4))
    (by simpa only [MultiplicativeBound, neg_mul] using h)
  simpa only [MultiplicativeBound, neg_mul] using he

theorem neighborhood_bulk : NeighborhoodBulkTheorem := by
  intro θ T hθlo hθhi hT
  obtain ⟨Cg, Ng, hCg, hNg, hg⟩ := graph_neighborhood_bulk θ T hθlo hθhi hT
  obtain ⟨Cb, Nb, _, _, hb⟩ := bipartite_neighborhood_bulk θ T hθlo hθhi hT
  refine ⟨max Cg Cb, max Ng Nb, hCg.trans_le (le_max_left _ _), hNg.trans (le_max_left _ _), ?_⟩
  intro n hn p hp
  have hgraph := hg n ((le_max_left _ _).trans hn) p hp
  have hbip := hb n ((le_max_right _ _).trans hn) p hp
  refine ⟨hgraph.1, hgraph.2.1, ?_, ?_⟩
  · intro m d hd
    obtain ⟨hne, he⟩ := hgraph.2.2 m d hd
    refine ⟨hne, ?_⟩
    intro v S hS hSc t ht htd
    exact (he v S hS hSc t ht htd).mono (graphComparison_nonneg p d v S t) (le_max_left _ _)
  · intro ell m a b hd
    obtain ⟨hne, he⟩ := hbip.2.2 ell m a b hd
    refine ⟨hne, ?_⟩
    intro v S hS hSc t ht htd
    exact (he v S hS hSc t ht htd).mono
      (bipartiteComparison_nonneg p ell b (a v) S t) (le_max_right _ _)

end MajorityDynamics.Probability.NeighborhoodBulk
