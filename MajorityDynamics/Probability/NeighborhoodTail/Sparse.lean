import MajorityDynamics.Probability.NeighborhoodTail.CarrierMain
import MajorityDynamics.Probability.NeighborhoodBulk.SparseMain
import MajorityDynamics.Probability.HypergeometricTiltTail.Sparse

/-! Actual graph and bipartite neighborhood tails throughout the sparse range,
with a single constant and threshold for every finite carrier. -/
noncomputable section
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodTail
open FixedDegreeSampling NeighborhoodBulk HypergeometricTiltTail
open MajorityDynamics.Combinatorics.DegreeRatios

def SparseGraphNeighborhoodTailTheorem : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∃ c : ℝ, ∃ n₀ : ℕ, 0 < c ∧ 3 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ p : ℝ, SparseDensityWindow θ T n p →
        0 < p ∧ p < 1 ∧ GraphConclusion c T n p

def SparseBipartiteNeighborhoodTailTheorem : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∃ c : ℝ, ∃ n₀ : ℕ, 0 < c ∧ 3 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ p : ℝ, SparseDensityWindow θ T n p →
        0 < p ∧ p < 1 ∧ BipartiteConclusion c T n p

def SparseNeighborhoodTailTheorem : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∃ c : ℝ, ∃ n₀ : ℕ, 0 < c ∧ 3 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ p : ℝ, SparseDensityWindow θ T n p →
        0 < p ∧ p < 1 ∧ GraphConclusion c T n p ∧ BipartiteConclusion c T n p


theorem graph_neighborhood_tail_sparse : SparseGraphNeighborhoodTailTheorem := by
  intro θ T hθlo hθhi hT
  obtain ⟨B, Nb, hB, hNb, hb⟩ := graph_neighborhood_bulk_sparse θ T hθlo hθhi hT
  obtain ⟨c, hc, Nf, hf⟩ := uniform_factor_sparse hθlo hθhi hT hB.le
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

theorem bipartite_neighborhood_tail_sparse : SparseBipartiteNeighborhoodTailTheorem := by
  intro θ T hθlo hθhi hT
  obtain ⟨B, Nb, hB, hNb, hb⟩ := bipartite_neighborhood_bulk_sparse θ T hθlo hθhi hT
  obtain ⟨c, hc, Nf, hf⟩ := uniform_factor_sparse hθlo hθhi hT hB.le
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


theorem neighborhood_tail_sparse : SparseNeighborhoodTailTheorem := by
  intro θ T hθlo hθhi hT
  obtain ⟨cg, Ng, hcg, hNg, hg⟩ := graph_neighborhood_tail_sparse θ T hθlo hθhi hT
  obtain ⟨cb, Nb, hcb, _, hb⟩ := bipartite_neighborhood_tail_sparse θ T hθlo hθhi hT
  refine ⟨min cg cb, max Ng Nb, lt_min hcg hcb, hNg.trans (le_max_left _ _), ?_⟩
  intro n hn p hw
  have hgraph := hg n ((le_max_left _ _).trans hn) p hw
  have hbip := hb n ((le_max_right _ _).trans hn) p hw
  exact ⟨hgraph.1, hgraph.2.1, hgraph.2.2.mono (min_le_left _ _),
    hbip.2.2.mono (min_le_right _ _)⟩


theorem carrier_neighborhood_tail_sparse (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ c : ℝ, ∃ n₀ : ℕ, 0 < c ∧ 3 ≤ n₀ ∧
      (∀ (V : Type*) [Fintype V], n₀ ≤ Fintype.card V →
        ∀ p : ℝ, SparseDensityWindow θ T (Fintype.card V) p →
          0 < p ∧ p < 1 ∧ GraphCarrierConclusion c T V p) ∧
      (∀ (L R : Type*) [Fintype L] [Fintype R], n₀ ≤ Fintype.card R →
        ∀ p : ℝ, SparseDensityWindow θ T (Fintype.card R) p →
          0 < p ∧ p < 1 ∧ BipartiteCarrierConclusion c T L R p) := by
  obtain ⟨c, n₀, hc, hn₀, h⟩ := neighborhood_tail_sparse θ T hθlo hθhi hT
  refine ⟨c, n₀, hc, hn₀, ?_, ?_⟩
  · intro V _ hn p hp
    have hh := h (Fintype.card V) hn p hp
    exact ⟨hh.1, hh.2.1, graphCarrierConclusion_of_fin V hh.2.2.1⟩
  · intro L R _ _ hn p hp
    have hh := h (Fintype.card R) hn p hp
    exact ⟨hh.1, hh.2.1, bipartiteCarrierConclusion_of_fin hh.2.2.2⟩


end MajorityDynamics.Probability.NeighborhoodTail

