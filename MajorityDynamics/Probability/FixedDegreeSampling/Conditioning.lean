import MajorityDynamics.Probability.FixedDegreeSampling.Laws
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
noncomputable section
open MeasureTheory ProbabilityTheory unitInterval
open scoped Classical ENNReal NNReal
namespace MajorityDynamics.Probability.FixedDegreeSampling
variable {V L R : Type*} [Fintype V] [Fintype L] [Fintype R]

theorem graph_edge_count_constant (d : V → ℕ) (G H : graphFamily d) :
    G.val.edgeSet.ncard = H.val.edgeSet.ncard := by
  have hg := G.val.sum_degrees_eq_twice_card_edges
  have hh := H.val.sum_degrees_eq_twice_card_edges
  have he : ∑ u, G.val.degree u = ∑ u, H.val.degree u := by
    apply Finset.sum_congr rfl
    intro u _
    rw [G.property u, H.property u]
  have hc : G.val.edgeFinset.card = H.val.edgeFinset.card := by omega
  simpa [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card'] using hc

omit [Fintype V] [Fintype L] [Fintype R] in
theorem bernoulli_weight_ne_zero (p : I) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (m k : ℕ) :
    (toNNReal p : ℝ≥0∞) ^ m * (toNNReal (σ p) : ℝ≥0∞) ^ k ≠ 0 := by
  apply mul_ne_zero <;> apply pow_ne_zero
  · apply ENNReal.coe_ne_zero.mpr
    intro h
    exact hp.ne' (congrArg (fun x : ℝ≥0 => (x : ℝ)) h)
  · have h : (0 : ℝ) < (σ p : ℝ) := by rw [coe_symm_eq]; linarith
    apply ENNReal.coe_ne_zero.mpr
    intro hz
    exact h.ne' (congrArg (fun x : ℝ≥0 => (x : ℝ)) hz)

theorem graph_conditional_bernoulli (d : V → ℕ) (h : (graphFamily d).Nonempty)
    (p : I) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    0 < SimpleGraph.binomialRandom V p (graphFamily d) ∧
      cond (SimpleGraph.binomialRandom V p) (graphFamily d) = fixedDegreeLaw d := by
  obtain ⟨G, hG⟩ := h
  apply conditional_eq_uniform _ _ ⟨G, hG⟩
    ((toNNReal p : ℝ≥0∞) ^ G.edgeSet.ncard *
      (toNNReal (σ p) : ℝ≥0∞) ^ ((Nat.card V).choose 2 - G.edgeSet.ncard))
    (bernoulli_weight_ne_zero p hp hp1 _ _)
  intro H hH
  rw [SimpleGraph.binomialRandom_singleton,
    graph_edge_count_constant d ⟨H, hH⟩ ⟨G, hG⟩]

theorem bipartite_edge_count (E : CrossEdges L R) :
    E.ncard = ∑ u, leftDegree E u := by
  rw [Set.ncard_eq_toFinset_card']
  have he : E.toFinset = Finset.univ.filter (fun x : L × R => x ∈ E) := by ext; simp
  rw [he, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
  simp only [leftDegree, leftNeighbors, Finset.card_eq_sum_ones, Finset.sum_filter]

theorem bipartite_edge_count_constant (a : L → ℕ) (b : R → ℕ)
    (E F : bipartiteFamily a b) : E.val.ncard = F.val.ncard := by
  rw [bipartite_edge_count, bipartite_edge_count]
  apply Finset.sum_congr rfl
  intro u _
  rw [E.property.1 u, F.property.1 u]

theorem bipartite_conditional_bernoulli (a : L → ℕ) (b : R → ℕ)
    (h : (bipartiteFamily a b).Nonempty) (p : I)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    0 < bipartiteBernoulliLaw p (bipartiteFamily a b) ∧
      cond (bipartiteBernoulliLaw p) (bipartiteFamily a b) = bipartiteFixedDegreeLaw a b := by
  obtain ⟨E, hE⟩ := h
  unfold bipartiteBernoulliLaw
  apply conditional_eq_uniform _ _ ⟨E, hE⟩
    ((toNNReal p : ℝ≥0∞) ^ E.ncard *
      (toNNReal (σ p) : ℝ≥0∞) ^ ((Set.univ : Set (L × R)).ncard - E.ncard))
    (bernoulli_weight_ne_zero p hp hp1 _ _)
  intro F hF
  rw [setBernoulli_singleton p (Set.subset_univ _) Set.finite_univ,
    Set.ncard_sdiff (Set.subset_univ _),
    bipartite_edge_count_constant a b ⟨F, hF⟩ ⟨E, hE⟩]
end MajorityDynamics.Probability.FixedDegreeSampling
