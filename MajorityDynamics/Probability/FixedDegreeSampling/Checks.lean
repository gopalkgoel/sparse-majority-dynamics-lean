import MajorityDynamics.Probability.FixedDegreeSampling.Main
noncomputable section
open MeasureTheory ProbabilityTheory unitInterval
open scoped Classical ENNReal
namespace MajorityDynamics.Probability.FixedDegreeSampling
variable {V L R : Type*} [Fintype V] [Fintype L] [Fintype R]

example : GraphNeighborhoodProbabilityTheorem (V := V) := graph_neighborhood_probability
example : GraphConditionalLawTheorem (V := V) := graph_conditional_bernoulli
example : BipartiteNeighborhoodProbabilityTheorem (L := L) (R := R) :=
  bipartite_neighborhood_probability
example : BipartiteConditionalLawTheorem (L := L) (R := R) := bipartite_conditional_bernoulli

-- Expanded degree-fiber predicates and residual degrees, with actual graph objects.
example (d : V → ℕ) (v : V) (S : Finset V)
    (hv : v ∉ S) (hs : S.card = d v) (hd : ∀ u ∈ S, 1 ≤ d u) :
    {G : SimpleGraph V // (∀ u, G.degree u = d u) ∧ G.neighborFinset v = S} ≃
      {H : SimpleGraph {u : V // u ≠ v} //
        ∀ u, H.degree u = d u - if u.val ∈ S then 1 else 0} :=
  graph_neighborhood_removal_equiv d v S ⟨hv, hs, hd⟩

example (d : V → ℕ) (v : V) (S : Finset V)
    (hv : v ∉ S) (hs : S.card = d v) (hd : ∀ u ∈ S, 1 ≤ d u) :
    uniformOn {G : SimpleGraph V | ∀ u, G.degree u = d u}
      {G | G.neighborFinset v = S} =
    (({H : SimpleGraph {u : V // u ≠ v} |
      ∀ u, H.degree u = d u - if u.val ∈ S then 1 else 0}.ncard : ℕ) : ℝ≥0∞) /
      ({G : SimpleGraph V | ∀ u, G.degree u = d u}.ncard : ℝ≥0∞) :=
  graph_neighborhood_probability d v S ⟨hv, hs, hd⟩

example (d : V → ℕ) (v : V) (S : Finset V)
    (h : ¬ (v ∉ S ∧ S.card = d v ∧ ∀ u ∈ S, 1 ≤ d u)) :
    uniformOn {G : SimpleGraph V | ∀ u, G.degree u = d u}
      {G | G.neighborFinset v = S} = 0 := graph_invalid_neighborhood d v S h

example (d : V → ℕ) (h : ∃ G : SimpleGraph V, ∀ u, G.degree u = d u)
    (p : I) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    0 < SimpleGraph.binomialRandom V p {G | ∀ u, G.degree u = d u} ∧
    cond (SimpleGraph.binomialRandom V p) {G | ∀ u, G.degree u = d u} =
      uniformOn {G : SimpleGraph V | ∀ u, G.degree u = d u} :=
  graph_conditional_bernoulli d h p hp hp1

example (d : V → ℕ) (h : ∃ G : SimpleGraph V, ∀ u, G.degree u = d u) :
    IsProbabilityMeasure (fixedDegreeLaw d) := fixedDegreeLaw_normalized d h

example (a : L → ℕ) (b : R → ℕ) (v : L) (S : Finset R)
    (hs : S.card = a v) (hb : ∀ w ∈ S, 1 ≤ b w) :
    {E : Set (L × R) //
      ((∀ u, (Finset.univ.filter fun w => (u, w) ∈ E).card = a u) ∧
        ∀ w, (Finset.univ.filter fun u => (u, w) ∈ E).card = b w) ∧
      (Finset.univ.filter fun w => (v, w) ∈ E) = S} ≃
    {E : Set ({u : L // u ≠ v} × R) //
      (∀ u, (Finset.univ.filter fun w => (u, w) ∈ E).card = a u) ∧
      ∀ w, (Finset.univ.filter fun u => (u, w) ∈ E).card = b w - if w ∈ S then 1 else 0} :=
  bipartite_neighborhood_removal_equiv a b v S ⟨hs, hb⟩

example (a : L → ℕ) (b : R → ℕ) (v : L) (S : Finset R)
    (hs : S.card = a v) (hb : ∀ w ∈ S, 1 ≤ b w) :
    bipartiteFixedDegreeLaw a b {E | (Finset.univ.filter fun w => (v, w) ∈ E) = S} =
    (({E : Set ({u : L // u ≠ v} × R) |
      (∀ u, (Finset.univ.filter fun w => (u, w) ∈ E).card = a u) ∧
      ∀ w, (Finset.univ.filter fun u => (u, w) ∈ E).card = b w - if w ∈ S then 1 else 0}.ncard : ℕ) : ℝ≥0∞) /
      bipartiteCount a b := bipartite_neighborhood_probability a b v S ⟨hs, hb⟩

example (a : L → ℕ) (b : R → ℕ) (v : L) (S : Finset R)
    (h : ¬ (S.card = a v ∧ ∀ w ∈ S, 1 ≤ b w)) :
    bipartiteFixedDegreeLaw a b {E | leftNeighbors E v = S} = 0 :=
  bipartite_invalid_neighborhood a b v S h

example (a : L → ℕ) (b : R → ℕ)
    (h : ∃ E : Set (L × R),
      (∀ u, (Finset.univ.filter fun w => (u, w) ∈ E).card = a u) ∧
      ∀ w, (Finset.univ.filter fun u => (u, w) ∈ E).card = b w)
    (p : I) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    0 < setBer((Set.univ : Set (L × R)), p) (bipartiteFamily a b) ∧
    cond setBer((Set.univ : Set (L × R)), p) (bipartiteFamily a b) =
      uniformOn (bipartiteFamily a b) := bipartite_conditional_bernoulli a b h p hp hp1

example (a : L → ℕ) (b : R → ℕ) (h : (bipartiteFamily a b).Nonempty) :
    IsProbabilityMeasure (bipartiteFixedDegreeLaw a b) := bipartiteFixedDegreeLaw_normalized a b h

example (E : Set (L × R)) (u : L) : (bipartiteGraph E).degree (.inl u) =
    (Finset.univ.filter fun w => (u, w) ∈ E).card := degree_inl E u
example (E : Set (L × R)) (w : R) : (bipartiteGraph E).degree (.inr w) =
    (Finset.univ.filter fun u => (u, w) ∈ E).card := degree_inr E w

example (d : V → ℕ) (G : SimpleGraph V) :
    fixedDegreeLaw d {G} =
      if (∀ u, G.degree u = d u) then
        ({H : SimpleGraph V | ∀ u, H.degree u = d u}.ncard : ℝ≥0∞)⁻¹ else 0 :=
  by
    convert fixedDegreeLaw_singleton d G using 1; simp only [graphFamily, graphCount]
    congr 1

example (d : V → ℕ) (f : SimpleGraph V → ℝ) :
    ∫ G, f G ∂fixedDegreeLaw d =
      (∑ G ∈ {G : SimpleGraph V | ∀ u, G.degree u = d u}.toFinset, f G) /
      ({G : SimpleGraph V | ∀ u, G.degree u = d u}.ncard : ℝ) :=
  by
    convert fixedDegreeLaw_integral d f using 1
    congr 2
    ext H
    simp only [Set.mem_toFinset]
    rfl

example (a : L → ℕ) (b : R → ℕ) (E : Set (L × R)) :
    bipartiteFixedDegreeLaw a b {E} =
      if ((∀ u, (Finset.univ.filter fun w => (u, w) ∈ E).card = a u) ∧
          ∀ w, (Finset.univ.filter fun u => (u, w) ∈ E).card = b w) then
        (bipartiteCount a b : ℝ≥0∞)⁻¹ else 0 :=
  by
    convert bipartiteFixedDegreeLaw_singleton a b E using 1
    congr 1

example (a : L → ℕ) (b : R → ℕ) (f : Set (L × R) → ℝ) :
    ∫ E, f E ∂bipartiteFixedDegreeLaw a b =
      (∑ E ∈ (bipartiteFamily a b).toFinset, f E) / (bipartiteCount a b : ℝ) :=
  bipartiteFixedDegreeLaw_integral a b f

end MajorityDynamics.Probability.FixedDegreeSampling
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.fixedDegreeLaw_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.fixedDegreeLaw_normalized
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.fixedDegreeLaw_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.fixedDegreeLaw_singleton
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.fixedDegreeLaw_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.fixedDegreeLaw_integral
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.graph_neighborhood_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.graph_neighborhood_probability
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.graph_invalid_neighborhood' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.graph_invalid_neighborhood
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.bipartiteFixedDegreeLaw_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.bipartiteFixedDegreeLaw_normalized
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.bipartiteFixedDegreeLaw_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.bipartiteFixedDegreeLaw_singleton
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.bipartiteFixedDegreeLaw_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.bipartiteFixedDegreeLaw_integral
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.bipartite_neighborhood_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.bipartite_neighborhood_probability
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.bipartite_invalid_neighborhood' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.bipartite_invalid_neighborhood
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.graph_edge_count_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.graph_edge_count_constant
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.bernoulli_weight_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.bernoulli_weight_ne_zero
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.graph_conditional_bernoulli' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.graph_conditional_bernoulli
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.bipartite_edge_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.bipartite_edge_count
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.bipartite_edge_count_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.bipartite_edge_count_constant
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.bipartite_conditional_bernoulli' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.bipartite_conditional_bernoulli
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.bipartiteGraph_adj_inl_inr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.bipartiteGraph_adj_inl_inr
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.bipartiteGraph_not_adj_inl_inl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.bipartiteGraph_not_adj_inl_inl
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.bipartiteGraph_not_adj_inr_inr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.bipartiteGraph_not_adj_inr_inr
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.bipartiteGraph_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.bipartiteGraph_injective
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.measurable_bipartiteGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.measurable_bipartiteGraph
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.degree_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.degree_inl
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.degree_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.degree_inr
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.bipartiteGraph_surjective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.bipartiteGraph_surjective
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.graph_neighborhood_removal_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.graph_neighborhood_removal_equiv
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.bipartite_neighborhood_removal_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.bipartite_neighborhood_removal_equiv
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.delete_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.delete_insert
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.insert_delete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.insert_delete
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.delete_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.delete_degree
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.insert_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.insert_degree
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.residualDegree_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.residualDegree_add
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.deleteLeft_insertLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.deleteLeft_insertLeft
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.insertLeft_deleteLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.insertLeft_deleteLeft
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.deleteLeft_rightDegree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.deleteLeft_rightDegree
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.insertLeft_rightDegree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.insertLeft_rightDegree
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.bipartiteGraph_fin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.bipartiteGraph_fin
/-- info: 'MajorityDynamics.Probability.FixedDegreeSampling.bipartiteBernoulliLaw_fin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeSampling.bipartiteBernoulliLaw_fin
