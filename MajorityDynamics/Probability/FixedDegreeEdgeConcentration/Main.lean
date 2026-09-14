import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.UniformEdges
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.TailAssembly

noncomputable section
universe u v w
open scoped Classical BigOperators
namespace MajorityDynamics.Probability.FixedDegreeEdgeConcentration
open FixedDegreeSampling

/-- The two graph clauses of C.1, on every literal subset. Balanced subsets from
the manuscript are a special case of this stronger conclusion. -/
def GraphConcentration {V : Type*} [Fintype V] (N m : ℕ) (p : ℝ) (d : V → ℕ) : Prop :=
  ∀ U : Finset V,
    (fixedDegreeLaw d).real {G | edgeThreshold N p ≤
      |(internalCount U G:ℝ)-(∑ v ∈ U, (d v:ℝ))^2/(4*m)|} < 1/Real.log N ∧
    (fixedDegreeLaw d).real {G | edgeThreshold N p ≤
      |(cutCount U G:ℝ)-(∑ v ∈ U, (d v:ℝ))*(∑ v ∈ Finset.univ \ U, (d v:ℝ))/(2*m)|} <
        1/Real.log N

/-- The bipartite rectangle clause of C.1, including every balanced rectangle. -/
def BipartiteConcentration {L R : Type*} [Fintype L] [Fintype R]
    (N m : ℕ) (p : ℝ) (a : L → ℕ) (b : R → ℕ) : Prop :=
  ∀ (U : Finset L) (W : Finset R),
    (bipartiteFixedDegreeLaw a b).real {E | edgeThreshold N p ≤
      |(rectangleCount U W E:ℝ)-(∑ i ∈ U, (a i:ℝ))*(∑ j ∈ W, (b j:ℝ))/m|} < 1/Real.log N

/-- Full original-input graph C.1. The only imported probability theorem is the
cited graph single-edge formula; realization is derived through Erdős–Gallai. -/
theorem graph_concentration {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ, DensityWindow θ T p N →
      ∀ (V : Type u) [Fintype V] (m : ℕ) (d : V → ℕ),
        GraphInput N m p T d → GraphConcentration N m p d := by
  obtain ⟨C,hC,N₁,h₁⟩ := uniform_graph_edges.{u} hθlo hθhi hT
  obtain ⟨N₂,h₂⟩ := eventually_originalScales hθlo hθhi hT
  obtain ⟨N₃,h₃⟩ := eventually_tail_consumers.{u,0,0} hθlo hθhi hT hC.le (K:=2) (by norm_num)
  refine ⟨max N₁ (max N₂ N₃), ?_⟩
  intro N hN p hp V _ m d hi U
  have he := h₁ N ((le_max_left _ _).trans hN) p hp V m d hi
  have hs := h₂ N (((le_max_left _ _).trans (le_max_right _ _)).trans hN) p hp
  have ht := h₃ N (((le_max_right _ _).trans (le_max_right _ _)).trans hN) p hp
  have hb := hi.original_bounds hs
  have hp0 := hs.p_pos
  have hNN : 0 ≤ (N:ℝ)^2*p := by positivity
  apply ht.1 V d m U (hi.realized hs) hi.total _ (fun v => (hb.1 v).2) he.1 he.2
  nlinarith [hb.2.2]

/-- Full original-input bipartite C.1. Both degree tolerances remain p*N; the
cited bipartite edge formula and Gale–Ryser are the only external inputs used. -/
theorem bipartite_concentration {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ, DensityWindow θ T p N →
      ∀ (L : Type u) (R : Type v) [Fintype L] [Fintype R]
        (ell m : ℕ) (a : L → ℕ) (b : R → ℕ),
        BipartiteInput ell N m p T a b → BipartiteConcentration N m p a b := by
  obtain ⟨C,hC,N₁,h₁⟩ := uniform_bipartite_edges.{u,v} hθlo hθhi hT
  obtain ⟨N₂,h₂⟩ := eventually_originalScales hθlo hθhi hT
  have hT0 : 0 < T := by linarith
  obtain ⟨N₃,h₃⟩ := eventually_tail_consumers.{0,u,v} hθlo hθhi hT hC.le (K:=2*T) (by positivity)
  refine ⟨max N₁ (max N₂ N₃), ?_⟩
  intro N hN p hp L R _ _ ell m a b hi U W
  have he := h₁ N ((le_max_left _ _).trans hN) p hp L R ell m a b hi
  have hs := h₂ N (((le_max_left _ _).trans (le_max_right _ _)).trans hN) p hp
  have ht := h₃ N (((le_max_right _ _).trans (le_max_right _ _)).trans hN) p hp
  have hb := hi.original_bounds hs
  apply ht.2 L R a b m U W (hi.realized hs) hi.total_left hi.total_right _ he.1 he.2
  nlinarith [hb.2.2.2]

/-- A common original-input threshold for all three C.1 clauses, before every
graph, bipartite graph, density, total and subset. -/
theorem c1 {θ T : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ, DensityWindow θ T p N →
      (∀ (V : Type u) [Fintype V] (m : ℕ) (d : V → ℕ),
        GraphInput N m p T d → GraphConcentration N m p d) ∧
      (∀ (L : Type v) (R : Type w) [Fintype L] [Fintype R]
        (ell m : ℕ) (a : L → ℕ) (b : R → ℕ),
        BipartiteInput ell N m p T a b → BipartiteConcentration N m p a b) := by
  obtain ⟨N₁,h₁⟩ := graph_concentration.{u} hθlo hθhi hT
  obtain ⟨N₂,h₂⟩ := bipartite_concentration.{v,w} hθlo hθhi hT
  exact ⟨max N₁ N₂,fun N hN p hp =>
    ⟨h₁ N ((le_max_left _ _).trans hN) p hp,
      h₂ N ((le_max_right _ _).trans hN) p hp⟩⟩

end MajorityDynamics.Probability.FixedDegreeEdgeConcentration
