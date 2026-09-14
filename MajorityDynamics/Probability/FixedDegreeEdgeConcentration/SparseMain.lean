import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Main
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.SparseUniformEdges
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.SparseTailAssembly
noncomputable section
universe u v w
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators
namespace MajorityDynamics.Probability.FixedDegreeEdgeConcentration
open FixedDegreeSampling Numerics Literature.EdgeProbabilities
theorem graph_concentration_sparse {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ, SparseDensityWindow θ T p N →
      ∀ (V : Type u) [Fintype V] (m : ℕ) (d : V → ℕ),
        GraphInput N m p T d → GraphConcentration N m p d := by
  obtain ⟨C,hC,N₁,h₁⟩ := uniform_graph_edges_sparse.{u} hθlo hθhi hT
  obtain ⟨N₂,h₂⟩ := eventually_originalScales_sparse hθlo hθhi hT
  obtain ⟨N₃,h₃⟩ := eventually_tail_consumers_sparse.{u,0,0} hθlo hθhi hT hC.le (K:=2) (by norm_num)
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

theorem bipartite_concentration_sparse {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ, SparseDensityWindow θ T p N →
      ∀ (L : Type u) (R : Type v) [Fintype L] [Fintype R]
        (ell m : ℕ) (a : L → ℕ) (b : R → ℕ),
        BipartiteInput ell N m p T a b → BipartiteConcentration N m p a b := by
  obtain ⟨C,hC,N₁,h₁⟩ := uniform_bipartite_edges_sparse.{u,v} hθlo hθhi hT
  obtain ⟨N₂,h₂⟩ := eventually_originalScales_sparse hθlo hθhi hT
  have hT0 : 0 < T := by linarith
  obtain ⟨N₃,h₃⟩ := eventually_tail_consumers_sparse.{0,u,v} hθlo hθhi hT hC.le (K:=2*T) (by positivity)
  refine ⟨max N₁ (max N₂ N₃), ?_⟩
  intro N hN p hp L R _ _ ell m a b hi U W
  have he := h₁ N ((le_max_left _ _).trans hN) p hp L R ell m a b hi
  have hs := h₂ N (((le_max_left _ _).trans (le_max_right _ _)).trans hN) p hp
  have ht := h₃ N (((le_max_right _ _).trans (le_max_right _ _)).trans hN) p hp
  have hb := hi.original_bounds hs
  apply ht.2 L R a b m U W (hi.realized hs) hi.total_left hi.total_right _ he.1 he.2
  nlinarith [hb.2.2.2]

theorem c1_sparse {θ T : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ, SparseDensityWindow θ T p N →
      (∀ (V : Type u) [Fintype V] (m : ℕ) (d : V → ℕ),
        GraphInput N m p T d → GraphConcentration N m p d) ∧
      (∀ (L : Type v) (R : Type w) [Fintype L] [Fintype R]
        (ell m : ℕ) (a : L → ℕ) (b : R → ℕ),
        BipartiteInput ell N m p T a b → BipartiteConcentration N m p a b) := by
  obtain ⟨N₁,h₁⟩ := graph_concentration_sparse.{u} hθlo hθhi hT
  obtain ⟨N₂,h₂⟩ := bipartite_concentration_sparse.{v,w} hθlo hθhi hT
  exact ⟨max N₁ N₂,fun N hN p hp =>
    ⟨h₁ N ((le_max_left _ _).trans hN) p hp,
      h₂ N ((le_max_right _ _).trans hN) p hp⟩⟩

end MajorityDynamics.Probability.FixedDegreeEdgeConcentration
