import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.UniformEdges
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.SparseRelative
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.SparseOriginal
noncomputable section
universe u v w
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators
namespace MajorityDynamics.Probability.FixedDegreeEdgeConcentration
open FixedDegreeSampling Numerics Literature.EdgeProbabilities
theorem uniform_graph_edges_sparse {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      SparseDensityWindow θ T p N → ∀ (V : Type u) [Fintype V] (m : ℕ) (d : V → ℕ),
      GraphInput N m p T d →
      (∀ e : Sym2 V, ¬e.IsDiag →
        |(fixedDegreeLaw d).real {G | e ∈ G.edgeSet} - graphWeight d m e| ≤
          C*Numerics.epsilon N p*graphWeight d m e) ∧
      (∀ e f : Sym2 V, ¬e.IsDiag → ¬f.IsDiag → e ≠ f →
        (fixedDegreeLaw d).real {G | e ∈ G.edgeSet ∧ f ∈ G.edgeSet} ≤
          (1+C*Numerics.epsilon N p)*graphWeight d m e*graphWeight d m f) := by
  obtain ⟨C,hC,N₁,h₁⟩ := graph_window_relative_error_sparse.{u} hθlo hθhi hT
    (K:=2*T+2) (A:=4) (by linarith)
  obtain ⟨N₂,h₂⟩ := eventually_originalScales_sparse hθlo hθhi hT
  obtain ⟨N₃,h₃⟩ := Numerics.eventually_epsilon_sparse hθlo hθhi hT (η:=1) zero_lt_one
  refine ⟨jointConstant C 8, hC.trans_le (le_jointConstant hC.le (by norm_num)),
    max N₁ (max N₂ N₃), ?_⟩
  intro N hN p hp V _ m d hi
  have hs := h₂ N (((le_max_left _ _).trans (le_max_right _ _)).trans hN) p hp
  have he := h₃ N (((le_max_right _ _).trans (le_max_right _ _)).trans hN) p hp.1 hp.2
  exact graph_edges_of_window_bound d hi hs hC.le he.2
    (h₁ N ((le_max_left _ _).trans hN) p hp)

theorem uniform_bipartite_edges_sparse {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      SparseDensityWindow θ T p N → ∀ (L : Type u) (R : Type v) [Fintype L] [Fintype R]
      (ell m : ℕ) (a : L → ℕ) (b : R → ℕ),
      BipartiteInput ell N m p T a b →
      (∀ e : L × R,
        |(bipartiteFixedDegreeLaw a b).real {E | e ∈ E} - bipartiteWeight a b m e| ≤
          C*Numerics.epsilon N p*bipartiteWeight a b m e) ∧
      (∀ e f : L × R, e ≠ f →
        (bipartiteFixedDegreeLaw a b).real {E | e ∈ E ∧ f ∈ E} ≤
          (1+C*Numerics.epsilon N p)*bipartiteWeight a b m e*bipartiteWeight a b m f) := by
  obtain ⟨C,hC,N₁,h₁⟩ := bipartite_window_relative_error_sparse.{u,v} hθlo hθhi hT
    (K:=2*T+2) (A:=4) (by linarith)
  obtain ⟨N₂,h₂⟩ := eventually_originalScales_sparse hθlo hθhi hT
  obtain ⟨N₃,h₃⟩ := Numerics.eventually_epsilon_sparse hθlo hθhi hT (η:=1) zero_lt_one
  refine ⟨jointConstant C (4*T^2), hC.trans_le (le_jointConstant hC.le (by positivity)),
    max N₁ (max N₂ N₃), ?_⟩
  intro N hN p hp L R _ _ ell m a b hi
  have hs := h₂ N (((le_max_left _ _).trans (le_max_right _ _)).trans hN) p hp
  have he := h₃ N (((le_max_right _ _).trans (le_max_right _ _)).trans hN) p hp.1 hp.2
  exact bipartite_edges_of_window_bound a b hi hs hs.p_le_one hC.le he.2
    (h₁ N ((le_max_left _ _).trans hN) p hp)

end MajorityDynamics.Probability.FixedDegreeEdgeConcentration
