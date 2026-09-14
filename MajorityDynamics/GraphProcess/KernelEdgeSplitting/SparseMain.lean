import MajorityDynamics.GraphProcess.KernelEdgeSplitting.Main
import MajorityDynamics.GraphProcess.KernelEdgeSplitting.SparseApplications
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.SparseMain

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.KernelEdgeSplitting
open Universal BlockDecomposition
open MajorityDynamics.Probability.FixedDegreeEdgeConcentration
universe u

theorem uniform_split_edges_failure_sparse {θ T φ Cf : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) (hCf : 0 ≤ Cf) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-(1/2:ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      Local.Admissible y q T φ p → ∀ σ : FineState.State V n,
      CoarseKernel.rho p σ = y → KernelInputs.DegreeTypical y p σ →
      KernelInputs.SizeTypical y q Cf σ →
      (FineKernel.K σ).real {τ | ¬ SplitEdgesGood y p (2*T) σ τ} ≤
        unionError n N := by
  obtain ⟨U,hU,N₁,h₁⟩ := KernelInputs.uniform_inputs_sparse.{u}
    n hθlo hθhi hT hφ hφ1 hCf
  obtain ⟨r₀,hr₀⟩ := c1_sparse.{u,u,u} hθlo hθhi hU
  obtain ⟨N₂,h₂⟩ := Numerics.uniform_block_log hT r₀
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN V inst hcard p hlo hhi y q hLA σ hρ hR1 hR2
  have h := h₁ N ((le_max_left _ _).trans hN) V hcard p hlo hhi y q hLA σ hρ hR1 hR2
  have hs (s : History (n+1)) :
      r₀ ≤ y.sizes s ∧ 0 < Real.log (N : ℝ) ∧
        0 < Real.log (y.sizes s : ℝ) ∧
        1 / Real.log (y.sizes s : ℝ) ≤ 2 / Real.log (N : ℝ) := by
    apply h₂ N ((le_max_right _ _).trans hN) (y.sizes s)
    · simpa only [hcard] using (h.parent_sizes s).1
    · simpa only [hcard] using (h.parent_sizes s).2.1
  have hg (s : History (n+1)) :
      GraphConcentration (y.sizes s) (y.edge s s / 2).toNat p
        (fun v : Block σ.part s => (σ.deg v s).toNat) := by
    exact (hr₀ (y.sizes s) (hs s).1 p (h.density s)).1
      (Block σ.part s) (y.edge s s / 2).toNat
      (fun v => (σ.deg v s).toNat) (graph_input_sparse h hρ s)
  have hb (s t : History (n+1)) :
      BipartiteConcentration (y.sizes t) (y.edge s t).toNat p
        (fun v : Block σ.part s => (σ.deg v t).toNat)
        (fun w : Block σ.part t => (σ.deg w s).toNat) := by
    exact (hr₀ (y.sizes t) (hs t).1 p (h.density t)).2
      (Block σ.part s) (Block σ.part t) (y.sizes s) (y.edge s t).toNat
      (fun v => (σ.deg v t).toNat) (fun w => (σ.deg w s).toNat)
      (bipartite_input_sparse h hρ s t)
  exact K_splitEdges_failure_le y p (2*T) σ N
    (pair_failure_le_sparse h hT hρ N hg hb (fun s => (hs s).2.2.2))

theorem uniform_split_edges_failure_epsilon_sparse {θ T φ Cf ε : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) (hCf : 0 ≤ Cf) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-(1/2:ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      Local.Admissible y q T φ p → ∀ σ : FineState.State V n,
      CoarseKernel.rho p σ = y → KernelInputs.DegreeTypical y p σ →
      KernelInputs.SizeTypical y q Cf σ →
      (FineKernel.K σ).real {τ | ¬ SplitEdgesGood y p (2*T) σ τ} ≤ ε := by
  obtain ⟨N₁,h₁⟩ := uniform_split_edges_failure_sparse.{u} n hθlo hθhi hT hφ hφ1 hCf
  obtain ⟨N₂,h₂⟩ := Numerics.eventually_unionError_lt n hε
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN V inst hcard p hlo hhi y q hLA σ hρ hR1 hR2
  exact (h₁ N ((le_max_left _ _).trans hN) V hcard p hlo hhi y q hLA σ hρ hR1 hR2).trans
    (h₂ N ((le_max_right _ _).trans hN)).le

theorem uniform_kernelGood_failure_sparse {θ T φ Cf : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) (hCf : 0 ≤ Cf) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-(1/2:ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      Local.Admissible y q T φ p → ∀ σ : FineState.State V n,
      CoarseKernel.rho p σ = y → KernelInputs.DegreeTypical y p σ →
      KernelInputs.SizeTypical y q Cf σ → ∀ er : ℝ,
      (FineKernel.K σ).real {τ | ¬ CoarseKernel.Regular p τ.part τ.deg} ≤ er →
      (FineKernel.K σ).real {τ | ¬ LocalTransition.KernelGood y p (2*T) σ τ} ≤
        er + unionError n N := by
  obtain ⟨N₀,h₀⟩ := uniform_split_edges_failure_sparse.{u} n hθlo hθhi hT hφ hφ1 hCf
  refine ⟨N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi y q hLA σ hρ hR1 hR2 er hreg
  exact K_kernelGood_failure_le y p (2*T) σ er (unionError n N) hreg
    (h₀ N hN V hcard p hlo hhi y q hLA σ hρ hR1 hR2)

theorem uniform_typical_split_edges_failure_sparse {θ T φ Cf : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) (hCf : 0 ≤ Cf) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-(1/2:ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      Local.Admissible y q T φ p → ∀ σ : FineState.State V n,
      CoarseKernel.rho p σ = y → LocalTransition.FiberTypical y q p Cf σ →
      (FineKernel.K σ).real {τ | ¬ SplitEdgesGood y p (2*T) σ τ} ≤
        unionError n N := by
  obtain ⟨N₀,h₀⟩ := uniform_split_edges_failure_sparse.{u} n hθlo hθhi hT hφ hφ1 hCf
  refine ⟨N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi y q hLA σ hρ htyp
  exact h₀ N hN V hcard p hlo hhi y q hLA σ hρ htyp.1 htyp.2.1

end MajorityDynamics.GraphProcess.KernelEdgeSplitting
