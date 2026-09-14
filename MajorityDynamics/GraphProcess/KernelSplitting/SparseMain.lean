import MajorityDynamics.GraphProcess.KernelSplitting.Main
import MajorityDynamics.GraphProcess.KernelSplitting.SparseRegularity
import MajorityDynamics.GraphProcess.KernelEdgeSplitting.SparseMain

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.KernelSplitting
open Universal BlockDecomposition FineKernel KernelInputs
open MajorityDynamics.Probability.NeighborhoodTail
open MajorityDynamics.Combinatorics.DegreeRatios
universe u

theorem kernel_splitting_estimates_sparse {θ T φ Cf A : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) (hCf : 0 ≤ Cf) (hA : 0 < A) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-(1/2:ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      Local.Admissible y q T φ p → ∀ σ : FineState.State V n,
      CoarseKernel.rho p σ = y → DegreeTypical y p σ → SizeTypical y q Cf σ →
      (K σ).real {τ | ¬ LocalTransition.KernelGood y p (2*T) σ τ} ≤
        (N:ℝ)^(-A) + KernelEdgeSplitting.unionError n N := by
  obtain ⟨N₁,h₁⟩ := uniform_regularity_failure_sparse.{u} n hθlo hθhi hT hφ hφ1 hCf hA
  obtain ⟨N₂,h₂⟩ := KernelEdgeSplitting.uniform_kernelGood_failure_sparse.{u}
    n hθlo hθhi hT hφ hφ1 hCf
  refine ⟨max N₁ N₂,?_⟩
  intro N hN V inst hcard p hlo hhi y q hLA σ hρ hR1 hR2
  exact h₂ N ((le_max_right _ _).trans hN) V hcard p hlo hhi y q hLA σ hρ hR1 hR2
    ((N:ℝ)^(-A))
    (h₁ N ((le_max_left _ _).trans hN) V hcard p hlo hhi y q hLA σ hρ hR1 hR2)

theorem kernel_splitting_estimates_epsilon_sparse {θ T φ Cf ε : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) (hCf : 0 ≤ Cf) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-(1/2:ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      Local.Admissible y q T φ p → ∀ σ : FineState.State V n,
      CoarseKernel.rho p σ = y → DegreeTypical y p σ → SizeTypical y q Cf σ →
      (K σ).real {τ | ¬ LocalTransition.KernelGood y p (2*T) σ τ} ≤ ε := by
  obtain ⟨N₁,h₁⟩ := kernel_splitting_estimates_sparse.{u} (A:=1)
    n hθlo hθhi hT hφ hφ1 hCf zero_lt_one
  obtain ⟨N₂,h₂⟩ := KernelEdgeSplitting.Numerics.eventually_unionError_lt n
    (show 0 < ε/2 by positivity)
  have hn : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun N : ℕ => (N:ℝ)^(-(1:ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop zero_lt_one).comp hn
  obtain ⟨N₃,h₃⟩ := eventually_atTop.mp
    (ht.eventually (eventually_lt_nhds (show 0 < ε/2 by positivity)))
  refine ⟨max (max N₁ N₂) N₃,?_⟩
  intro N hN V inst hcard p hlo hhi y q hLA σ hρ hR1 hR2
  have hn1 := ((le_max_left N₁ N₂).trans (le_max_left (max N₁ N₂) N₃)).trans hN
  have hn2 := ((le_max_right N₁ N₂).trans (le_max_left (max N₁ N₂) N₃)).trans hN
  have hn3 := (le_max_right (max N₁ N₂) N₃).trans hN
  exact (h₁ N hn1 V hcard p hlo hhi y q hLA σ hρ hR1 hR2).trans
    (by linarith [h₂ N hn2,h₃ N hn3])

theorem typical_kernel_splitting_estimates_sparse {θ T φ Cf A : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) (hCf : 0 ≤ Cf) (hA : 0 < A) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-(1/2:ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      Local.Admissible y q T φ p → ∀ σ : FineState.State V n,
      CoarseKernel.rho p σ = y → LocalTransition.FiberTypical y q p Cf σ →
      (K σ).real {τ | ¬ LocalTransition.KernelGood y p (2*T) σ τ} ≤
        (N:ℝ)^(-A) + KernelEdgeSplitting.unionError n N := by
  obtain ⟨N₀,h₀⟩ := kernel_splitting_estimates_sparse.{u} n hθlo hθhi hT hφ hφ1 hCf hA
  refine ⟨N₀,?_⟩
  intro N hN V inst hcard p hlo hhi y q hLA σ hρ htyp
  exact h₀ N hN V hcard p hlo hhi y q hLA σ hρ htyp.1 htyp.2.1

theorem typical_kernel_splitting_epsilon_sparse {θ T φ Cf ε : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) (hCf : 0 ≤ Cf) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-(1/2:ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      Local.Admissible y q T φ p → ∀ σ : FineState.State V n,
      CoarseKernel.rho p σ = y → LocalTransition.FiberTypical y q p Cf σ →
      (K σ).real {τ | ¬ LocalTransition.KernelGood y p (2*T) σ τ} ≤ ε := by
  obtain ⟨N₀,h₀⟩ := kernel_splitting_estimates_epsilon_sparse.{u} n hθlo hθhi hT hφ hφ1 hCf hε
  refine ⟨N₀,?_⟩
  intro N hN V inst hcard p hlo hhi y q hLA σ hρ htyp
  exact h₀ N hN V hcard p hlo hhi y q hLA σ hρ htyp.1 htyp.2.1

end MajorityDynamics.GraphProcess.KernelSplitting
