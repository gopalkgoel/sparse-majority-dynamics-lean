import MajorityDynamics.GraphProcess.EnumerationBounds.Preparation
import MajorityDynamics.GraphProcess.EnumerationBounds.Corrections

/-! Closed numerical B.2 endpoints, uniformly in the paper's density window. -/
noncomputable section
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.EnumerationBounds
universe u

/-- Weak correction estimate. Constants precede all varying finite data. -/
theorem uniform_weak_correction {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (d : RowArray.Ambient y.part),
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
      RowArray.totals d = y.edge → RowArray.Regular p d →
      |correction y d| ≤ C*(p*N)^(2/7:ℝ) := by
  obtain ⟨N₀, hN₀⟩ := uniform_preparation hθlo hθhi hT
  refine ⟨weakConstant n T, weakConstant_pos n T, N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi y d hsizes hcounts _htot hreg
  have h := hN₀ N hN V hcard n p hlo hhi y d hsizes hcounts hreg
  simpa only [hcard] using weak_correction_bound hT h

/-- Strong correction estimate under the original normalized Gamma predicate. -/
theorem uniform_strong_correction {θ T CΓ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hΓ : 0 < CΓ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (d : RowArray.Ambient y.part),
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
      RowArray.totals d = y.edge → RowArray.Regular p d →
      RowArray.Gamma y.part y.edge CΓ p d → |correction y d| ≤ C := by
  obtain ⟨N₀, hN₀⟩ := uniform_preparation hθlo hθhi hT
  refine ⟨strongConstant n T CΓ, strongConstant_pos n hΓ, N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi y d hsizes hcounts _htot hreg hgamma
  have h := hN₀ N hN V hcard n p hlo hhi y d hsizes hcounts hreg
  exact strong_correction_bound hT h hΓ hgamma

end MajorityDynamics.GraphProcess.EnumerationBounds
