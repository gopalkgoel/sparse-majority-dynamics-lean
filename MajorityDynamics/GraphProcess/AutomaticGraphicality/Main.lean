import MajorityDynamics.GraphProcess.AutomaticGraphicality.Finite
import MajorityDynamics.GraphProcess.AutomaticGraphicality.Asymptotics

/-! Complete Appendix B.1: the threshold precedes every finite graph carrier,
partition, ordered count array, density, and ambient degree array. -/
noncomputable section
namespace MajorityDynamics.GraphProcess.AutomaticGraphicality
universe u

/-- Automatic graphicality, uniformly throughout the manuscript's density window.
The threshold is independent even of the history length. The carrier's Boolean
regularity flag has no role; κ is imposed on the supplied degree array itself. -/
theorem automatic_graphicality {θ T : ℝ}
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ (n : ℕ) (p : ℝ),
      T⁻¹ * (N : ℝ) ^ (-θ) < p → p < T * (N : ℝ) ^ (-θ) →
      ∀ (y : Local.CoarseData V n) (d : RowArray.Ambient y.part),
      (∀ s, (N : ℝ) / T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ) - p * (y.sizes s : ℝ) * (y.sizes t : ℝ)| ≤
        T * (N : ℝ) ^ 2 * p / Real.sqrt (p * N)) →
      RowArray.totals d = y.edge → RowArray.Regular p d → GraphicalArray.Graphical d := by
  obtain ⟨N₀, hN₀⟩ := eventually_regime hθlo hθhi hT
  refine ⟨N₀, ?_⟩
  intro N hN V inst hcard n p hpLo hpHi y d hsizes hcounts htot hreg
  obtain ⟨hNpos, hppos, hx, hxT, hpSmall⟩ := hN₀ N hN p hpLo hpHi
  subst N
  exact finite_graphicality y d hNpos hT hppos hx hxT hpSmall hsizes hcounts htot hreg

/-- The same closed lemma with the literal graph-existence conclusion expanded. -/
theorem automatic_graphicality_exists {θ T : ℝ}
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ (n : ℕ) (p : ℝ),
      T⁻¹ * (N : ℝ) ^ (-θ) < p → p < T * (N : ℝ) ^ (-θ) →
      ∀ (y : Local.CoarseData V n) (d : RowArray.Ambient y.part),
      (∀ s, (N : ℝ) / T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ) - p * (y.sizes s : ℝ) * (y.sizes t : ℝ)| ≤
        T * (N : ℝ) ^ 2 * p / Real.sqrt (p * N)) →
      RowArray.totals d = y.edge → RowArray.Regular p d →
      ∃ G : SimpleGraph V, History.degreeArray y.part G = RowArray.values d :=
  automatic_graphicality hθlo hθhi hT

end MajorityDynamics.GraphProcess.AutomaticGraphicality
