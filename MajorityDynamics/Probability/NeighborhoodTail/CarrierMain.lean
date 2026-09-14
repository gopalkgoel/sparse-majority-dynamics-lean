import MajorityDynamics.Probability.NeighborhoodTail.GraphCarrier
import MajorityDynamics.Probability.NeighborhoodTail.BipartiteCarrier

/-! Shared constants for all finite carriers. This is the C.2 interface consumed
by actual block graph and bipartite component laws in the next kernel slice. -/
noncomputable section
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodTail
open FixedDegreeSampling
open MajorityDynamics.Combinatorics.DegreeRatios

/-- The same positive constant and common threshold cover both cases and every
finite carrier. In the bipartite case the threshold is on the opposite side. -/
theorem carrier_neighborhood_tail (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ c : ℝ, ∃ n₀ : ℕ, 0 < c ∧ 3 ≤ n₀ ∧
      (∀ (V : Type*) [Fintype V], n₀ ≤ Fintype.card V →
        ∀ p : ℝ, DensityWindow θ T (Fintype.card V) p →
          0 < p ∧ p < 1 ∧ GraphCarrierConclusion c T V p) ∧
      (∀ (L R : Type*) [Fintype L] [Fintype R], n₀ ≤ Fintype.card R →
        ∀ p : ℝ, DensityWindow θ T (Fintype.card R) p →
          0 < p ∧ p < 1 ∧ BipartiteCarrierConclusion c T L R p) := by
  obtain ⟨c, n₀, hc, hn₀, h⟩ := neighborhood_tail θ T hθlo hθhi hT
  refine ⟨c, n₀, hc, hn₀, ?_, ?_⟩
  · intro V _ hn p hp
    have hh := h (Fintype.card V) hn p hp
    exact ⟨hh.1, hh.2.1, graphCarrierConclusion_of_fin V hh.2.2.1⟩
  · intro L R _ _ hn p hp
    have hh := h (Fintype.card R) hn p hp
    exact ⟨hh.1, hh.2.1, bipartiteCarrierConclusion_of_fin hh.2.2.2⟩

end MajorityDynamics.Probability.NeighborhoodTail
