import MajorityDynamics.Probability.NeighborhoodTail.Main
import MajorityDynamics.Probability.NeighborhoodTail.GraphRelabel

/-! The graph case of C.2 on an arbitrary finite carrier, for natural degrees.
The original degree windows imply realization; callers need no law-transport premise. -/
noncomputable section
open MeasureTheory
open scoped Classical BigOperators
namespace MajorityDynamics.Probability.NeighborhoodTail
open FixedDegreeSampling NeighborhoodBulk
open MajorityDynamics.Combinatorics.DegreeRatios

def GraphCarrierConclusion (c T : ℝ) (V : Type*) [Fintype V] (p : ℝ) : Prop :=
  ∀ (m : ℤ) (d : V → ℕ),
    (∀ v, (d v : ℤ) ≤ (Fintype.card V : ℤ) - 1) →
    (∑ v, (d v : ℤ)) = 2 * m →
    |(m : ℝ) - p * Fintype.card V * ((Fintype.card V : ℝ) - 1) / 2| ≤
      T * (Fintype.card V : ℝ) ^ 2 * p / Real.sqrt (p * Fintype.card V) →
    (∀ v, |((d v : ℝ) - p * Fintype.card V) / Real.sqrt (p * Fintype.card V)| ≤
      Real.log (Fintype.card V)) →
    (graphFamily d).Nonempty ∧
      ∀ (v : V) (S : Finset V),
        (Fintype.card V : ℝ) / T ≤ S.card →
        (Fintype.card V : ℝ) / T ≤ (Fintype.card V : ℝ) - S.card →
        ∀ t : ℤ, 0 ≤ t → t ≤ (d v : ℤ) →
          Real.log (Fintype.card V : ℝ) ^ 100 ≤
            |((t : ℝ) - p * S.card) / Real.sqrt (p * S.card)| →
          (fixedDegreeLaw d).real {G | ((G.neighborFinset v ∩ S).card : ℤ) = t} ≤
            Real.exp (-c * (((t : ℝ) - p * S.card) / Real.sqrt (p * S.card)) ^ 2)

/-- The finite-carrier adapter is purely exact: its only input is the Fin conclusion. -/
theorem graphCarrierConclusion_of_fin {c T p : ℝ} (V : Type*) [Fintype V]
    (h : GraphConclusion c T (Fintype.card V) p) : GraphCarrierConclusion c T V p := by
  intro m d hcap hsum hm hd
  let e := Fintype.equivFin V
  let df : Fin (Fintype.card V) → ℤ := fun i => (d (e.symm i) : ℤ)
  have hdf : GraphInput T (Fintype.card V) p m df := by
    refine ⟨fun i => ⟨Int.natCast_nonneg _, hcap _⟩, ?_, hm, ?_⟩
    · exact (e.symm.sum_comp (fun v => (d v : ℤ))).trans hsum
    · intro i
      simpa only [standardizedDegree, df, Int.cast_natCast] using hd (e.symm i)
  obtain ⟨hne, he⟩ := h m df hdf
  refine ⟨?_, ?_⟩
  · obtain ⟨G, hG⟩ := hne
    refine ⟨e.symm.simpleGraph G, ?_⟩
    have hG' : G ∈ graphFamily (fun i => d (e.symm i)) := by
      simpa only [df, Int.toNat_natCast] using hG
    have hr := (graph_relabel_mem e.symm (fun i => d (e.symm i)) G).mpr hG'
    simpa only [Equiv.symm_symm, Equiv.symm_apply_apply] using hr
  · intro v S hS hSc t ht htd hτ
    have hf := he (e v) (S.map e.toEmbedding)
      (by simpa only [Finset.card_map] using hS)
      (by simpa only [Finset.card_map] using hSc) t ht
      (by simpa only [df, Equiv.symm_apply_apply] using htd)
      (by simpa only [Finset.card_map] using hτ)
    rw [graph_neighborhood_relabel e d v S t]
    simp only [df, Int.toNat_natCast, Finset.card_map] at hf
    convert hf using 1
    congr 1
    ext G
    simp only [Set.mem_ofPred_eq]
    apply iff_of_eq
    congr 3
    ext i
    simp only [Finset.mem_inter]

/-- One positive constant and one threshold work for every finite vertex carrier. -/
theorem graph_carrier_neighborhood_tail (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ c : ℝ, ∃ n₀ : ℕ, 0 < c ∧ 3 ≤ n₀ ∧
      ∀ (V : Type*) [Fintype V], n₀ ≤ Fintype.card V →
        ∀ p : ℝ, DensityWindow θ T (Fintype.card V) p →
          0 < p ∧ p < 1 ∧ GraphCarrierConclusion c T V p := by
  obtain ⟨c, n₀, hc, hn₀, h⟩ := graph_neighborhood_tail θ T hθlo hθhi hT
  refine ⟨c, n₀, hc, hn₀, ?_⟩
  intro V _ hn p hp
  have hh := h (Fintype.card V) hn p hp
  exact ⟨hh.1, hh.2.1, graphCarrierConclusion_of_fin V hh.2.2⟩

end MajorityDynamics.Probability.NeighborhoodTail
