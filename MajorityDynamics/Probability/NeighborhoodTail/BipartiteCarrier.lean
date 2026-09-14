import MajorityDynamics.Probability.NeighborhoodTail.Main
import MajorityDynamics.Probability.NeighborhoodTail.BipartiteRelabel

/-! The original-input bipartite point tail on arbitrary finite carriers. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodTail
open FixedDegreeSampling NeighborhoodBulk
open MajorityDynamics.Combinatorics.DegreeRatios

/-- Literal original hypotheses with the right population size and two distinct degree scales. -/
def BipartiteCarrierConclusion (c T : ℝ) (L R : Type*) [Fintype L] [Fintype R]
    (p : ℝ) : Prop :=
  (Fintype.card R : ℝ) / T ≤ Fintype.card L →
  (Fintype.card L : ℝ) ≤ T * Fintype.card R →
  ∀ (m : ℤ) (a : L → ℕ) (b : R → ℕ),
    (∀ i, a i ≤ Fintype.card R) → (∀ j, b j ≤ Fintype.card L) →
    (∑ i, (a i : ℤ)) = m → (∑ j, (b j : ℤ)) = m →
    |(m : ℝ) - p * Fintype.card L * Fintype.card R| ≤
      T * (Fintype.card R : ℝ) ^ 2 * p / Real.sqrt (p * Fintype.card R) →
    (∀ i, |((a i : ℝ) - p * Fintype.card R) / Real.sqrt (p * Fintype.card R)| ≤
      Real.log (Fintype.card R)) →
    (∀ j, |((b j : ℝ) - p * Fintype.card L) / Real.sqrt (p * Fintype.card L)| ≤
      Real.log (Fintype.card R)) →
    (bipartiteFamily a b).Nonempty ∧
      ∀ (v : L) (S : Finset R),
        (Fintype.card R : ℝ) / T ≤ S.card →
        (Fintype.card R : ℝ) / T ≤ (Fintype.card R : ℝ) - S.card →
        ∀ t : ℤ, 0 ≤ t → t ≤ a v →
          Real.log (Fintype.card R : ℝ) ^ 100 ≤
            |((t : ℝ) - p * S.card) / Real.sqrt (p * S.card)| →
          (bipartiteFixedDegreeLaw a b).real
            {E | ((leftNeighbors E v ∩ S).card : ℤ) = t} ≤
            Real.exp (-c * (((t : ℝ) - p * S.card) / Real.sqrt (p * S.card)) ^ 2)

/-- The finite-carrier endpoint uses only the corresponding checked `Fin` endpoint. -/
theorem bipartiteCarrierConclusion_of_fin {c T p : ℝ} {L R : Type*}
    [Fintype L] [Fintype R]
    (h : BipartiteConclusion c T (Fintype.card R) p) :
    BipartiteCarrierConclusion c T L R p := by
  intro hsizeLo hsizeHi m a b hacap hbcap haSum hbSum hcount hadev hbdev
  let ell : ℤ := Fintype.card L
  let e : L ≃ Fin ell.toNat := Fintype.equivFin L
  let f : R ≃ Fin (Fintype.card R) := Fintype.equivFin R
  let a' : Fin ell.toNat → ℤ := fun i => a (e.symm i)
  let b' : Fin (Fintype.card R) → ℤ := fun j => b (f.symm j)
  have hinput : BipartiteInput T (Fintype.card R) p ell m a' b' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [ell] using hsizeLo
    · simpa [ell] using hsizeHi
    · intro i
      dsimp [a']
      exact ⟨by positivity, by exact_mod_cast hacap (e.symm i)⟩
    · intro j
      dsimp [b', ell]
      exact ⟨by positivity, by exact_mod_cast hbcap (f.symm j)⟩
    · calc
        (∑ i, a' i) = ∑ i, (a i : ℤ) := by
          simpa only [a'] using e.symm.sum_comp (fun i => (a i : ℤ))
        _ = m := haSum
    · calc
        (∑ j, b' j) = ∑ j, (b j : ℤ) := by
          simpa only [b'] using f.symm.sum_comp (fun j => (b j : ℤ))
        _ = m := hbSum
    · simpa [ell] using hcount
    · intro i
      simpa only [a', standardizedDegree, Int.cast_natCast] using hadev (e.symm i)
    · intro j
      simpa [b', ell, standardizedDegree] using hbdev (f.symm j)
  obtain ⟨hne, htail⟩ := h ell m a' b' hinput
  refine ⟨?_, ?_⟩
  · obtain ⟨E, hE⟩ := hne
    refine ⟨crossRelabel e.symm f.symm E, ?_⟩
    have hh := (bipartite_relabel_mem e.symm f.symm
      (fun i => (a' i).toNat) (fun j => (b' j).toNat) E).mpr hE
    simpa [a', b'] using hh
  · intro v S hS hSc t ht htd hτ
    have hx := htail (e v) (S.map f.toEmbedding)
      (by simpa only [Finset.card_map] using hS)
      (by simpa only [Finset.card_map] using hSc) t ht
      (by simpa [a'] using htd)
      (by simpa only [Finset.card_map] using hτ)
    rw [bipartite_neighborhood_relabel e f a b v S t]
    simpa [a', b'] using hx

/-- One positive constant and one threshold precede both arbitrary finite carriers. -/
theorem bipartite_carrier_neighborhood_tail (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ c : ℝ, ∃ n₀ : ℕ, 0 < c ∧ 3 ≤ n₀ ∧
      ∀ (L R : Type*) [Fintype L] [Fintype R], n₀ ≤ Fintype.card R →
        ∀ p : ℝ, DensityWindow θ T (Fintype.card R) p →
          0 < p ∧ p < 1 ∧ BipartiteCarrierConclusion c T L R p := by
  obtain ⟨c, n₀, hc, hn₀, h⟩ := bipartite_neighborhood_tail θ T hθlo hθhi hT
  refine ⟨c, n₀, hc, hn₀, ?_⟩
  intro L R _ _ hn p hw
  have hh := h (Fintype.card R) hn p hw
  exact ⟨hh.1, hh.2.1, bipartiteCarrierConclusion_of_fin hh.2.2⟩

end MajorityDynamics.Probability.NeighborhoodTail
