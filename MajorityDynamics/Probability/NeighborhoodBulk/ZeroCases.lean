import MajorityDynamics.Probability.NeighborhoodBulk.Basic

/-! Impossible subset capacities, including the graph's self-exclusion. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodBulk
open FixedDegreeSampling

theorem erase_card {n : ℕ} (S : Finset (Fin n)) (v : Fin n) :
    (S.erase v).card = S.card - if v ∈ S then 1 else 0 := by
  by_cases h : v ∈ S <;> simp [h]

theorem complement_insert_card {n : ℕ} (S : Finset (Fin n)) (v : Fin n) :
    (Finset.univ \ insert v S).card = n - S.card - if v ∉ S then 1 else 0 := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  by_cases h : v ∈ S <;> simp [h, Nat.sub_sub]

theorem graphComparison_zero {n : ℕ} (p : ℝ) (d : Fin n → ℤ)
    (v : Fin n) (S : Finset (Fin n)) (t : ℤ)
    (h : (S.erase v).card < t.toNat ∨
      (Finset.univ \ insert v S).card < (d v - t).toNat) :
    graphComparison p d v S t = 0 := by
  rcases h with h | h
  · rw [erase_card] at h
    rw [graphComparison, Nat.choose_eq_zero_of_lt h]
    simp
  · rw [complement_insert_card] at h
    rw [graphComparison, Nat.choose_eq_zero_of_lt h]
    simp

theorem bipartiteComparison_zero {n : ℕ} (p : ℝ) (ell : ℤ) (b : Fin n → ℤ)
    (dv : ℤ) (S : Finset (Fin n)) (t : ℤ)
    (h : S.card < t.toNat ∨ n - S.card < (dv - t).toNat) :
    bipartiteComparison p ell b dv S t = 0 := by
  rcases h with h | h <;>
    simp [bipartiteComparison, Nat.choose_eq_zero_of_lt h]

private theorem graph_capacities {n : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n) (S : Finset (Fin n)) :
    (G.neighborFinset v ∩ S).card ≤ (S.erase v).card ∧
      (G.neighborFinset v \ S).card ≤ (Finset.univ \ insert v S).card := by
  constructor
  · apply Finset.card_le_card
    intro i hi
    obtain ⟨hiG, hiS⟩ := Finset.mem_inter.mp hi
    apply Finset.mem_erase.mpr
    refine ⟨?_, hiS⟩
    intro hiv
    subst i
    simp at hiG
  · apply Finset.card_le_card
    intro i hi
    obtain ⟨hiG, hiS⟩ := Finset.mem_sdiff.mp hi
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [Finset.mem_insert]
    rintro (hiv | hiS')
    · subst i
      simp at hiG
    · exact hiS hiS'

theorem graph_event_zero {n : ℕ} (d : Fin n → ℤ) (v : Fin n)
    (S : Finset (Fin n)) (t : ℤ) (ht : 0 ≤ t) (_htd : t ≤ d v)
    (h : (S.erase v).card < t.toNat ∨
      (Finset.univ \ insert v S).card < (d v - t).toNat) :
    fixedDegreeLaw (fun i => (d i).toNat)
      {G | ((G.neighborFinset v ∩ S).card : ℤ) = t} = 0 := by
  apply (uniformOn_eq_zero_iff (Set.toFinite _)).mpr
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro G hG
  have hd : (G.neighborFinset v).card = (d v).toNat := hG.1 v
  have hi : ((G.neighborFinset v ∩ S).card : ℤ) = t := hG.2
  obtain ⟨hc₁, hc₂⟩ := graph_capacities G v S
  have he := Finset.card_sdiff_add_card_inter (G.neighborFinset v) S
  omega

theorem bipartite_event_zero {ell : ℤ} {n : ℕ}
    (a : Fin ell.toNat → ℤ) (b : Fin n → ℤ) (v : Fin ell.toNat)
    (S : Finset (Fin n)) (t : ℤ) (ht : 0 ≤ t) (_htd : t ≤ a v)
    (h : S.card < t.toNat ∨ n - S.card < (a v - t).toNat) :
    bipartiteFixedDegreeLaw (fun i => (a i).toNat) (fun j => (b j).toNat)
      {E | ((leftNeighbors E v ∩ S).card : ℤ) = t} = 0 := by
  apply (uniformOn_eq_zero_iff (Set.toFinite _)).mpr
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro E hE
  have hd : (leftNeighbors E v).card = (a v).toNat := hE.1.1 v
  have hi : ((leftNeighbors E v ∩ S).card : ℤ) = t := hE.2
  have hc₁ := Finset.card_le_card (Finset.inter_subset_right (s₁ := leftNeighbors E v) (s₂ := S))
  have hc₂ : (leftNeighbors E v \ S).card ≤ n - S.card := by
    calc
      _ ≤ (Finset.univ \ S).card :=
        Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.subset_univ _) le_rfl)
      _ = _ := by rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]; simp
  have he := Finset.card_sdiff_add_card_inter (leftNeighbors E v) S
  omega

end MajorityDynamics.Probability.NeighborhoodBulk
