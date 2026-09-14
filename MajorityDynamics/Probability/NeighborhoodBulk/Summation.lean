import MajorityDynamics.Probability.NeighborhoodBulk.Partition
import MajorityDynamics.Probability.NeighborhoodBulk.Adapters

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodBulk
open FixedDegreeSampling

theorem subset_comparison_sum {V : Type*} [Fintype V] (A B : Finset V) (k l : ℕ)
    (c : ℝ) (f : Finset V → ℝ) :
    ((A.card.choose k : ℝ) * (B.card.choose l : ℝ) / c) * subsetExpectation A B k l f =
      ∑ R₁ ∈ A.powersetCard k, ∑ R₂ ∈ B.powersetCard l, f (R₁ ∪ R₂) / c := by
  by_cases hk : k ≤ A.card
  · by_cases hl : l ≤ B.card
    · rw [subsetExpectation_eq_average]
      simp_rw [← Finset.sum_div]
      have hA : (A.card.choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
      have hB : (B.card.choose l : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hl).ne'
      field_simp
    · have hl' : B.card < l := by omega
      simp [Finset.powersetCard_eq_empty.mpr hl', Nat.choose_eq_zero_of_lt hl']
  · have hk' : A.card < k := by omega
    simp [Finset.powersetCard_eq_empty.mpr hk', Nat.choose_eq_zero_of_lt hk']

theorem graph_comparison_sum {n : ℕ} (p : ℝ) (d : Fin n → ℤ) (v : Fin n)
    (S : Finset (Fin n)) (t : ℤ) :
    graphComparison p d v S t =
      ∑ R₁ ∈ (S.erase v).powersetCard t.toNat,
        ∑ R₂ ∈ (Finset.univ \ insert v S).powersetCard (d v - t).toNat,
          Real.exp (graphWeight p d v (R₁ ∪ R₂)) / ((n - 1).choose (d v).toNat : ℝ) := by
  unfold graphComparison
  rw [← erase_card, ← complement_insert_card]
  convert subset_comparison_sum (S.erase v) (Finset.univ \ insert v S)
    t.toNat (d v - t).toNat ((n - 1).choose (d v).toNat : ℝ)
    (fun R => Real.exp (graphWeight p d v R)) using 1
  congr!

theorem bipartite_comparison_sum {n : ℕ} (p : ℝ) (ell : ℤ) (b : Fin n → ℤ)
    (dv : ℤ) (S : Finset (Fin n)) (t : ℤ) :
    bipartiteComparison p ell b dv S t =
      ∑ R₁ ∈ S.powersetCard t.toNat,
        ∑ R₂ ∈ (Finset.univ \ S).powersetCard (dv - t).toNat,
          Real.exp (bipartiteWeight p ell b (R₁ ∪ R₂)) / (n.choose dv.toNat : ℝ) := by
  have hc : (Finset.univ \ S).card = n - S.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]; simp
  unfold bipartiteComparison
  rw [← hc]
  convert subset_comparison_sum S (Finset.univ \ S) t.toNat (dv - t).toNat
    (n.choose dv.toNat : ℝ) (fun R => Real.exp (bipartiteWeight p ell b R)) using 1
  congr!

theorem graph_partition_disjoint {n : ℕ} (v : Fin n) (S : Finset (Fin n)) :
    Disjoint (S.erase v) (Finset.univ \ insert v S) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_insert_of_mem (Finset.mem_erase.mp hi).2)

theorem graph_partition_union {n : ℕ} (v : Fin n) (S : Finset (Fin n)) :
    S.erase v ∪ (Finset.univ \ insert v S) = Finset.univ.erase v := by
  ext i
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
    Finset.mem_insert, true_and, and_true]
  tauto

theorem graph_event_sum {n : ℕ} (d : Fin n → ℤ) (v : Fin n) (S : Finset (Fin n))
    (t : ℤ) (ht : 0 ≤ t) (htd : t ≤ d v) :
    (fixedDegreeLaw (fun i => (d i).toNat)).real
      {G | ((G.neighborFinset v ∩ S).card : ℤ) = t} =
      ∑ R₁ ∈ (S.erase v).powersetCard t.toNat,
        ∑ R₂ ∈ (Finset.univ \ insert v S).powersetCard (d v - t).toNat,
          (fixedDegreeLaw (fun i => (d i).toNat)).real {G | G.neighborFinset v = R₁ ∪ R₂} := by
  have hp := uniform_partition_sum (graphFamily (fun i => (d i).toNat))
    (fun G => G.neighborFinset v) (S.erase v) (Finset.univ \ insert v S)
    t.toNat (d v - t).toNat (graph_partition_disjoint v S) (by
      intro G hG
      constructor
      · intro i hi
        have hiv : i ≠ v := by intro he; subst i; simp at hi
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
          Finset.mem_insert, true_and]
        tauto
      · have hcard : (G.neighborFinset v).card = (d v).toNat := hG v
        omega)
  convert hp using 1
  · apply uniform_real_congr
    intro G _
    have he : G.neighborFinset v ∩ S.erase v = G.neighborFinset v ∩ S := by
      ext i
      by_cases hiv : i = v
      · subst i; simp
      · simp [hiv]
    have hiff : ((G.neighborFinset v ∩ S).card : ℤ) = t ↔
        (G.neighborFinset v ∩ S.erase v).card = t.toNat := by rw [he]; omega
    simp only [Set.mem_ofPred_eq]
    convert hiff using 1; congr!
  · congr!

theorem bipartite_event_sum {ell : ℤ} {n : ℕ} (a : Fin ell.toNat → ℤ) (b : Fin n → ℤ)
    (v : Fin ell.toNat) (S : Finset (Fin n)) (t : ℤ) (ht : 0 ≤ t) (htd : t ≤ a v) :
    (bipartiteFixedDegreeLaw (fun i => (a i).toNat) (fun j => (b j).toNat)).real
      {E | ((leftNeighbors E v ∩ S).card : ℤ) = t} =
      ∑ R₁ ∈ S.powersetCard t.toNat,
        ∑ R₂ ∈ (Finset.univ \ S).powersetCard (a v - t).toNat,
          (bipartiteFixedDegreeLaw (fun i => (a i).toNat) (fun j => (b j).toNat)).real
            {E | leftNeighbors E v = R₁ ∪ R₂} := by
  have hp := uniform_partition_sum (bipartiteFamily (fun i => (a i).toNat) (fun j => (b j).toNat))
    (fun E => leftNeighbors E v) S (Finset.univ \ S) t.toNat (a v - t).toNat
    (by apply Finset.disjoint_left.mpr; intro i hi hj; exact (Finset.mem_sdiff.mp hj).2 hi) (by
      intro E hE
      constructor
      · intro i _
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact em _
      · have hcard : (leftNeighbors E v).card = (a v).toNat := hE.1 v
        omega)
  convert hp using 1
  · apply uniform_real_congr
    intro E _
    have hiff : ((leftNeighbors E v ∩ S).card : ℤ) = t ↔
        (leftNeighbors E v ∩ S).card = t.toNat := by omega
    simp only [Set.mem_ofPred_eq]
    convert hiff using 1; congr!
  · congr!

theorem multiplicative_sum {I J : Type*} (s : Finset I) (t : Finset J) (C : ℝ) (n : ℕ)
    (P Q : I → J → ℝ) (h : ∀ i ∈ s, ∀ j ∈ t, MultiplicativeBound C n (P i j) (Q i j)) :
    MultiplicativeBound C n (∑ i ∈ s, ∑ j ∈ t, P i j) (∑ i ∈ s, ∑ j ∈ t, Q i j) := by
  constructor
  · simp_rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => (h i hi j hj).1))
  · simp_rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => (h i hi j hj).2))

end MajorityDynamics.Probability.NeighborhoodBulk
