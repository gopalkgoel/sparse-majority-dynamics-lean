import MajorityDynamics.Literature.Graphicality.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
Finite double counting and parity used in the constructive Erdős–Gallai proof.
The proof organization follows Tripathi, Venugopalan and West (2010),
https://dwest.web.illinois.edu/pubs/tripathi.pdf.
-/
namespace MajorityDynamics.Combinatorics.SufficientGraphicality
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem degree_eq_sum_indicator {n : ℕ} (G : SimpleGraph (Fin n)) (i : Fin n) :
    G.degree i = ∑ j, if G.Adj i j then 1 else 0 := by
  simp [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter, Finset.sum_boole]

/-- A clique with independent complement has only cross edges outside its clique. -/
theorem degree_sum_clique_independent_compl {n : ℕ} (G : SimpleGraph (Fin n))
    (P : Finset (Fin n))
    (hclique : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → G.Adj i j)
    (hind : ∀ i ∈ Pᶜ, ∀ j ∈ Pᶜ, ¬ G.Adj i j) :
    (∑ i ∈ P, G.degree i) = P.card * (P.card - 1) + ∑ i ∈ Pᶜ, G.degree i := by
  have hsplit (i : Fin n) : G.degree i =
      (∑ j ∈ P, if G.Adj i j then 1 else 0) +
      ∑ j ∈ Pᶜ, if G.Adj i j then 1 else 0 := by
    rw [Finset.sum_add_sum_compl, degree_eq_sum_indicator]
  have hinside (i : Fin n) (hi : i ∈ P) :
      (∑ j ∈ P, if G.Adj i j then 1 else 0) = P.card - 1 := by
    have heq : P.filter (G.Adj i) = P.erase i := by
      ext j
      simp only [mem_filter, mem_erase]
      constructor
      · rintro ⟨hj, hadj⟩
        exact ⟨hadj.ne.symm, hj⟩
      · rintro ⟨hne, hj⟩
        exact ⟨hj, hclique i hi j hj hne.symm⟩
    simp [Finset.sum_boole, heq, card_erase_of_mem hi]
  have houtside (i : Fin n) (hi : i ∈ Pᶜ) :
      G.degree i = ∑ j ∈ P, if G.Adj i j then 1 else 0 := by
    rw [hsplit]
    have hz : (∑ j ∈ Pᶜ, if G.Adj i j then 1 else 0) = 0 := by
      apply sum_eq_zero
      intro j hj
      simp [hind i hi j hj]
    rw [hz, add_zero]
  calc
    (∑ i ∈ P, G.degree i) =
        ∑ i ∈ P, ((P.card - 1) + ∑ j ∈ Pᶜ, if G.Adj i j then 1 else 0) := by
      apply sum_congr rfl
      intro i hi
      rw [hsplit, hinside i hi]
    _ = P.card * (P.card - 1) + ∑ j ∈ Pᶜ, ∑ i ∈ P, if G.Adj i j then 1 else 0 := by
      rw [sum_add_distrib, sum_comm]
      simp
    _ = P.card * (P.card - 1) + ∑ j ∈ Pᶜ, G.degree j := by
      congr 1
      apply sum_congr rfl
      intro j hj
      rw [houtside j hj]
      apply sum_congr rfl
      intro i hi
      rw [G.adj_comm]

/-- Prefix specialization in the indexing used by the constructive proof. -/
theorem prefix_degree_sum_clique_independent {n : ℕ} (G : SimpleGraph (Fin n))
    (r : Fin n)
    (hclique : ∀ i, i ≤ r → ∀ j, j ≤ r → i ≠ j → G.Adj i j)
    (hind : ∀ i, r < i → ∀ j, r < j → ¬ G.Adj i j) :
    (∑ i ∈ prefixSet n (r.val + 1) (by omega), G.degree i) =
      (r.val + 1) * r.val +
        ∑ i ∈ (prefixSet n (r.val + 1) (by omega))ᶜ, G.degree i := by
  have hc : ∀ i ∈ prefixSet n (r.val + 1) (by omega),
      ∀ j ∈ prefixSet n (r.val + 1) (by omega), i ≠ j → G.Adj i j := by
    intro i hi j hj hne
    simp only [mem_prefixSet] at hi hj
    exact hclique i (by exact Fin.le_iff_val_le_val.mpr (by omega)) j
      (by exact Fin.le_iff_val_le_val.mpr (by omega)) hne
  have hd : ∀ i ∈ (prefixSet n (r.val + 1) (by omega))ᶜ,
      ∀ j ∈ (prefixSet n (r.val + 1) (by omega))ᶜ, ¬ G.Adj i j := by
    intro i hi j hj
    simp only [mem_compl, mem_prefixSet, not_lt] at hi hj
    exact hind i (by exact Fin.lt_def.mpr (by omega)) j
      (by exact Fin.lt_def.mpr (by omega))
  simpa using degree_sum_clique_independent_compl G
    (prefixSet n (r.val + 1) (by omega)) hc hd

/-- Even target total rules out a unique deficiency of one at the first unsaturated index. -/
theorem exists_later_deficient_of_one_deficiency {n : ℕ} (G : SimpleGraph (Fin n))
    (d : Fin n → ℕ) (r : Fin n) (hbound : ∀ i, G.degree i ≤ d i)
    (heven : Even (total d)) (hearly : ∀ i, i < r → G.degree i = d i)
    (hone : G.degree r + 1 = d r) :
    ∃ k, r < k ∧ G.degree k < d k := by
  by_contra h
  have hlate : ∀ k, r < k → G.degree k = d k := by
    intro k hk
    have := hbound k
    have hn : ¬ G.degree k < d k := by
      intro hlt
      exact h ⟨k, hk, hlt⟩
    omega
  have hall : ∀ k, d k = G.degree k + if k = r then 1 else 0 := by
    intro k
    by_cases hk : k = r
    · subst k
      simpa using hone.symm
    · have heq : G.degree k = d k := by
        rcases lt_or_gt_of_ne hk with hkr | hrk
        · exact hearly k hkr
        · exact hlate k hrk
      simp [hk, heq]
  have htotal : total d = (∑ k, G.degree k) + 1 := by
    simp only [total, hall, sum_add_distrib]
    simp
  have hdeg := G.sum_degrees_eq_twice_card_edges
  rcases heven with ⟨a, ha⟩
  omega

end
end MajorityDynamics.Combinatorics.SufficientGraphicality
