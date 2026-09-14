import MajorityDynamics.Combinatorics.SufficientGraphicality.Basic

/-! Sorting preserves the numerical inputs, and graph isomorphisms restore labels. -/
namespace MajorityDynamics.Combinatorics.SufficientGraphicality
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Sort in decreasing order by sorting into the dual order. -/
def descendingOrder {n : ℕ} (d : Fin n → ℕ) : Equiv.Perm (Fin n) :=
  Tuple.sort (α := OrderDual ℕ) d

theorem antitone_descendingOrder {n : ℕ} (d : Fin n → ℕ) :
    Antitone (d ∘ descendingOrder d) :=
  Tuple.monotone_sort (α := OrderDual ℕ) d

@[simp] theorem total_perm {n : ℕ} (d : Fin n → ℕ) (e : Equiv.Perm (Fin n)) :
    total (d ∘ e) = total d := Equiv.sum_comp e d

@[simp] theorem maxDegree_perm {n : ℕ} (d : Fin n → ℕ) (e : Equiv.Perm (Fin n)) :
    maxDegree (d ∘ e) = maxDegree d := by
  apply le_antisymm
  · exact Finset.sup_le fun i _ => le_maxDegree d (e i)
  · apply Finset.sup_le
    intro i _
    simpa using le_maxDegree (d ∘ e) (e.symm i)

/-- Pull the sorted graph back along the inverse permutation. -/
theorem graphical_original_order {n : ℕ} (d : Fin n → ℕ) (e : Equiv.Perm (Fin n))
    (h : Graphical (d ∘ e)) : Graphical d := by
  obtain ⟨G, hG⟩ := h
  refine ⟨G.comap e.symm, fun i => ?_⟩
  have hd := (SimpleGraph.Iso.comap e.symm G).degree_eq i
  convert hd.symm.trans (hG (e.symm i)) using 1 <;> congr 1
  simp

/-- Independent permutations of the two sides preserve the specified bipartition. -/
theorem bipartite_original_order {l n : ℕ} (a : Fin l → ℕ) (b : Fin n → ℕ)
    (e : Equiv.Perm (Fin l)) (f : Equiv.Perm (Fin n))
    (h : Bigraphical (a ∘ e) (b ∘ f)) : Bigraphical a b := by
  obtain ⟨G, hL, hR, ha, hb⟩ := h
  let p := Equiv.sumCongr e.symm f.symm
  refine ⟨G.comap p, ?_, ?_, ?_, ?_⟩
  · intro i j
    simpa [SimpleGraph.comap_adj, p] using hL (e.symm i) (e.symm j)
  · intro i j
    simpa [SimpleGraph.comap_adj, p] using hR (f.symm i) (f.symm j)
  · intro i
    have hd := (SimpleGraph.Iso.comap p G).degree_eq (.inl i)
    convert hd.symm.trans (ha (e.symm i)) using 1 <;> congr 1
    simp
  · intro j
    have hd := (SimpleGraph.Iso.comap p G).degree_eq (.inr j)
    convert hd.symm.trans (hb (f.symm j)) using 1 <;> congr 1
    simp

/-- All-zero sequences, including the empty sequence, have the empty graph. -/
theorem graphical_zero {n : ℕ} (d : Fin n → ℕ) (h : ∀ i, d i = 0) : Graphical d := by
  exact ⟨⊥, by simp [h]⟩

theorem bipartite_zero {l n : ℕ} (a : Fin l → ℕ) (b : Fin n → ℕ)
    (ha : ∀ i, a i = 0) (hb : ∀ j, b j = 0) : Bigraphical a b := by
  refine ⟨⊥, ?_, ?_, ?_, ?_⟩ <;> simp [ha, hb]

theorem eq_zero_of_total_zero {n : ℕ} (d : Fin n → ℕ) (h : total d = 0) :
    ∀ i, d i = 0 := by
  simpa [total] using (sum_eq_zero_iff_of_nonneg (fun i _ => Nat.zero_le (d i))).mp h

end
end MajorityDynamics.Combinatorics.SufficientGraphicality
