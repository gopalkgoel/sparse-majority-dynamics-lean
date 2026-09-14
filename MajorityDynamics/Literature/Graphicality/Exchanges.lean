import MajorityDynamics.Literature.Graphicality.Edits

/-!
# Degree-preserving exchange packages

The augmentations implement the elementary exchanges in the constructive proof
of A. Tripathi, S. Venugopalan and D. B. West, “A short constructive proof of the
Erdős–Gallai characterization of graphic lists” (preprint September 6, 2009),
<https://dwest.web.illinois.edu/pubs/tripathi.pdf>, Theorem 1, Case 1.
These are original Lean proofs of the cited mathematical exchanges.
-/
namespace MajorityDynamics.Combinatorics.SufficientGraphicality
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Replace `i-u` by `r-u` and `r-i`, increasing only the degree of `r`. -/
theorem exists_double_augmentation (G : SimpleGraph V) {r i u : V}
    (hri : r ≠ i) (hnri : ¬ G.Adj r i) (hiu : G.Adj i u)
    (hnru : ¬ G.Adj r u) (hur : u ≠ r) :
    ∃ H : SimpleGraph V,
      (∀ v, H.degree v = G.degree v + (if v = r then 2 else 0)) ∧
      (∀ v w, H.Adj v w → G.Adj v w ∨ v = r ∨ w = r) ∧
      (∀ v w, G.Adj v w → v ≠ i → w ≠ i → H.Adj v w) := by
  let D := removeEdge G i u
  let A := addEdge D r u hur.symm
  let H := addEdge A r i hri
  have hiu_ne : i ≠ u := hiu.ne
  have hDru : ¬ D.Adj r u := by simp [D, hnru]
  have hAri : ¬ A.Adj r i := by simp [A, D, hnri, hiu_ne, hur.symm]
  refine ⟨H, ?_, ?_, ?_⟩
  · intro v
    have hD := degree_removeEdge G i u hiu v
    have hA := degree_addEdge D r u hur.symm hDru v
    have hH := degree_addEdge A r i hri hAri v
    change H.degree v = G.degree v + (if v = r then 2 else 0)
    change D.degree v + _ + _ = G.degree v at hD
    change A.degree v = D.degree v + _ + _ at hA
    change H.degree v = A.degree v + _ + _ at hH
    split_ifs at * <;> omega
  · intro v w hvw
    simp only [H, A, D, addEdge_adj, removeEdge_adj] at hvw
    tauto
  · intro v w hvw hvi hwi
    simp [H, A, D, hvw, hvi, hwi]

/-- Add one unit of degree at `r` and remove one at `k` by a two-edge exchange. -/
theorem exists_single_augmentation (G : SimpleGraph V) {r i u k : V}
    (hri : r ≠ i) (hnri : ¬ G.Adj r i) (hiu : G.Adj i u)
    (hnru : ¬ G.Adj r u) (hur : u ≠ r) (hrk : G.Adj r k)
    (hki : k ≠ i) :
    ∃ H : SimpleGraph V,
      (∀ v, H.degree v + (if v = k then 1 else 0) =
        G.degree v + (if v = r then 1 else 0)) ∧
      (∀ v w, H.Adj v w → G.Adj v w ∨ v = r ∨ w = r) := by
  obtain ⟨A, hdeg, hadj, hpres⟩ :=
    exists_double_augmentation G hri hnri hiu hnru hur
  have hArk := hpres r k hrk hri hki
  refine ⟨removeEdge A r k, ?_, ?_⟩
  · intro v
    have hd := degree_removeEdge A r k hArk v
    have ha := hdeg v
    have hrk_ne : r ≠ k := hrk.ne
    split_ifs at * <;> omega
  · intro v w hvw
    exact hadj v w hvw.1

end
end MajorityDynamics.Combinatorics.SufficientGraphicality
