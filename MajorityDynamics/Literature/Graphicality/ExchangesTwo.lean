import MajorityDynamics.Literature.Graphicality.Edits

/-!
Two edge exchanges used in the constructive Erdős–Gallai argument of
Tripathi, Venugopalan and West (2010),
https://dwest.web.illinois.edu/pubs/tripathi.pdf.
These are direct finite graph constructions; in the second exchange the two
external neighbors are allowed to coincide.
-/
namespace MajorityDynamics.Combinatorics.SufficientGraphicality
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Replace `i—u` by `r—u` and `i—k`, increasing only the degrees of `r` and `k`. -/
theorem exchange_two_edges (G : SimpleGraph V) (r i u k : V)
    (hiu : G.Adj i u) (hru : ¬ G.Adj r u) (hik : ¬ G.Adj i k)
    (hri : r ≠ i) (hrk : r ≠ k) (hur : u ≠ r) (hikne : i ≠ k) :
    ∃ H : SimpleGraph V,
      (∀ v, H.degree v = G.degree v + (if v = r then 1 else 0) +
        (if v = k then 1 else 0)) ∧
      (∀ v z, H.Adj v z → G.Adj v z ∨ v = r ∨ z = r ∨ v = i ∨ z = i) := by
  let G₁ := removeEdge G i u
  have hr₁ : ¬ G₁.Adj r u := by
    intro h
    exact hru h.1
  let G₂ := addEdge G₁ r u hur.symm
  have hi₂ : ¬ G₂.Adj i k := by
    dsimp [G₂, G₁]
    simp only [addEdge_adj, removeEdge_adj]
    grind
  let H := addEdge G₂ i k hikne
  refine ⟨H, ?_, ?_⟩
  · intro v
    have h₁ := degree_removeEdge G i u hiu v
    have h₂ := degree_addEdge G₁ r u hur.symm hr₁ v
    have h₃ := degree_addEdge G₂ i k hikne hi₂ v
    change G₁.degree v + _ + _ = G.degree v at h₁
    change G₂.degree v = _ at h₂
    change H.degree v = _ at h₃
    omega
  · intro v z h
    dsimp [H, G₂, G₁, addEdge, removeEdge] at h
    tauto

/-- Replace `i—u,j—w` by `i—j,r—u`, transferring one unit from `w` to `r`.
The vertices `u` and `w` need not be distinct. -/
theorem exchange_three_edges (G : SimpleGraph V) (r i j u w : V)
    (hiu : G.Adj i u) (hjw : G.Adj j w)
    (hij : ¬ G.Adj i j) (hru : ¬ G.Adj r u)
    (hri : r ≠ i) (hrj : r ≠ j) (hru_ne : r ≠ u)
    (hij_ne : i ≠ j) (hju : j ≠ u) :
    ∃ H : SimpleGraph V,
      (∀ v, H.degree v + (if v = w then 1 else 0) =
        G.degree v + (if v = r then 1 else 0)) ∧
      (∀ v z, H.Adj v z →
        G.Adj v z ∨ v = r ∨ z = r ∨ v = i ∨ z = i ∨ v = j ∨ z = j) := by
  let G₁ := removeEdge G i u
  have hj₁ : G₁.Adj j w := by
    dsimp [G₁]
    simp only [removeEdge_adj]
    grind
  let G₂ := removeEdge G₁ j w
  have hij₂ : ¬ G₂.Adj i j := by
    intro h
    exact hij h.1.1
  let G₃ := addEdge G₂ i j hij_ne
  have hru₃ : ¬ G₃.Adj r u := by
    dsimp [G₃, G₂, G₁]
    simp only [addEdge_adj, removeEdge_adj]
    grind
  let H := addEdge G₃ r u hru_ne
  refine ⟨H, ?_, ?_⟩
  · intro v
    have h₁ := degree_removeEdge G i u hiu v
    have h₂ := degree_removeEdge G₁ j w hj₁ v
    have h₃ := degree_addEdge G₂ i j hij_ne hij₂ v
    have h₄ := degree_addEdge G₃ r u hru_ne hru₃ v
    change G₁.degree v + _ + _ = G.degree v at h₁
    change G₂.degree v + _ + _ = G₁.degree v at h₂
    change G₃.degree v = _ at h₃
    change H.degree v = _ at h₄
    omega
  · intro v z h
    dsimp [H, G₃, G₂, G₁, addEdge, removeEdge] at h
    tauto

end
end MajorityDynamics.Combinatorics.SufficientGraphicality
