import MajorityDynamics.Combinatorics.SufficientGraphicality.Main

/-! Exact targets, independently expanded acceptance contracts, representation
bridges, and minimal transitive axiom guards. -/
namespace MajorityDynamics.Combinatorics.SufficientGraphicality
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

example : GraphicalSufficientTheorem := graphical_sufficient
example : BipartiteGraphicalSufficientTheorem := bipartite_graphical_sufficient
example : IntegerGraphicalSufficientTheorem := graphical_sufficient_integer
example : IntegerBipartiteGraphicalSufficientTheorem := bipartite_graphical_sufficient_integer
example : ErdosGallaiCriterion → GraphicalSufficientTheorem :=
  graphical_sufficient_of_erdos_gallai
example : GaleRyserCriterion → BipartiteGraphicalSufficientTheorem :=
  bipartite_graphical_sufficient_of_gale_ryser

example : ∀ (n : ℕ) (d : Fin n → ℕ), Even (∑ i, d i) →
    univ.sup d * (univ.sup d + 1) ≤ ∑ i, d i →
    ∃ G : SimpleGraph (Fin n), ∀ i, G.degree i = d i := graphical_sufficient

example : ∀ (l n : ℕ) (a : Fin l → ℕ) (b : Fin n → ℕ),
    (∑ i, a i) = ∑ j, b j → univ.sup a * univ.sup b ≤ ∑ i, a i →
    ∃ G : SimpleGraph (Fin l ⊕ Fin n),
      (∀ i j, ¬ G.Adj (.inl i) (.inl j)) ∧
      (∀ i j, ¬ G.Adj (.inr i) (.inr j)) ∧
      (∀ i, G.degree (.inl i) = a i) ∧
      (∀ j, G.degree (.inr j) = b j) := bipartite_graphical_sufficient

example : ∀ (n : ℕ) (d : Fin n → ℤ), (∀ i, 0 ≤ d i) → Even (∑ i, d i) →
    (insert 0 (univ.image d)).max' (by simp) *
      ((insert 0 (univ.image d)).max' (by simp) + 1) ≤ ∑ i, d i →
    ∃ G : SimpleGraph (Fin n), ∀ i, (G.degree i : ℤ) = d i :=
  graphical_sufficient_integer

example : ∀ (l n : ℕ) (a : Fin l → ℤ) (b : Fin n → ℤ),
    (∀ i, 0 ≤ a i) → (∀ j, 0 ≤ b j) → (∑ i, a i) = ∑ j, b j →
    (insert 0 (univ.image a)).max' (by simp) *
      (insert 0 (univ.image b)).max' (by simp) ≤ ∑ i, a i →
    ∃ G : SimpleGraph (Fin l ⊕ Fin n),
      (∀ i j, ¬ G.Adj (.inl i) (.inl j)) ∧
      (∀ i j, ¬ G.Adj (.inr i) (.inr j)) ∧
      (∀ i, (G.degree (.inl i) : ℤ) = a i) ∧
      (∀ j, (G.degree (.inr j) : ℤ) = b j) :=
  bipartite_graphical_sufficient_integer

example {n : ℕ} (d : Fin n → ℕ) (e : Equiv.Perm (Fin n))
    (h : ∃ G : SimpleGraph (Fin n), ∀ i, G.degree i = d (e i)) :
    ∃ G : SimpleGraph (Fin n), ∀ i, G.degree i = d i :=
  graphical_original_order d e h

example {l n : ℕ} (a : Fin l → ℕ) (b : Fin n → ℕ)
    (e : Equiv.Perm (Fin l)) (f : Equiv.Perm (Fin n))
    (h : ∃ G : SimpleGraph (Fin l ⊕ Fin n),
      (∀ i j, ¬ G.Adj (.inl i) (.inl j)) ∧
      (∀ i j, ¬ G.Adj (.inr i) (.inr j)) ∧
      (∀ i, G.degree (.inl i) = a (e i)) ∧ (∀ j, G.degree (.inr j) = b (f j))) :
    ∃ G : SimpleGraph (Fin l ⊕ Fin n),
      (∀ i j, ¬ G.Adj (.inl i) (.inl j)) ∧
      (∀ i j, ¬ G.Adj (.inr i) (.inr j)) ∧
      (∀ i, G.degree (.inl i) = a i) ∧ (∀ j, G.degree (.inr j) = b j) :=
  bipartite_original_order a b e f h

example {n : ℕ} (d : Fin n → ℤ) (hd : ∀ i, 0 ≤ d i) :
    (maxDegree (fun i => (d i).toNat) : ℤ) = integerMax d := maxDegree_toNat d hd
example {n : ℕ} (d : Fin n → ℤ) (hd : ∀ i, 0 ≤ d i) :
    (total (fun i => (d i).toNat) : ℤ) = ∑ i, d i := total_toNat d hd

-- Empty sets and sharp equality are part of the universal contracts.
example : Graphical (fun i : Fin 0 => i.elim0) :=
  graphical_zero _ (fun i => i.elim0)
example (l n : ℕ) : Bigraphical (fun _ : Fin l => 0) (fun _ : Fin n => 0) :=
  bipartite_zero _ _ (fun _ => rfl) (fun _ => rfl)
example : Graphical (fun _ : Fin 2 => 1) := by
  apply graphical_sufficient
  · norm_num [total, Fin.sum_univ_two]
  · norm_num [total, maxDegree, Fin.sum_univ_two, Fin.univ_succ]
example : Bigraphical (fun _ : Fin 2 => 3) (fun _ : Fin 3 => 2) := by
  apply bipartite_graphical_sufficient
  · norm_num [total]
  · norm_num [total, maxDegree, Fin.univ_succ]

/-- info: 'MajorityDynamics.Combinatorics.SufficientGraphicality.graphical_sufficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms graphical_sufficient
/-- info: 'MajorityDynamics.Combinatorics.SufficientGraphicality.bipartite_graphical_sufficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bipartite_graphical_sufficient
/-- info: 'MajorityDynamics.Combinatorics.SufficientGraphicality.graphical_sufficient_integer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms graphical_sufficient_integer
/-- info: 'MajorityDynamics.Combinatorics.SufficientGraphicality.bipartite_graphical_sufficient_integer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bipartite_graphical_sufficient_integer
/-- info: 'MajorityDynamics.Combinatorics.SufficientGraphicality.graphical_sufficient_of_erdos_gallai' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms graphical_sufficient_of_erdos_gallai
/-- info: 'MajorityDynamics.Combinatorics.SufficientGraphicality.bipartite_graphical_sufficient_of_gale_ryser' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bipartite_graphical_sufficient_of_gale_ryser
/-- info: 'MajorityDynamics.Combinatorics.SufficientGraphicality.graphical_original_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms graphical_original_order
/-- info: 'MajorityDynamics.Combinatorics.SufficientGraphicality.bipartite_original_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bipartite_original_order
/-- info: 'MajorityDynamics.Combinatorics.SufficientGraphicality.graphical_subset_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms graphical_subset_bound
/-- info: 'MajorityDynamics.Combinatorics.SufficientGraphicality.bipartite_subset_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bipartite_subset_bound
/-- info: 'MajorityDynamics.Combinatorics.SufficientGraphicality.total_toNat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms total_toNat
/-- info: 'MajorityDynamics.Combinatorics.SufficientGraphicality.maxDegree_toNat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms maxDegree_toNat
end
end MajorityDynamics.Combinatorics.SufficientGraphicality
