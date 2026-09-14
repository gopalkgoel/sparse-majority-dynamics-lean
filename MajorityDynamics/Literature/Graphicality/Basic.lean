import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic

/-! Shared classical degree-sequence vocabulary, independent of the paper's
maximum-degree sufficient conditions. Public names are preserved for compatibility. -/
namespace MajorityDynamics.Combinatorics.SufficientGraphicality
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

def total {n : ℕ} (d : Fin n → ℕ) : ℕ := ∑ i, d i

def Graphical {n : ℕ} (d : Fin n → ℕ) : Prop :=
  ∃ G : SimpleGraph (Fin n), ∀ i, G.degree i = d i

def BipartiteRealizes {l n : ℕ} (G : SimpleGraph (Fin l ⊕ Fin n))
    (a : Fin l → ℕ) (b : Fin n → ℕ) : Prop :=
  (∀ i j, ¬ G.Adj (.inl i) (.inl j)) ∧
  (∀ i j, ¬ G.Adj (.inr i) (.inr j)) ∧
  (∀ i, G.degree (.inl i) = a i) ∧ (∀ j, G.degree (.inr j) = b j)

def Bigraphical {l n : ℕ} (a : Fin l → ℕ) (b : Fin n → ℕ) : Prop :=
  ∃ G, BipartiteRealizes G a b

/-- Exactly the first `r` labeled indices; the bound only constructs their inclusion. -/
def prefixSet (n r : ℕ) (hr : r ≤ n) : Finset (Fin n) :=
  univ.map (Fin.castLEEmb hr)

@[simp] theorem card_prefix (n r : ℕ) (hr : r ≤ n) : (prefixSet n r hr).card = r := by
  simp [prefixSet]

/-- Zero-based membership makes the correspondence to the cited prefixes explicit. -/
@[simp] theorem mem_prefixSet {n r : ℕ} (hr : r ≤ n) (i : Fin n) :
    i ∈ prefixSet n r hr ↔ i.val < r := by
  simp only [prefixSet, mem_map, mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    exact j.isLt
  · intro hi
    exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩

end
end MajorityDynamics.Combinatorics.SufficientGraphicality
