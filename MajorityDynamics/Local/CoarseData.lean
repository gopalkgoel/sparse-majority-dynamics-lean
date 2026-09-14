import MajorityDynamics.Local.Template

/-! The broad, static coarse carrier of §2. It imposes no graph attainability. -/
noncomputable section
open scoped BigOperators
namespace MajorityDynamics.Local
open Universal

def partSizes {V : Type*} [Fintype V] {n : ℕ}
    (π : V → History (n + 1)) : Sizes n := by
  classical
  exact fun s => (Finset.univ.filter fun v => π v = s).card

/-- Integer ordered counts. An internal edge is counted twice. -/
structure CoarseData (V : Type*) [Fintype V] (n : ℕ) where
  part : V → History (n + 1)
  edge : History (n + 1) → History (n + 1) → ℤ
  edge_symm : ∀ s t, edge s t = edge t s
  edge_even : ∀ s, Even (edge s s)
  edge_nonneg : ∀ s t, 0 ≤ edge s t
  edge_upper : ∀ s t, edge s t ≤ (partSizes part s : ℤ) *
    ((partSizes part t : ℤ) - if s = t then 1 else 0)
  reg : Bool

namespace CoarseData
variable {V : Type*} [Fintype V] {n : ℕ}
def sizes (y : CoarseData V n) : Sizes n := partSizes y.part
def integerSizes (y : CoarseData V n) : History (n + 1) → ℤ :=
  fun s => (y.sizes s : ℤ)
def realEdges (y : CoarseData V n) : EdgeCounts n := fun s t => (y.edge s t : ℝ)

@[simp] theorem integerSizes_toNat (y : CoarseData V n) (s : History (n + 1)) :
    (y.integerSizes s).toNat = y.sizes s := by simp [integerSizes]

theorem sizes_le_card (y : CoarseData V n) (s : History (n + 1)) :
    y.sizes s ≤ Fintype.card V := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_univ)

theorem sum_sizes (y : CoarseData V n) : ∑ s, y.sizes s = Fintype.card V := by
  classical
  exact (Finset.card_eq_sum_card_fiberwise (f := y.part)
    (s := Finset.univ) (t := Finset.univ) (by simp)).symm

theorem sum_integerSizes (y : CoarseData V n) :
    ∑ s, y.integerSizes s = (Fintype.card V : ℤ) := by
  simpa only [integerSizes, ← Nat.cast_sum] using congrArg (Nat.cast : ℕ → ℤ) y.sum_sizes

theorem realEdges_symm (y : CoarseData V n) (s t : History (n + 1)) :
    y.realEdges s t = y.realEdges t s := by simp only [realEdges, y.edge_symm]
end CoarseData
end MajorityDynamics.Local
