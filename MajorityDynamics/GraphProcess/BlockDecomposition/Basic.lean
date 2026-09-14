import MajorityDynamics.GraphProcess.FineState.Main
import MajorityDynamics.Probability.FixedDegreeSampling.BipartiteBasic

noncomputable section
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable
namespace MajorityDynamics.GraphProcess.BlockDecomposition
open History
open MajorityDynamics.Probability.FixedDegreeSampling
variable {V L : Type*} [LinearOrder L]

abbrev Block (π : V → L) (s : L) := {v : V // π v = s}
abbrev Pair (L : Type*) [LT L] := {p : L × L // p.1 < p.2}
abbrev Components (π : V → L) :=
  ((s : L) → SimpleGraph (Block π s)) ×
  ((p : Pair L) → CrossEdges (Block π p.val.1) (Block π p.val.2))

def cross (π : V → L) (G : SimpleGraph V) (s t : L) :
    CrossEdges (Block π s) (Block π t) := {e | G.Adj e.1.val e.2.val}

def restrict (π : V → L) (G : SimpleGraph V) : Components π :=
  ⟨fun s => internalGraph π G s, fun p => cross π G p.val.1 p.val.2⟩

/-- Glue each unordered block pair once, orienting distinct labels increasingly. -/
def glue (π : V → L) (C : Components π) : SimpleGraph V where
  Adj v w :=
    (∃ (s : L) (hv : π v = s) (hw : π w = s),
      (C.1 s).Adj ⟨v, hv⟩ ⟨w, hw⟩) ∨
    (∃ p : Pair L,
      (∃ (hv : π v = p.val.1) (hw : π w = p.val.2),
        (⟨v, hv⟩, ⟨w, hw⟩) ∈ C.2 p) ∨
      (∃ (hw : π w = p.val.1) (hv : π v = p.val.2),
        (⟨w, hw⟩, ⟨v, hv⟩) ∈ C.2 p))
  symm := ⟨by
    intro v w h
    rcases h with ⟨s, hv, hw, h⟩ | ⟨p, h | h⟩
    · exact Or.inl ⟨s, hw, hv, (C.1 s).adj_symm h⟩
    · exact Or.inr ⟨p, Or.inr h⟩
    · exact Or.inr ⟨p, Or.inl h⟩⟩
  loopless := ⟨by
    intro v h
    rcases h with ⟨s, hv, hw, h⟩ | ⟨p, h | h⟩
    · exact (C.1 s).irrefl h
    · obtain ⟨hv, hw, _⟩ := h
      exact (ne_of_lt p.property) (hv.symm.trans hw)
    · obtain ⟨hv, hw, _⟩ := h
      exact (ne_of_lt p.property) (hv.symm.trans hw)⟩

@[simp] theorem glue_internal (π : V → L) (C : Components π) (s : L)
    (v w : Block π s) : (glue π C).Adj v.val w.val ↔ (C.1 s).Adj v w := by
  constructor
  · rintro (⟨t, hv, hw, h⟩ | ⟨p, h | h⟩)
    · have ht : t = s := hv.symm.trans v.property
      cases ht
      exact h
    · obtain ⟨hv, hw, _⟩ := h
      exact False.elim ((ne_of_lt p.property)
        (hv.symm.trans (v.property.trans (w.property.symm.trans hw))))
    · obtain ⟨hw, hv, _⟩ := h
      exact False.elim ((ne_of_lt p.property)
        (hw.symm.trans (w.property.trans (v.property.symm.trans hv))))
  · intro h
    exact Or.inl ⟨s, v.property, w.property, h⟩

@[simp] theorem glue_cross (π : V → L) (C : Components π) (p : Pair L)
    (v : Block π p.val.1) (w : Block π p.val.2) :
    (glue π C).Adj v.val w.val ↔ (v, w) ∈ C.2 p := by
  constructor
  · rintro (⟨t, hv, hw, h⟩ | ⟨q, h | h⟩)
    · exact False.elim ((ne_of_lt p.property)
        (v.property.symm.trans (hv.trans (hw.symm.trans w.property))))
    · obtain ⟨hv, hw, h⟩ := h
      have hq : q = p := Subtype.ext (Prod.ext
        (hv.symm.trans v.property) (hw.symm.trans w.property))
      subst q
      exact h
    · obtain ⟨hw, hv, _⟩ := h
      have h₁ := hw.symm.trans w.property
      have h₂ := hv.symm.trans v.property
      have hlt := q.property
      rw [h₁, h₂] at hlt
      exact False.elim (not_lt_of_gt p.property hlt)
  · intro h
    exact Or.inr ⟨p, Or.inl ⟨v.property, w.property, h⟩⟩

@[simp] theorem restrict_glue (π : V → L) (C : Components π) :
    restrict π (glue π C) = C := by
  apply Prod.ext
  · funext s
    ext v w
    exact glue_internal π C s v w
  · funext p
    ext e
    exact glue_cross π C p e.1 e.2

@[simp] theorem glue_restrict (π : V → L) (G : SimpleGraph V) :
    glue π (restrict π G) = G := by
  ext v w
  rcases lt_trichotomy (π v) (π w) with h | h | h
  · exact glue_cross π (restrict π G) ⟨(π v, π w), h⟩ ⟨v, rfl⟩ ⟨w, rfl⟩
  · exact glue_internal π (restrict π G) (π v) ⟨v, rfl⟩ ⟨w, h.symm⟩
  · rw [(glue π (restrict π G)).adj_comm, G.adj_comm]
    exact glue_cross π (restrict π G) ⟨(π w, π v), h⟩ ⟨w, rfl⟩ ⟨v, rfl⟩

def decompositionEquiv (π : V → L) : SimpleGraph V ≃ Components π where
  toFun := restrict π
  invFun := glue π
  left_inv := glue_restrict π
  right_inv := restrict_glue π

end MajorityDynamics.GraphProcess.BlockDecomposition
