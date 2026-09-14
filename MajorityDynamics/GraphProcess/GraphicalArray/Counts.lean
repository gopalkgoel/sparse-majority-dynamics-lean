import MajorityDynamics.GraphProcess.BlockDecomposition.Main

noncomputable section
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable
namespace MajorityDynamics.GraphProcess.GraphicalArray
open History BlockDecomposition
open MajorityDynamics.Probability.FixedDegreeSampling
variable {V L : Type*} [Fintype V] [LinearOrder L]

def fixedCountFamily (π : V → L) (m : L → L → ℤ) : Set (SimpleGraph V) :=
  {G | edgeTotals π (degreeArray π G) = m}
abbrev CountGraphFiber (π : V → L) (m : L → L → ℤ) :=
  {G : SimpleGraph V // G ∈ fixedCountFamily π m}
abbrev InternalCountFiber (π : V → L) (m : L → L → ℤ) (s : L) :=
  {G : SimpleGraph (Block π s) // 2 * (G.edgeFinset.card : ℤ) = m s s}
abbrev CrossCountFiber (π : V → L) (m : L → L → ℤ) (p : Pair L) :=
  {E : CrossEdges (Block π p.val.1) (Block π p.val.2) // (E.ncard : ℤ) = m p.val.1 p.val.2}
abbrev CountComponents (π : V → L) (m : L → L → ℤ) :=
  ((s : L) → InternalCountFiber π m s) × ((p : Pair L) → CrossCountFiber π m p)
def countComponents (π : V → L) (m : L → L → ℤ) (C : CountComponents π m) : Components π :=
  ⟨fun s => (C.1 s).val, fun p => (C.2 p).val⟩

theorem counts_iff (π : V → L) (m : L → L → ℤ) (hm : ∀ s t, m s t = m t s)
    (G : SimpleGraph V) : G ∈ fixedCountFamily π m ↔
    (∀ s, 2 * ((internalGraph π G s).edgeFinset.card : ℤ) = m s s) ∧
    (∀ p : Pair L, ((cross π G p.val.1 p.val.2).ncard : ℤ) = m p.val.1 p.val.2) := by
  constructor
  · intro h
    constructor
    · intro s
      have hh := congrFun (congrFun h s) s
      simpa only [edgeTotals_diagonal, internalEdgeCount] using hh
    · intro p
      simpa only [cross_edgeTotals] using congrFun (congrFun h p.val.1) p.val.2
  · rintro ⟨hi, hc⟩
    funext s t
    rcases lt_trichotomy s t with h | h | h
    · exact (cross_edgeTotals π G s t).trans (hc ⟨(s,t),h⟩)
    · subst t
      simpa only [edgeTotals_diagonal, internalEdgeCount] using hi s
    · rw [edgeTotals_symm π G s t, hm s t]
      exact (cross_edgeTotals π G t s).trans (hc ⟨(t,s),h⟩)

def countRestrict (π : V → L) (m : L → L → ℤ) (hm : ∀ s t, m s t = m t s)
    (G : CountGraphFiber π m) : CountComponents π m :=
  ⟨fun s => ⟨internalGraph π G.val s, ((counts_iff π m hm G.val).mp G.property).1 s⟩,
   fun p => ⟨cross π G.val p.val.1 p.val.2, ((counts_iff π m hm G.val).mp G.property).2 p⟩⟩

def countGlue (π : V → L) (m : L → L → ℤ) (hm : ∀ s t, m s t = m t s)
    (C : CountComponents π m) : CountGraphFiber π m := by
  refine ⟨glue π (countComponents π m C), (counts_iff π m hm _).mpr ⟨?_, ?_⟩⟩
  · intro s
    have h := congrFun (congrArg Prod.fst (restrict_glue π (countComponents π m C))) s
    change internalGraph π (glue π (countComponents π m C)) s = (C.1 s).val at h
    rw [h]
    exact (C.1 s).property
  · intro p
    have h := congrFun (congrArg Prod.snd (restrict_glue π (countComponents π m C))) p
    change cross π (glue π (countComponents π m C)) p.val.1 p.val.2 = (C.2 p).val at h
    rw [h]
    exact (C.2 p).property

def countFiberEquiv (π : V → L) (m : L → L → ℤ) (hm : ∀ s t, m s t = m t s) :
    CountGraphFiber π m ≃ CountComponents π m where
  toFun := countRestrict π m hm
  invFun := countGlue π m hm
  left_inv G := by
    apply Subtype.ext
    exact glue_restrict π G.val
  right_inv C := by
    apply Prod.ext
    · funext s
      apply Subtype.ext
      exact congrFun (congrArg Prod.fst (restrict_glue π (countComponents π m C))) s
    · funext p
      apply Subtype.ext
      exact congrFun (congrArg Prod.snd (restrict_glue π (countComponents π m C))) p

@[simp] theorem countFiberEquiv_internal (π : V → L) (m : L → L → ℤ)
    (hm : ∀ s t, m s t = m t s) (G : CountGraphFiber π m) (s : L) :
    ((countFiberEquiv π m hm G).1 s).val = internalGraph π G.val s := rfl
@[simp] theorem countFiberEquiv_cross (π : V → L) (m : L → L → ℤ)
    (hm : ∀ s t, m s t = m t s) (G : CountGraphFiber π m) (p : Pair L) :
    ((countFiberEquiv π m hm G).2 p).val = cross π G.val p.val.1 p.val.2 := rfl
@[simp] theorem countFiberEquiv_symm_val (π : V → L) (m : L → L → ℤ)
    (hm : ∀ s t, m s t = m t s) (C : CountComponents π m) :
    ((countFiberEquiv π m hm).symm C).val = glue π (countComponents π m C) := rfl

end MajorityDynamics.GraphProcess.GraphicalArray
