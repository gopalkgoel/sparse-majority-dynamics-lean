import MajorityDynamics.GraphProcess.BlockDecomposition.Degrees
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable
namespace MajorityDynamics.GraphProcess.BlockDecomposition
open History
open MajorityDynamics.Probability.FixedDegreeSampling
variable {V L : Type*} [Fintype V] [LinearOrder L]

abbrev GraphFiber (π : V → L) (d : V → L → ℤ) :=
  {G : SimpleGraph V // degreeArray π G = d}
abbrev InternalFiber (π : V → L) (d : V → L → ℤ) (s : L) :=
  {G : SimpleGraph (Block π s) // ∀ v, (G.degree v : ℤ) = d v s}
abbrev CrossFiber (π : V → L) (d : V → L → ℤ) (s t : L) :=
  {E : CrossEdges (Block π s) (Block π t) //
    (∀ v, (leftDegree E v : ℤ) = d v t) ∧
    (∀ w, (rightDegree E w : ℤ) = d w s)}
abbrev ComponentFiber (π : V → L) (d : V → L → ℤ) :=
  ((s : L) → InternalFiber π d s) × ((p : Pair L) → CrossFiber π d p.val.1 p.val.2)

def fiberComponents (π : V → L) (d : V → L → ℤ) (F : ComponentFiber π d) :
    Components π := ⟨fun s => (F.1 s).val, fun p => (F.2 p).val⟩

theorem fiberComponents_degrees (π : V → L) (d : V → L → ℤ) (F : ComponentFiber π d) :
    HasDegrees π d (fiberComponents π d F) :=
  ⟨fun s => (F.1 s).property, fun p => (F.2 p).property⟩

def fiberRestrict (π : V → L) (d : V → L → ℤ) (G : GraphFiber π d) : ComponentFiber π d :=
  ⟨fun s => ⟨(restrict π G.val).1 s,
      ((restrict_hasDegrees_iff π d G.val).mpr G.property).1 s⟩,
   fun p => ⟨(restrict π G.val).2 p,
      ((restrict_hasDegrees_iff π d G.val).mpr G.property).2 p⟩⟩

def fiberGlue (π : V → L) (d : V → L → ℤ) (F : ComponentFiber π d) : GraphFiber π d :=
  ⟨glue π (fiberComponents π d F),
    (glue_degreeArray_iff π d _).mpr (fiberComponents_degrees π d F)⟩

def fiberEquiv (π : V → L) (d : V → L → ℤ) : GraphFiber π d ≃ ComponentFiber π d where
  toFun := fiberRestrict π d
  invFun := fiberGlue π d
  left_inv G := by
    apply Subtype.ext
    exact glue_restrict π G.val
  right_inv F := by
    apply Prod.ext
    · funext s
      apply Subtype.ext
      exact congrFun (congrArg Prod.fst (restrict_glue π (fiberComponents π d F))) s
    · funext p
      apply Subtype.ext
      exact congrFun (congrArg Prod.snd (restrict_glue π (fiberComponents π d F))) p

@[simp] theorem fiberEquiv_internal (π : V → L) (d : V → L → ℤ)
    (G : GraphFiber π d) (s : L) :
    ((fiberEquiv π d G).1 s).val = internalGraph π G.val s := rfl
@[simp] theorem fiberEquiv_cross (π : V → L) (d : V → L → ℤ)
    (G : GraphFiber π d) (p : Pair L) :
    ((fiberEquiv π d G).2 p).val = cross π G.val p.val.1 p.val.2 := rfl
@[simp] theorem fiberEquiv_symm_val (π : V → L) (d : V → L → ℤ)
    (F : ComponentFiber π d) :
    ((fiberEquiv π d).symm F).val = glue π (fiberComponents π d F) := rfl

/-- Graphicality means existence with exact integer counts, including negativity checks. -/
def InternalGraphical (π : V → L) (d : V → L → ℤ) (s : L) : Prop :=
  ∃ G : SimpleGraph (Block π s), ∀ v, (G.degree v : ℤ) = d v s

def CrossGraphical (π : V → L) (d : V → L → ℤ) (s t : L) : Prop :=
  ∃ E : CrossEdges (Block π s) (Block π t),
    (∀ v, (leftDegree E v : ℤ) = d v t) ∧
    (∀ w, (rightDegree E w : ℤ) = d w s)

theorem realizable_iff_ordered (π : V → L) (d : V → L → ℤ) :
    (∃ G, degreeArray π G = d) ↔
      (∀ s, InternalGraphical π d s) ∧
      (∀ p : Pair L, CrossGraphical π d p.val.1 p.val.2) := by
  constructor
  · rintro ⟨G, hG⟩
    have h := (restrict_hasDegrees_iff π d G).mpr hG
    exact ⟨fun s => ⟨_, h.1 s⟩, fun p => ⟨_, h.2 p⟩⟩
  · rintro ⟨hi, hc⟩
    let F : ComponentFiber π d :=
      ⟨fun s => ⟨Classical.choose (hi s), Classical.choose_spec (hi s)⟩,
       fun p => ⟨Classical.choose (hc p), Classical.choose_spec (hc p)⟩⟩
    exact ⟨(fiberGlue π d F).val, (fiberGlue π d F).property⟩

/-- Fact 2.1 in the paper's all-distinct-pairs formulation. -/
theorem graphical_blockwise (π : V → L) (d : V → L → ℤ) :
    (∃ G, degreeArray π G = d) ↔
      (∀ s, InternalGraphical π d s) ∧
      (∀ s t, s ≠ t → CrossGraphical π d s t) := by
  constructor
  · rintro ⟨G, hG⟩
    constructor
    · intro s
      exact ⟨internalGraph π G s, fun v =>
        (internalGraph_degree π G s v).trans (congrFun (congrFun hG v) s)⟩
    · intro s t _
      exact ⟨cross π G s t,
        fun v => (cross_leftDegree π G s t v).trans (congrFun (congrFun hG v) t),
        fun w => (cross_rightDegree π G s t w).trans (congrFun (congrFun hG w) s)⟩
  · rintro ⟨hi, hc⟩
    exact (realizable_iff_ordered π d).mpr ⟨hi, fun p => hc _ _ (ne_of_lt p.property)⟩

variable [Fintype L]

/-- Exact counts, valid even when any degree fiber is empty. -/
theorem realization_count (π : V → L) (d : V → L → ℤ) :
    Nat.card (GraphFiber π d) =
      (∏ s, Nat.card (InternalFiber π d s)) *
      ∏ p : Pair L, Nat.card (CrossFiber π d p.val.1 p.val.2) := by
  rw [Nat.card_congr (fiberEquiv π d), Nat.card_prod]
  simp only [Nat.card_pi]

end MajorityDynamics.GraphProcess.BlockDecomposition
