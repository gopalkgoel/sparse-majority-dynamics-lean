import MajorityDynamics.GraphProcess.BlockDecomposition.Basic
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable
namespace MajorityDynamics.GraphProcess.BlockDecomposition
open History
open MajorityDynamics.Probability.FixedDegreeSampling
variable {V L : Type*} [Fintype V] [LinearOrder L]

omit [LinearOrder L] in
theorem cross_leftDegree (π : V → L) (G : SimpleGraph V) (s t : L) (v : Block π s) :
    (leftDegree (cross π G s t) v : ℤ) = degreeArray π G v t := by
  classical
  unfold leftDegree leftNeighbors
  rw [← Finset.sum_boole]
  change (∑ w : Block π t, if G.Adj v.val w.val then (1 : ℤ) else 0) = _
  unfold degreeArray
  exact (Finset.sum_subtype (block π t) (fun w => mem_block π t w)
    (fun w => if G.Adj v.val w then (1 : ℤ) else 0)).symm

omit [LinearOrder L] in
theorem cross_rightDegree (π : V → L) (G : SimpleGraph V) (s t : L) (w : Block π t) :
    (rightDegree (cross π G s t) w : ℤ) = degreeArray π G w s := by
  classical
  unfold rightDegree rightNeighbors
  rw [← Finset.sum_boole]
  simp_rw [cross, Set.mem_ofPred_eq, G.adj_comm]
  simpa only [degreeArray, block, Finset.sum_filter]
    using (Finset.sum_subtype (block π s) (fun v => mem_block π s v)
      (fun v => if G.Adj w.val v then (1 : ℤ) else 0)).symm

/-- Exact integer degree constraints, retaining negative targets as impossible. -/
def HasDegrees (π : V → L) (d : V → L → ℤ) (C : Components π) : Prop :=
  (∀ s (v : Block π s), ((C.1 s).degree v : ℤ) = d v s) ∧
  (∀ p : Pair L,
    (∀ v, (leftDegree (C.2 p) v : ℤ) = d v p.val.2) ∧
    (∀ w, (rightDegree (C.2 p) w : ℤ) = d w p.val.1))

theorem restrict_hasDegrees_iff (π : V → L) (d : V → L → ℤ) (G : SimpleGraph V) :
    HasDegrees π d (restrict π G) ↔ degreeArray π G = d := by
  constructor
  · intro h
    funext v t
    rcases lt_trichotomy (π v) t with hlt | heq | hgt
    · exact (cross_leftDegree π G (π v) t ⟨v, rfl⟩).symm.trans
        ((h.2 ⟨(π v, t), hlt⟩).1 ⟨v, rfl⟩)
    · exact (internalGraph_degree π G t ⟨v, heq⟩).symm.trans (h.1 t ⟨v, heq⟩)
    · exact (cross_rightDegree π G t (π v) ⟨v, rfl⟩).symm.trans
        ((h.2 ⟨(t, π v), hgt⟩).2 ⟨v, rfl⟩)
  · intro h
    constructor
    · intro s v
      exact (internalGraph_degree π G s v).trans (congrFun (congrFun h v) s)
    · intro p
      constructor
      · intro v
        exact (cross_leftDegree π G _ _ v).trans (congrFun (congrFun h v) _)
      · intro w
        exact (cross_rightDegree π G _ _ w).trans (congrFun (congrFun h w) _)

theorem glue_degreeArray_iff (π : V → L) (d : V → L → ℤ) (C : Components π) :
    degreeArray π (glue π C) = d ↔ HasDegrees π d C := by
  rw [← restrict_hasDegrees_iff, restrict_glue]

theorem glue_internal_degree (π : V → L) (C : Components π) (s : L) (v : Block π s) :
    degreeArray π (glue π C) v s = ((C.1 s).degree v : ℤ) := by
  have h := internalGraph_degree π (glue π C) s v
  have hc := congrFun (congrArg Prod.fst (restrict_glue π C)) s
  change internalGraph π (glue π C) s = C.1 s at hc
  rw [hc] at h
  exact h.symm

theorem glue_left_degree (π : V → L) (C : Components π) (p : Pair L)
    (v : Block π p.val.1) :
    degreeArray π (glue π C) v p.val.2 = (leftDegree (C.2 p) v : ℤ) := by
  have h := cross_leftDegree π (glue π C) p.val.1 p.val.2 v
  have hc := congrFun (congrArg Prod.snd (restrict_glue π C)) p
  change cross π (glue π C) p.val.1 p.val.2 = C.2 p at hc
  rw [hc] at h
  exact h.symm

theorem glue_right_degree (π : V → L) (C : Components π) (p : Pair L)
    (w : Block π p.val.2) :
    degreeArray π (glue π C) w p.val.1 = (rightDegree (C.2 p) w : ℤ) := by
  have h := cross_rightDegree π (glue π C) p.val.1 p.val.2 w
  have hc := congrFun (congrArg Prod.snd (restrict_glue π C)) p
  change cross π (glue π C) p.val.1 p.val.2 = C.2 p at hc
  rw [hc] at h
  exact h.symm

end MajorityDynamics.GraphProcess.BlockDecomposition
