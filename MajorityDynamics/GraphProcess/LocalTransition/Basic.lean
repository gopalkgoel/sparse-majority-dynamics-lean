import MajorityDynamics.GraphProcess.RowConcentration.Basic
import MajorityDynamics.GraphProcess.LocalTransition.Algebra

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.LocalTransition
open Universal
variable {V : Type*} [Fintype V] {n : ℕ}

/-- Literal L1, as a pointwise parent identity. -/
def Refines (π : V → History (n+1)) (π' : V → History (n+2)) : Prop :=
  ∀ v, parent (π' v) = π v

/-- The original four local conclusions, with real unrounded sizes and ordered totals. -/
def LocalSuccess (y : Local.CoarseData V n) (q : Local.Tilt n) (p C : ℝ)
    (y' : Local.CoarseData V (n+1)) : Prop :=
  Refines y.part y'.part ∧ y'.reg = true ∧
  (∀ s b, |(y'.sizes (append s b) : ℝ) -
    Local.templateSizes y.sizes q (append s b)| ≤ C * sizeScale (Fintype.card V)) ∧
  (∀ s t b c, |y'.realEdges (append s b) (append t c) -
    Local.templateEdges y.sizes y.realEdges q (append s b) (append t c)| ≤
      C * edgeScale (Fintype.card V) p)

/-- Precisely R2 and R3 on the actual state array. -/
def FiberGood (y : Local.CoarseData V n) (q : Local.Tilt n) (p C : ℝ)
    (σ : FineState.State V n) : Prop :=
  (∀ s b, |((RowArray.childSet (RowArray.stateArray σ) s b).card : ℝ) -
    Local.templateSizes y.sizes q (append s b)| ≤ C * sizeScale (Fintype.card V)) ∧
  (∀ s t b, |(RowArray.childMass (RowArray.stateArray σ) s b t : ℝ) -
    Local.templateHalfEdges y.sizes q (append s b) t| ≤ C * massScale (Fintype.card V) p)

/-- All three original typicality conclusions. R1 is needed by the later
kernel estimate even though only R2/R3 enter the deterministic calculation. -/
def FiberTypical (y : Local.CoarseData V n) (q : Local.Tilt n) (p C : ℝ)
    (σ : FineState.State V n) : Prop :=
  (∀ v t, |(σ.deg v t : ℝ) - p * y.sizes t| ≤
    Real.sqrt (p * Fintype.card V) * Real.log (Fintype.card V)^(2/3 : ℝ)) ∧
    FiberGood y q p C σ

/-- Precisely S1–S3: the edge center is the actual mass quotient, not the template. -/
def KernelGood (y : Local.CoarseData V n) (p C : ℝ)
    (σ : FineState.State V n) (τ : FineState.State V (n+1)) : Prop :=
  τ.part = FineState.refinement σ ∧ CoarseKernel.Regular p τ.part τ.deg ∧
  ∀ s t b c, |(CoarseKernel.rho p τ).realEdges (append s b) (append t c) -
    (RowArray.childMass (RowArray.stateArray σ) s b t : ℝ) *
      (RowArray.childMass (RowArray.stateArray σ) t c s : ℝ) / y.realEdges s t| ≤
    C * edgeScale (Fintype.card V) p

theorem refines_iff_children (π : V → History (n+1)) (π' : V → History (n+2)) :
    Refines π π' ↔ ∀ s,
      Disjoint (History.block π' (append s false)) (History.block π' (append s true)) ∧
      History.block π' (append s false) ∪ History.block π' (append s true) =
        History.block π s := by
  constructor
  · intro h s
    refine ⟨History.block_disjoint π' ?_, ?_⟩
    · intro he
      have := congrArg last he
      simp only [last_append, Bool.false_eq_true] at this
    · ext v
      simp only [Finset.mem_union, History.mem_block]
      constructor
      · rintro (hv | hv) <;> simpa only [hv, parent_append] using (h v).symm
      · intro hv
        have hp : parent (π' v) = s := (h v).trans hv
        have he := append_parent_last (π' v)
        rw [hp] at he
        cases hb : last (π' v)
        · exact Or.inl (by simpa only [hb] using he.symm)
        · exact Or.inr (by simpa only [hb] using he.symm)
  · intro h v
    have hv : v ∈ History.block π (π v) := by simp
    rw [← (h (π v)).2] at hv
    rcases Finset.mem_union.mp hv with hv | hv
    · have he := (History.mem_block _ _ _).mp hv
      rw [he, parent_append]
    · have he := (History.mem_block _ _ _).mp hv
      rw [he, parent_append]

/-- The deterministic S1 conclusion under the actual graph kernel. -/
theorem K_split (σ : FineState.State V n) :
    FineKernel.K σ {τ | τ.part = FineState.refinement σ ∧
      ∀ s b, History.block τ.part (append s b) =
        RowArray.childSet (RowArray.stateArray σ) s b} = 1 := by
  have he : {τ : FineState.State V (n+1) | τ.part = FineState.refinement σ ∧
      ∀ s b, History.block τ.part (append s b) =
        RowArray.childSet (RowArray.stateArray σ) s b} =
      {τ | τ.part = FineState.refinement σ} := by
    ext τ
    constructor
    · exact And.left
    · intro h
      exact ⟨h, by intro s b; rw [h, RowArray.childSet_stateArray]⟩
  rw [he]
  exact FineKernel.K_refinement σ

/-- Array equality here is only transport; both statistics remain the literal ones. -/
theorem fiberGood_of_rows (y : Local.CoarseData V n) (q : Local.Tilt n) (p : ℝ)
    (σ : FineState.State V n) (d : RowArray.Ambient y.part)
    (hp : σ.part = y.part) (hd : σ.deg = RowArray.values d)
    (h2 : RowConcentration.R2 y q d) (h3 : RowConcentration.R3 y p q d) :
    FiberGood y q p 1 σ := by
  have hc : ∀ s b, RowArray.childSet (RowArray.stateArray σ) s b = RowArray.childSet d s b := by
    intro s b
    ext v
    simp only [RowArray.mem_childSet, RowArray.realRow_stateArray, hp]
    have hr : FineState.row σ.deg v = RowArray.realRow d v := by
      apply WithLp.ofLp_injective
      funext t
      change (σ.deg v t : ℝ) = RowArray.realRow d v t
      rw [RowArray.realRow_apply, hd]
    rw [hr]
  have hm : ∀ s b t, RowArray.childMass (RowArray.stateArray σ) s b t =
      RowArray.childMass d s b t := by
    intro s b t
    simp only [RowArray.childMass, hc, RowArray.values_stateArray, hd]
  constructor
  · intro s b
    simpa only [hc, one_mul, sizeScale] using h2 s b
  · intro s t b
    simpa only [hm, one_mul, massScale] using h3 s t b

/-- Exact coefficient-one adapter from all three existing row estimates. -/
theorem fiberTypical_of_good (y : Local.CoarseData V n) (q : Local.Tilt n) (p : ℝ)
    (σ : FineState.State V n) (d : RowArray.Ambient y.part)
    (hp : σ.part = y.part) (hd : σ.deg = RowArray.values d)
    (h : RowConcentration.Good y p q d) : FiberTypical y q p 1 σ := by
  refine ⟨?_, fiberGood_of_rows y q p σ d hp hd h.2.1 h.2.2⟩
  intro v t
  simpa only [hd] using h.1 v t

end MajorityDynamics.GraphProcess.LocalTransition
