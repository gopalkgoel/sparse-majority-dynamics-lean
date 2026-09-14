import MajorityDynamics.GraphProcess.LocalTransition.Basic
import MajorityDynamics.GraphProcess.LocalTransition.Mixture

/-! A terminal local transition records only the refined block sizes.  It does
not ask the output state to be regular and does not estimate its edge totals,
so no nondegeneracy assumption on the two new children is needed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.LocalTransition
open Universal
variable {V : Type*} [Fintype V] {n : ℕ}

/-- The only fine-state estimate needed to control terminal block sizes. -/
def SizeFiberGood (y : Local.CoarseData V n) (q : Local.Tilt n) (C : ℝ)
    (σ : FineState.State V n) : Prop :=
  ∀ s b, |((RowArray.childSet (RowArray.stateArray σ) s b).card : ℝ) -
    Local.templateSizes y.sizes q (append s b)| ≤
      C * sizeScale (Fintype.card V)

/-- Terminal output: exact refinement and the child-size estimates. -/
def TerminalSizeSuccess (y : Local.CoarseData V n) (q : Local.Tilt n) (C : ℝ)
    (y' : Local.CoarseData V (n+1)) : Prop :=
  Refines y.part y'.part ∧
  ∀ s b, |(y'.sizes (append s b) : ℝ) -
    Local.templateSizes y.sizes q (append s b)| ≤
      C * sizeScale (Fintype.card V)

theorem sizeFiberGood_of_fiberGood (y : Local.CoarseData V n) (q : Local.Tilt n)
    (p C : ℝ) (σ : FineState.State V n) (h : FiberGood y q p C σ) :
    SizeFiberGood y q C σ := h.1

/-- The terminal conclusion is deterministic once the current rows satisfy R2;
the next graph resampling affects degrees but not the refined partition. -/
theorem terminalSizeSuccess_of_refinement (y : Local.CoarseData V n)
    (q : Local.Tilt n) (p C : ℝ) (σ : FineState.State V n)
    (τ : FineState.State V (n+1)) (hρ : CoarseKernel.rho p σ = y)
    (hf : SizeFiberGood y q C σ) (href : τ.part = FineState.refinement σ) :
    TerminalSizeSuccess y q C (CoarseKernel.rho p τ) := by
  have hpart : σ.part = y.part := congrArg Local.CoarseData.part hρ
  constructor
  · intro v
    change parent (τ.part v) = y.part v
    rw [href, FineState.parent_refinement, hpart]
  · intro s b
    have hc : (CoarseKernel.rho p τ).sizes (append s b) =
        (RowArray.childSet (RowArray.stateArray σ) s b).card := by
      rw [RowArray.childSet_stateArray, History.block_card_partSizes]
      change Local.partSizes τ.part (append s b) = _
      rw [href]
    rw [hc]
    exact hf s b

theorem refinement_failure_zero (σ : FineState.State V n) :
    (FineKernel.K σ).real {τ | ¬ τ.part = FineState.refinement σ} ≤ 0 := by
  have hgood : (FineKernel.K σ).real
      {τ | τ.part = FineState.refinement σ} = 1 := by
    rw [Measure.real, FineKernel.K_refinement, ENNReal.toReal_one]
  have hc := probReal_compl_eq_one_sub (μ := FineKernel.K σ)
    ((Set.toFinite {τ | τ.part = FineState.refinement σ}).measurableSet)
  change (FineKernel.K σ).real {τ | ¬ τ.part = FineState.refinement σ} =
    1 - (FineKernel.K σ).real {τ | τ.part = FineState.refinement σ} at hc
  rw [hgood] at hc
  have hn : 0 ≤ (FineKernel.K σ).real
      {τ | ¬ τ.part = FineState.refinement σ} := measureReal_nonneg
  linarith

/-- Size-only Kbar assembly.  There is no kernel-splitting error: refinement is
an almost-sure identity of the exact fine kernel. -/
theorem terminal_size_failure (p : unitInterval) (y : Local.CoarseData V n)
    (q : Local.Tilt n) (C ε : ℝ)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hy : CoarseKernel.pAttainable p y) (hε : 0 ≤ ε)
    (hf : (CoarseKernel.Lambda p y).real
      {σ | ¬ SizeFiberGood y q C σ} ≤ ε) :
    (CoarseKernel.Kbar p y).real
      {z | ¬ TerminalSizeSuccess y q C z} ≤ ε := by
  have h := Kbar_failure_le p y hp hp1 hy
    (SizeFiberGood y q C)
    (fun σ τ => τ.part = FineState.refinement σ)
    (TerminalSizeSuccess y q C)
    (fun σ hρ hF τ hS =>
      terminalSizeSuccess_of_refinement y q p C σ τ hρ hF hS)
    ε 0 hε (le_refl 0) hf
    (fun σ _ _ => refinement_failure_zero σ)
  simpa only [add_zero] using h

end MajorityDynamics.GraphProcess.LocalTransition
