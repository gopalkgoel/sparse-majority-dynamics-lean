import MajorityDynamics.GraphProcess.LocalTransition.Basic
import MajorityDynamics.Local.Admissibility

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.KernelInputs
open Universal
variable {V : Type*} [Fintype V] {n : ℕ}

/-- The actual child vertex set, without a fresh abstract subset parameter. -/
abbrev child (σ : FineState.State V n) (s : History (n+1)) (b : Bool) : Finset V :=
  RowArray.childSet (RowArray.stateArray σ) s b

/-- R2 alone, retaining its original local template and scale. -/
def SizeTypical (y : Local.CoarseData V n) (q : Local.Tilt n) (C : ℝ)
    (σ : FineState.State V n) : Prop :=
  ∀ s b, |((child σ s b).card : ℝ) -
    Local.templateSizes y.sizes q (append s b)| ≤
      C * LocalTransition.sizeScale (Fintype.card V)

/-- R1 alone. -/
def DegreeTypical (y : Local.CoarseData V n) (p : ℝ)
    (σ : FineState.State V n) : Prop :=
  ∀ v t, |(σ.deg v t : ℝ) - p * y.sizes t| ≤
    Real.sqrt (p * Fintype.card V) * Real.log (Fintype.card V)^(2/3 : ℝ)

theorem child_partition (σ : FineState.State V n) (s : History (n+1)) :
    Disjoint (child σ s false) (child σ s true) ∧
      child σ s false ∪ child σ s true = History.block σ.part s :=
  ⟨RowArray.childSet_disjoint _ _,
    RowArray.childSet_union _ (RowArray.stateArray_history σ) s⟩

theorem child_subset (σ : FineState.State V n) (s : History (n+1)) (b : Bool) :
    child σ s b ⊆ History.block σ.part s := by
  intro v hv
  exact (History.mem_block _ _ _).mpr ((RowArray.mem_childSet _ _ _ _).mp hv).1

theorem child_complement (σ : FineState.State V n) (s : History (n+1)) (b : Bool) :
    History.block σ.part s \ child σ s b = child σ s (!b) := by
  have hd := (child_partition σ s).1
  have hu := (child_partition σ s).2
  rw [← hu]
  cases b <;> simp only [Bool.not_false, Bool.not_true]
  · rw [Finset.union_sdiff_left]
    exact Finset.sdiff_eq_self_of_disjoint hd.symm
  · rw [Finset.union_comm, Finset.union_sdiff_left]
    exact Finset.sdiff_eq_self_of_disjoint hd

theorem child_card_sum (σ : FineState.State V n) (s : History (n+1)) (b : Bool) :
    (child σ s b).card + (child σ s (!b)).card = Local.partSizes σ.part s := by
  have h := RowArray.child_card_conservation (RowArray.stateArray σ)
    (RowArray.stateArray_history σ) s
  cases b
  · exact h
  · simpa only [Bool.not_true, add_comm] using h

theorem child_card_le (σ : FineState.State V n) (s : History (n+1)) (b : Bool) :
    (child σ s b).card ≤ Fintype.card V := Finset.card_le_univ _

/-- Original LA.split and original R2 imply the manuscript's child lower bound. -/
theorem child_size_lower {y : Local.CoarseData V n} {q : Local.Tilt n}
    {T φ p C : ℝ} (hT : 0 < T) (hφ : 0 ≤ φ)
    (hLA : Local.Admissible y q T φ p) {σ : FineState.State V n}
    (h2 : SizeTypical y q C σ)
    (herr : C * LocalTransition.sizeScale (Fintype.card V) ≤
      φ * Fintype.card V / (2*T)) (s : History (n+1)) (b : Bool) :
    φ * Fintype.card V / (2*T) ≤ ((child σ s b).card : ℝ) := by
  have hs : (Fintype.card V : ℝ)/T ≤ (y.sizes s : ℝ) := by
    simpa only [div_eq_mul_inv, mul_comm] using hLA.sizes s
  have htemplate : φ * Fintype.card V / T ≤
      Local.templateSizes y.sizes q (append s b) := by
    simp only [Local.templateSizes, parent_append, last_append]
    calc
      φ * Fintype.card V / T = φ * ((Fintype.card V : ℝ)/T) := by ring
      _ ≤ φ * (y.sizes s : ℝ) := mul_le_mul_of_nonneg_left hs hφ
      _ ≤ (y.sizes s : ℝ) * Local.splitProbability y.sizes q s b := by
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left (hLA.split s b).1 (Nat.cast_nonneg (y.sizes s))
  have hb := (abs_le.mp (h2 s b)).1
  have he : φ * Fintype.card V / T = 2 * (φ * Fintype.card V / (2*T)) := by
    field_simp
  linarith

/-- Complement sizes are the opposite literal child sizes, including casts. -/
theorem child_complement_card {y : Local.CoarseData V n} {p : ℝ}
    (σ : FineState.State V n) (hρ : CoarseKernel.rho p σ = y)
    (s : History (n+1)) (b : Bool) :
    (y.sizes s : ℝ) - (child σ s b).card = (child σ s (!b)).card := by
  have hp : σ.part = y.part := congrArg Local.CoarseData.part hρ
  have hh := child_card_sum σ s b
  rw [hp] at hh
  have hr : ((child σ s b).card : ℝ) + (child σ s (!b)).card = (y.sizes s : ℝ) := by
    exact_mod_cast hh
  linarith

/-- The parent typicality object supplies precisely R1 and R2; R3 is unused. -/
theorem typical_inputs {y : Local.CoarseData V n} {q : Local.Tilt n} {p C : ℝ}
    {σ : FineState.State V n} (h : LocalTransition.FiberTypical y q p C σ) :
    DegreeTypical y p σ ∧ SizeTypical y q C σ := ⟨h.1,h.2.1⟩

end MajorityDynamics.GraphProcess.KernelInputs
