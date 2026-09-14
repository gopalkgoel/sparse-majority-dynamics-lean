import MajorityDynamics.GraphProcess.CoarseKernel.Main
import MajorityDynamics.Local.RowModel

/-! The literal bounded integer array space, represented by finite binomial boxes. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace MajorityDynamics.GraphProcess.RowArray
open Universal
variable {V : Type*} [Fintype V] {n : ℕ}

abbrev Ambient (π : V → History (n + 1)) :=
  (v : V) → Binomial.Box (Local.trials (Local.partSizes π) (π v))

abbrev Literal (π : V → History (n + 1)) :=
  {d : V → History (n + 1) → ℤ // ∀ v t, 0 ≤ d v t ∧
    d v t ≤ (Local.partSizes π t : ℤ) - if π v = t then 1 else 0}

instance (π : V → History (n + 1)) : MeasurableSpace (Ambient π) := ⊤
instance (π : V → History (n + 1)) : DiscreteMeasurableSpace (Ambient π) := ⟨fun _ => trivial⟩

theorem occupied_pos (π : V → History (n + 1)) (v : V) :
    0 < Local.partSizes π (π v) := by
  rw [← History.block_card_partSizes]
  exact Finset.card_pos.mpr ⟨v, by simp⟩

theorem trials_int (π : V → History (n + 1)) (v : V) (t : History (n + 1)) :
    (Local.trials (Local.partSizes π) (π v) t : ℤ) =
      (Local.partSizes π t : ℤ) - if π v = t then 1 else 0 := by
  by_cases h : π v = t
  · subst t
    have hp := occupied_pos π v
    simp only [Local.trials_self, if_true]
    omega
  · simp [Local.trials, h]

def values {π : V → History (n + 1)} (d : Ambient π) : V → History (n + 1) → ℤ :=
  fun v t => (d v t : ℕ)
def naturalRows {π : V → History (n + 1)} (d : Ambient π) : V → History (n + 1) → ℕ :=
  fun v => Binomial.point (d v)
def realRow {π : V → History (n + 1)} (d : Ambient π) (v : V) : Row (n + 1) :=
  Local.rowVector (d v)

@[simp] theorem values_nat {π : V → History (n + 1)} (d : Ambient π) (v : V)
    (t : History (n + 1)) : (naturalRows d v t : ℤ) = values d v t := rfl
@[simp] theorem realRow_apply {π : V → History (n + 1)} (d : Ambient π) (v : V)
    (t : History (n + 1)) : realRow d v t = (values d v t : ℝ) := by
  simp [realRow, Local.rowVector, Binomial.vector, values]

theorem values_bounds {π : V → History (n + 1)} (d : Ambient π) (v : V)
    (t : History (n + 1)) : 0 ≤ values d v t ∧
      values d v t ≤ (Local.partSizes π t : ℤ) - if π v = t then 1 else 0 := by
  rw [← trials_int]
  have h := (d v t).isLt
  constructor <;> dsimp [values] <;> omega

def ofLiteral {π : V → History (n + 1)} (d : Literal π) : Ambient π :=
  fun v t => ⟨(d.val v t).toNat, by
    have h := d.property v t
    rw [← trials_int] at h
    omega⟩

@[simp] theorem values_ofLiteral {π : V → History (n + 1)} (d : Literal π) :
    values (ofLiteral d) = d.val := by
  funext v t
  exact Int.toNat_of_nonneg (d.property v t).1

def literalEquiv (π : V → History (n + 1)) : Ambient π ≃ Literal π where
  toFun d := ⟨values d, values_bounds d⟩
  invFun := ofLiteral
  left_inv d := by funext v t; apply Fin.ext; simp [ofLiteral, values]
  right_inv d := Subtype.ext (values_ofLiteral d)

instance (π : V → History (n + 1)) : Fintype (Literal π) :=
  Fintype.ofEquiv (Ambient π) (literalEquiv π)

@[simp] theorem literalEquiv_val (π : V → History (n + 1)) (d : Ambient π) :
    (literalEquiv π d).val = values d := rfl

theorem naturalRows_injective (π : V → History (n + 1)) :
    Function.Injective (@naturalRows V _ n π) := by
  intro a b h
  funext v t
  exact Fin.ext (congrFun (congrFun h v) t)

theorem naturalRows_embedding (π : V → History (n + 1)) :
    MeasurableEmbedding (@naturalRows V _ n π) :=
  ⟨naturalRows_injective π, measurable_of_countable _, fun _ _ => Set.to_countable _ |>.measurableSet⟩

def graphArray (π : V → History (n + 1)) (G : SimpleGraph V) : Ambient π :=
  ofLiteral ⟨History.degreeArray π G, fun v t => ⟨History.degreeArray_nonneg π G v t,
    by
      have h := History.degreeArray_upper π G v t
      rw [History.block_card_partSizes] at h
      split_ifs at * <;> assumption⟩⟩

@[simp] theorem values_graphArray (π : V → History (n + 1)) (G : SimpleGraph V) :
    values (graphArray π G) = History.degreeArray π G := values_ofLiteral _

def stateArray (σ : FineState.State V n) : Ambient σ.part :=
  ofLiteral ⟨σ.deg, by
    obtain ⟨G, hG⟩ := σ.realizable
    rw [← hG]
    exact fun v t => ⟨History.degreeArray_nonneg _ _ _ _,
      by
        have h := History.degreeArray_upper σ.part G v t
        rw [History.block_card_partSizes] at h
        split_ifs at * <;> assumption⟩⟩

@[simp] theorem values_stateArray (σ : FineState.State V n) :
    values (stateArray σ) = σ.deg := values_ofLiteral _

@[simp] theorem realRow_stateArray (σ : FineState.State V n) (v : V) :
    realRow (stateArray σ) v = FineState.row σ.deg v := by
  apply WithLp.ofLp_injective
  funext t
  change realRow (stateArray σ) v t = (σ.deg v t : ℝ)
  rw [realRow_apply, values_stateArray]

end MajorityDynamics.GraphProcess.RowArray
