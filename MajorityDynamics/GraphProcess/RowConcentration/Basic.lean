import MajorityDynamics.GraphProcess.RowArray.Statistics
import MajorityDynamics.Local.Template

/-! The literal three concentration events under original history conditioning. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace MajorityDynamics.GraphProcess.RowConcentration
open Universal
variable {V : Type*} [Fintype V] {n : ℕ}

def conditionedLaw (y : Local.CoarseData V n) (q : Local.Tilt n) :=
  cond (RowArray.law y.part q) (RowArray.history y.part)

def Conditioning (y : Local.CoarseData V n) (q : Local.Tilt n) (φ : ℝ) : Prop :=
  ∀ s, φ ≤ Binomial.eventMass (Local.trials y.sizes s) (q s)
    (Local.historySupport y.sizes s)

def R1 (y : Local.CoarseData V n) (p : ℝ) (d : RowArray.Ambient y.part) : Prop :=
  ∀ v t, |(RowArray.values d v t : ℝ) - p * y.sizes t| ≤
    Real.sqrt (p * Fintype.card V) * (Real.log (Fintype.card V)) ^ (2 / 3 : ℝ)

def R2 (y : Local.CoarseData V n) (q : Local.Tilt n)
    (d : RowArray.Ambient y.part) : Prop :=
  ∀ s b, |((RowArray.childSet d s b).card : ℝ) -
    Local.templateSizes y.sizes q (append s b)| ≤
      Real.sqrt (Fintype.card V) * Real.log (Fintype.card V)

def R3 (y : Local.CoarseData V n) (p : ℝ) (q : Local.Tilt n)
    (d : RowArray.Ambient y.part) : Prop :=
  ∀ s t b, |(RowArray.childMass d s b t : ℝ) -
    Local.templateHalfEdges y.sizes q (append s b) t| ≤
      (Fintype.card V : ℝ)^2 * p / Real.sqrt (Fintype.card V) * Real.log (Fintype.card V)

def Good (y : Local.CoarseData V n) (p : ℝ) (q : Local.Tilt n)
    (d : RowArray.Ambient y.part) : Prop := R1 y p d ∧ R2 y q d ∧ R3 y p q d

def childIndicator {π : V → History (n + 1)} (s : History (n + 1)) (b : Bool)
    (v : V) (d : RowArray.Ambient π) : ℝ :=
  if v ∈ RowArray.childSet d s b then 1 else 0

def childVariable {π : V → History (n + 1)} (s : History (n + 1)) (b : Bool)
    (t : History (n + 1)) (v : V) (d : RowArray.Ambient π) : ℝ :=
  if v ∈ RowArray.childSet d s b then (RowArray.values d v t : ℝ) else 0

theorem sum_childIndicator {π : V → History (n + 1)} (s : History (n + 1))
    (b : Bool) (d : RowArray.Ambient π) :
    ∑ v, childIndicator s b v d = ((RowArray.childSet d s b).card : ℝ) := by
  simp only [childIndicator, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
    Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem sum_childVariable {π : V → History (n + 1)} (s : History (n + 1))
    (b : Bool) (t : History (n + 1)) (d : RowArray.Ambient π) :
    ∑ v, childVariable s b t v d = (RowArray.childMass d s b t : ℝ) := by
  simp only [childVariable, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
    Finset.univ_inter, RowArray.childMass, Int.cast_sum]

theorem childIndicator_bounds {π : V → History (n + 1)} (s : History (n + 1))
    (b : Bool) (v : V) (d : RowArray.Ambient π) :
    0 ≤ childIndicator s b v d ∧ childIndicator s b v d ≤ 1 := by
  unfold childIndicator
  split_ifs <;> norm_num

theorem childVariable_bounds {π : V → History (n + 1)} (s : History (n + 1))
    (b : Bool) (t : History (n + 1)) (v : V) (d : RowArray.Ambient π) :
    0 ≤ childVariable s b t v d ∧ childVariable s b t v d ≤ Fintype.card V := by
  have hb := RowArray.values_bounds d v t
  have hs : Local.partSizes π t ≤ Fintype.card V := by
    rw [← History.block_card_partSizes]
    exact Finset.card_le_univ _
  have hv : (RowArray.values d v t : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast (show RowArray.values d v t ≤ (Fintype.card V : ℤ) by split_ifs at hb <;> omega)
  unfold childVariable
  split_ifs
  · exact ⟨by exact_mod_cast hb.1, hv⟩
  · exact ⟨le_rfl, Nat.cast_nonneg _⟩

end MajorityDynamics.GraphProcess.RowConcentration
