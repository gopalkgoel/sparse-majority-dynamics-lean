import Mathlib.Probability.UniformOn
import Mathlib.MeasureTheory.Measure.Sub
import MajorityDynamics.GraphProcess.GoodArrayProbability.Product

noncomputable section
open scoped BigOperators Classical ENNReal
open MeasureTheory ProbabilityTheory
namespace MajorityDynamics.Probability.ConditionedBinomialBox

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The literal uniform measure on the finite lattice box. -/
def uniformBox (B : Finset α) : Measure α := uniformOn (B : Set α)

theorem uniformBox_probability (B : Finset α) (hB : B.Nonempty) :
    IsProbabilityMeasure (uniformBox B) :=
  isProbabilityMeasure_uniformOn B.finite_toSet hB

theorem uniformBox_singleton (B : Finset α) (x : α) :
    uniformBox B {x} = if x ∈ B then 1 / (B.card : ℝ≥0∞) else 0 := by
  classical
  change uniformOn (B : Set α) {x} = _
  rw [← Finset.coe_singleton]
  rw [uniformOn_apply_finset]
  by_cases hx : x ∈ B <;> simp [hx]

theorem uniformBox_singleton_real (B : Finset α) (x : α) :
    (uniformBox B).real {x} = if x ∈ B then 1 / (B.card : ℝ) else 0 := by
  rw [measureReal_def, uniformBox_singleton]
  split_ifs <;> simp

theorem uniformBox_support (B : Finset α) : uniformBox B (B : Set α)ᶜ = 0 := by
  exact (uniformOn_eq_zero_iff B.finite_toSet).2 (Set.inter_compl_self _)

theorem finset_mass_lower (μ : Measure α) [IsProbabilityMeasure μ] (B : Finset α)
    (a : ℝ) (hpoint : ∀ x ∈ B, a ≤ μ.real {x}) :
    a * B.card ≤ μ.real (B : Set α) := by
  calc
    a * B.card = ∑ _x ∈ B, a := by simp [mul_comm]
    _ ≤ ∑ x ∈ B, μ.real {x} := Finset.sum_le_sum hpoint
    _ = _ := sum_measureReal_singleton B

omit [MeasurableSingletonClass α] in
theorem point_le_conditioned (μ : Measure α) [IsProbabilityMeasure μ]
    {E : Set α} (hE : MeasurableSet E) (hpos : 0 < μ E) {x : α} (hx : x ∈ E) :
    μ.real {x} ≤ (cond μ E).real {x} :=
  GraphProcess.GoodArrayProbability.real_le_cond_real μ hE
    (Set.singleton_subset_iff.mpr hx) hpos

/-- On a countable discrete space, domination of atoms implies domination of measures. -/
theorem measure_le_of_singletons [Countable α] (μ ν : Measure α)
    (h : ∀ x, μ {x} ≤ ν {x}) : μ ≤ ν := by
  rw [← Measure.sum_smul_dirac μ, ← Measure.sum_smul_dirac ν]
  intro s
  simp only [Measure.sum_apply_of_countable, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.tsum_le_tsum fun x => mul_le_mul_left (h x) _

/-- An actual atom lower bound gives measure domination by a weighted uniform box. -/
theorem uniformBox_domination [Countable α] (ρ : Measure α) [IsProbabilityMeasure ρ]
    (B : Finset α) (hB : B.Nonempty) {a β : ℝ} (_hβ : 0 ≤ β)
    (hpoint : ∀ x ∈ B, a ≤ ρ.real {x}) (hweight : β ≤ a * B.card) :
    ENNReal.ofReal β • uniformBox B ≤ ρ := by
  have hc : (0 : ℝ) < B.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hB)
  apply measure_le_of_singletons
  intro x
  rw [Measure.smul_apply, smul_eq_mul, uniformBox_singleton]
  by_cases hx : x ∈ B
  · simp only [hx, ite_true]
    have hr : β / B.card ≤ ρ.real {x} :=
      (div_le_iff₀ hc).2 (hweight.trans (mul_le_mul_of_nonneg_right (hpoint x hx) hc.le))
    have he : ENNReal.ofReal (β / B.card) ≤ ρ {x} :=
      (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 hr
    rw [ENNReal.ofReal_div_of_pos hc, ENNReal.ofReal_natCast] at he
    simpa [div_eq_mul_inv] using he
  · simp [hx]

/-- Subtract the proved dominated component and normalize the actual positive remainder. -/
theorem exists_uniform_component [Countable α] (ρ : Measure α) [IsProbabilityMeasure ρ]
    (B : Finset α) (hB : B.Nonempty) {a β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hpoint : ∀ x ∈ B, a ≤ ρ.real {x}) (hweight : β ≤ a * B.card) :
    ∃ ν : Measure α, IsProbabilityMeasure ν ∧
      ρ = ENNReal.ofReal β • uniformBox B + ENNReal.ofReal (1 - β) • ν := by
  let _ := uniformBox_probability B hB
  let τ := ENNReal.ofReal β • uniformBox B
  have : IsFiniteMeasure τ := ⟨by simp [τ, Measure.smul_apply, smul_eq_mul]⟩
  have hdom : τ ≤ ρ := uniformBox_domination ρ B hB hβ0.le hpoint hweight
  have hrest : (ρ - τ) Set.univ = ENNReal.ofReal (1 - β) := by
    rw [Measure.sub_apply MeasurableSet.univ hdom]
    simp only [τ, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hβ0.le]
  have hc0 : ENNReal.ofReal (1 - β) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hβ1)
  have hct : ENNReal.ofReal (1 - β) ≠ ∞ := ENNReal.ofReal_ne_top
  let ν := (ENNReal.ofReal (1 - β))⁻¹ • (ρ - τ)
  have hprob : IsProbabilityMeasure ν := by
    constructor
    change (ENNReal.ofReal (1 - β))⁻¹ * (ρ - τ) Set.univ = 1
    rw [hrest, ENNReal.inv_mul_cancel hc0 hct]
  refine ⟨ν, hprob, ?_⟩
  have hscale : ENNReal.ofReal (1 - β) • ν = ρ - τ := by
    simp only [ν, smul_smul, ENNReal.mul_inv_cancel hc0 hct, one_smul]
  rw [hscale, add_comm]
  exact (Measure.sub_add_cancel_of_le hdom).symm

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.uniformBox_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uniformBox_probability
/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.uniformBox_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uniformBox_singleton
/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.uniformBox_singleton_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uniformBox_singleton_real
/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.uniformBox_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uniformBox_support
/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.finset_mass_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finset_mass_lower
/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.point_le_conditioned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms point_le_conditioned
/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.measure_le_of_singletons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms measure_le_of_singletons
/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.uniformBox_domination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uniformBox_domination
/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.exists_uniform_component' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_uniform_component

end MajorityDynamics.Probability.ConditionedBinomialBox
