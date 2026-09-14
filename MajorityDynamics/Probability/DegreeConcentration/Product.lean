import MajorityDynamics.Probability.DegreeConcentration.Moment
import Mathlib.Probability.Independence.Integration

/-!
# The independent truncated-square bound (`eq:trunc-mgf`)

If `Y₁, …, Y_q` are independent with `Yⱼ ∼ Bin(rⱼ,p)`, `rⱼ p ≤ B`, then for every `t`

  `P[∑ⱼ (Yⱼ - rⱼ p)² ≥ t ∧ ∀ j, |Yⱼ - rⱼ p| ≤ 2B] ≤ exp(-t/(20B) + q/2)`.

This is Markov's inequality for `exp(λ ∑ⱼ (Yⱼ - rⱼ p)²)` on the truncation event, the
factorisation of the expectation of a product of independent nonnegative functions, and
the single-variable bound `truncated_exp_moment`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory unitInterval Set
open scoped BigOperators ENNReal

namespace MajorityDynamics.Probability.DegreeConcentration

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The truncation-and-spread event for a family of centered counts. -/
def truncatedSpread {J : Type*} [Fintype J] (X : J → Ω → ℕ) (r : J → ℕ) (p : I) (B t : ℝ) :
    Set Ω :=
  {ω | t ≤ ∑ j, ((X j ω : ℝ) - r j * p) ^ 2 ∧ ∀ j, |(X j ω : ℝ) - r j * p| ≤ 2 * B}

theorem measurableSet_truncatedSpread {J : Type*} [Fintype J] (X : J → Ω → ℕ)
    (hX : ∀ j, Measurable (X j)) (r : J → ℕ) (p : I) (B t : ℝ) :
    MeasurableSet (truncatedSpread X r p B t) := by
  have hcast : ∀ j, Measurable fun ω ↦ ((X j ω : ℝ) - r j * p) := fun j ↦
    (measurable_from_nat.comp (hX j)).sub_const ((r j : ℝ) * p)
  have hset : truncatedSpread X r p B t =
      {ω | t ≤ ∑ j, ((X j ω : ℝ) - r j * p) ^ 2} ∩
        ⋂ j, {ω | |(X j ω : ℝ) - r j * p| ≤ 2 * B} := by
    ext ω
    simp [truncatedSpread]
  rw [hset]
  exact (measurableSet_le measurable_const
    (Finset.measurable_sum _ fun j _ ↦ (hcast j).pow_const 2)).inter
    (MeasurableSet.iInter fun j ↦
      measurableSet_le (continuous_abs.measurable.comp (hcast j)) measurable_const)

/-- `eq:trunc-mgf`: the independent truncated-square bound. -/
theorem truncated_square_bound (P : Measure Ω) [IsProbabilityMeasure P]
    {J : Type*} [Fintype J] (X : J → Ω → ℕ) (r : J → ℕ) (p : I) (B t : ℝ) (hB : 0 < B)
    (hr : ∀ j, (r j : ℝ) * p ≤ B) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, P.map (X j) = binomial (r j) p) (hind : iIndepFun X P) :
    P (truncatedSpread X r p B t) ≤
      ENNReal.ofReal (Real.exp (-t / (20 * B) + (Fintype.card J : ℝ) / 2)) := by
  -- the weights
  let Z : J → Ω → ℝ≥0∞ := fun j ω ↦ ENNReal.ofReal (truncWeight (r j) p B (X j ω))
  have hZmeas : ∀ j, Measurable (Z j) := fun j ↦
    ENNReal.measurable_ofReal.comp ((Measurable.of_discrete (f := truncWeight (r j) p B)).comp (hX j))
  have hZind : iIndepFun Z P :=
    hind.comp (fun j (k : ℕ) ↦ ENNReal.ofReal (truncWeight (r j) p B k))
      fun j ↦ Measurable.of_discrete
  -- each factor has expectation at most `e^{1/2}`
  have hZint : ∀ j, ∫⁻ ω, Z j ω ∂P ≤ ENNReal.ofReal (Real.exp (1 / 2)) := by
    intro j
    have := lintegral_map (μ := P) (f := fun k ↦ ENNReal.ofReal (truncWeight (r j) p B k))
      (g := X j) Measurable.of_discrete (hX j)
    simp only [Z]
    rw [← this, hlaw j]
    exact truncated_exp_moment (r j) p B hB (hr j)
  -- Markov: the indicator of the event is dominated by `e^{-λ t} ∏ Zⱼ`
  have hdom : ∀ ω, (truncatedSpread X r p B t).indicator (1 : Ω → ℝ≥0∞) ω ≤
      ENNReal.ofReal (Real.exp (-t / (20 * B))) * ∏ j, Z j ω := by
    intro ω
    by_cases hω : ω ∈ truncatedSpread X r p B t
    · rw [indicator_of_mem hω, Pi.one_apply]
      obtain ⟨hsum, htrunc⟩ := hω
      have hprod : ∏ j, Z j ω = ENNReal.ofReal (Real.exp
          ((∑ j, ((X j ω : ℝ) - r j * p) ^ 2) / (20 * B))) := by
        simp only [Z]
        rw [← ENNReal.ofReal_prod_of_nonneg fun j _ ↦ truncWeight_nonneg _ _ _ _]
        congr 1
        rw [Finset.sum_div, Real.exp_sum]
        exact Finset.prod_congr rfl fun j _ ↦ truncWeight_of_le _ _ _ _ (htrunc j)
      rw [hprod, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      rw [neg_div, neg_add_eq_sub, sub_nonneg]
      exact div_le_div_of_nonneg_right hsum (by positivity)
    · rw [indicator_of_notMem hω]
      exact zero_le
  calc P (truncatedSpread X r p B t)
      = ∫⁻ ω, (truncatedSpread X r p B t).indicator (1 : Ω → ℝ≥0∞) ω ∂P :=
        (lintegral_indicator_one (measurableSet_truncatedSpread X hX r p B t)).symm
    _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (-t / (20 * B))) * ∏ j, Z j ω ∂P := lintegral_mono hdom
    _ = ENNReal.ofReal (Real.exp (-t / (20 * B))) * ∫⁻ ω, ∏ j, Z j ω ∂P :=
        lintegral_const_mul _ (Finset.measurable_prod _ fun j _ ↦ hZmeas j)
    _ = ENNReal.ofReal (Real.exp (-t / (20 * B))) * ∏ j, ∫⁻ ω, Z j ω ∂P := by
        rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ Z hZind hZmeas]
    _ ≤ ENNReal.ofReal (Real.exp (-t / (20 * B))) * ∏ _j : J, ENNReal.ofReal (Real.exp (1 / 2)) := by
        gcongr with j
        exact hZint j
    _ = ENNReal.ofReal (Real.exp (-t / (20 * B) + (Fintype.card J : ℝ) / 2)) := by
        rw [Finset.prod_const, Finset.card_univ, ← ENNReal.ofReal_pow (Real.exp_pos _).le,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_nat_mul, ← Real.exp_add]
        congr 2
        ring

end MajorityDynamics.Probability.DegreeConcentration
