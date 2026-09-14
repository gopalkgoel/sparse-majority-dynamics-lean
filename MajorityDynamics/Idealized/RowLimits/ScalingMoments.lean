import MajorityDynamics.Idealized.RowLimits.Scaling

/-! Exact normalization of A.2's monomial moments and error bound. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace MajorityDynamics.Idealized.RowLimits
open Binomial.Approximation

/-- Homogeneity applies also to constants and repeated coordinates. -/
theorem monomial_div {d : ℕ} (c : ℝ) (e : Fin d → ℕ)
    (x : Fin d → ℝ) (a : ℝ) :
    monomial c e (fun i => x i / a) = monomial c e x / a ^ (∑ i, e i) := by
  simp only [monomial, div_pow, Finset.prod_div_distrib, ← Finset.prod_pow_eq_pow_sum]
  ring

/-- Exact scaling of raw event moments; no integrability premise is hidden. -/
theorem integral_monomial_div {α : Type*} [MeasurableSpace α] {d : ℕ}
    (μ : Measure α) (E : Set α) (x : α → Fin d → ℝ)
    (c : ℝ) (e : Fin d → ℕ) (a : ℝ) :
    (∫ z in E, monomial c e (fun i => x z i / a) ∂μ) =
      (∫ z in E, monomial c e (x z) ∂μ) / a ^ (∑ i, e i) := by
  simp_rw [monomial_div]
  exact integral_div _ _

/-- A.2's degree-dependent error becomes the same error for every normalized
monomial, in particular degrees zero, one, and two used in E.3. -/
theorem normalized_error {a A B C L : ℝ} (ha : 0 < a) (degree : ℕ)
    (h : |A - B| ≤ C * a ^ ((degree : ℝ) - 1) * L) :
    |A / a ^ degree - B / a ^ degree| ≤ C * L / a := by
  rw [← sub_div, abs_div, abs_of_pos (pow_pos ha degree)]
  apply (div_le_iff₀ (pow_pos ha degree)).2
  have heq : C * L / a * a ^ degree = C * a ^ ((degree : ℝ) - 1) * L := by
    rw [Real.rpow_sub ha, Real.rpow_natCast, Real.rpow_one]
    ring
  rw [heq]
  exact h

/-- Apply the normalized error directly to two actual event integrals. -/
theorem normalized_monomial_comparison {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {d : ℕ}
    (μ : Measure α) (ν : Measure β) (E : Set α) (F : Set β)
    (x : α → Fin d → ℝ) (y : β → Fin d → ℝ)
    (c : ℝ) (e : Fin d → ℕ) (a C L : ℝ) (ha : 0 < a)
    (h : |(∫ z in E, monomial c e (x z) ∂μ) -
        (∫ z in F, monomial c e (y z) ∂ν)| ≤
      C * a ^ (((∑ i, e i : ℕ) : ℝ) - 1) * L) :
    |(∫ z in E, monomial c e (fun i => x z i / a) ∂μ) -
      (∫ z in F, monomial c e (fun i => y z i / a) ∂ν)| ≤ C * L / a := by
  rw [integral_monomial_div, integral_monomial_div]
  exact normalized_error ha _ h

end MajorityDynamics.Idealized.RowLimits
