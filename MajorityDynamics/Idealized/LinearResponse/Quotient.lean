import MajorityDynamics.Idealized.LinearResponse.Basic

/-!
# The quotient expansion behind Lemma E.4

Given the two first-order expansions (mass and first moment) of a tilted model
around a reference model, dividing them yields the reference conditional mean
plus the covariance-type first-order term, with an explicit remainder. The
first-order term of the denominator is cancelled here exactly; omitting this
cancellation would give the wrong derivative.
-/

open scoped BigOperators

namespace MajorityDynamics.Idealized.LinearResponse

/-- `X₁ = Σ β_i M1_i`, `X₂ = Σ β_i M2_i`, `Y = Σ β_i m̄_i` are the first-order
sums; `D` is the reference mass and `A` the reference first moment. -/
theorem quotient_response (M' P' A D X₁ X₂ Y eP eM S : ℝ) (hD : 0 < D)
    (hS : S = X₂ / D - A / D * X₁ / D)
    (hP : |P' - D - X₁ + Y * D| ≤ eP) (hM : |M' - A - X₂ + Y * A| ≤ eM)
    (hU : |X₁ - Y * D| ≤ D / 4) (heP : eP ≤ D / 4) :
    D / 2 ≤ P' ∧ |M' / P' - (A / D + S)| ≤
      2 / D * (eM + |X₁ - Y * D| * |S| + eP * |A / D + S|) := by
  have hU' := abs_le.mp hU
  have hP1 := abs_le.mp hP
  have hDen : D / 2 ≤ P' := by linarith [hU'.1, hP1.1]
  have hP'pos : 0 < P' := lt_of_lt_of_le (half_pos hD) hDen
  refine ⟨hDen, ?_⟩
  have hD0 : D ≠ 0 := hD.ne'
  have hP0 : P' ≠ 0 := hP'pos.ne'
  have key : M' / P' - (A / D + S) =
      ((M' - A - X₂ + Y * A) - (X₁ - Y * D) * S - (P' - D - X₁ + Y * D) * (A / D + S)) / P' := by
    subst hS
    field_simp
    ring
  rw [key, abs_div, abs_of_pos hP'pos]
  have heM : 0 ≤ eM := (abs_nonneg _).trans hM
  have heP0 : 0 ≤ eP := (abs_nonneg _).trans hP
  have hnum : |(M' - A - X₂ + Y * A) - (X₁ - Y * D) * S - (P' - D - X₁ + Y * D) * (A / D + S)| ≤
      eM + |X₁ - Y * D| * |S| + eP * |A / D + S| := by
    have h1 := abs_sub ((M' - A - X₂ + Y * A) - (X₁ - Y * D) * S) ((P' - D - X₁ + Y * D) * (A / D + S))
    have h2 := abs_sub (M' - A - X₂ + Y * A) ((X₁ - Y * D) * S)
    rw [abs_mul] at h1 h2
    have h3 : |P' - D - X₁ + Y * D| * |A / D + S| ≤ eP * |A / D + S| :=
      mul_le_mul_of_nonneg_right hP (abs_nonneg _)
    linarith
  have hK : 0 ≤ eM + |X₁ - Y * D| * |S| + eP * |A / D + S| := by positivity
  calc
    _ ≤ (eM + |X₁ - Y * D| * |S| + eP * |A / D + S|) / P' :=
      div_le_div_of_nonneg_right hnum hP'pos.le
    _ ≤ (eM + |X₁ - Y * D| * |S| + eP * |A / D + S|) / (D / 2) :=
      div_le_div_of_nonneg_left hK (half_pos hD) hDen
    _ = _ := by
      rw [div_div_eq_mul_div]
      ring

/-- The first-order sum is a covariance-type sum. -/
theorem first_order_sum_eq {ι : Type*} [Fintype ι] (β M1 M2 : ι → ℝ) (A D : ℝ) :
    (∑ i, β i * M2 i) / D - A / D * (∑ i, β i * M1 i) / D =
      ∑ i, β i * (M2 i / D - M1 i / D * (A / D)) := by
  rw [Finset.sum_div, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Two bounded-by-`b` and bounded-by-`c` families have a bounded product sum. -/
theorem abs_sum_mul_le' {ι : Type*} [Fintype ι] (f g : ι → ℝ) (b c : ℝ)
    (hf : ∀ i, |f i| ≤ b) (hg : ∀ i, |g i| ≤ c) :
    |∑ i, f i * g i| ≤ (Fintype.card ι : ℝ) * (b * c) := by
  calc
    _ ≤ ∑ i, |f i * g i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, b * c := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (hf i) (hg i) (abs_nonneg _) ((abs_nonneg _).trans (hf i))
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Difference of two products with bounded factors. -/
theorem abs_mul_sub_mul_le (a a' b b' Ka Kb : ℝ) (ha : |a| ≤ Ka) (hb' : |b'| ≤ Kb) :
    |a * b - a' * b'| ≤ Ka * |b - b'| + Kb * |a - a'| := by
  have h : a * b - a' * b' = a * (b - b') + (a - a') * b' := by ring
  rw [h]
  calc
    _ ≤ |a * (b - b')| + |(a - a') * b'| := abs_add_le _ _
    _ = |a| * |b - b'| + |a - a'| * |b'| := by rw [abs_mul, abs_mul]
    _ ≤ Ka * |b - b'| + |a - a'| * Kb :=
      add_le_add (mul_le_mul_of_nonneg_right ha (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hb' (abs_nonneg _))
    _ = _ := by ring

end MajorityDynamics.Idealized.LinearResponse
