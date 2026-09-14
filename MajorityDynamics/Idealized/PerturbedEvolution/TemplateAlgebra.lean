import MajorityDynamics.Idealized.Process.EvolutionAlgebra
import MajorityDynamics.Idealized.Process.QuotientExpansion
import MajorityDynamics.Idealized.LinearResponse.Basic
import MajorityDynamics.Universal.ResponseAlgebra

/-! Exact identities and quantitative algebra for Steps 4 and 5 of Theorem 5.4.
The reference sizes are rounded, while the reference edge counts are not. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace MajorityDynamics.Idealized.PerturbedEvolution
open Universal Local

theorem gaussianSplitResponse_beta (n : ℕ) (s : History (n + 1)) (b : Bool) :
    LinearResponse.gaussianSplitResponse n s b (WithLp.toLp 2 (β n s)) =
      ε (n + 1) (append s b) / ν n s := by
  have hc := childLaw_regular n s b
  have hh := historyLaw_regular n s
  let := hc.probability
  let := hh.probability
  rw [ε_recursion]
  simp only [B, integral_responseLinear _ hc.memLp_two,
    integral_responseLinear _ hh.memLp_two, LinearResponse.gaussianSplitResponse,
    mul_sub, Finset.sum_sub_distrib]
  ring

/-- Multiplication by the varying parent size, before rounding the reference.
The parent perturbation contributes a lower-order term bounded using only
the fact that the reference split probability is at most one. -/
theorem size_propagation_error {N x x₀ P P₀ v e h τ A B C : ℝ}
    (hx : 0 ≤ x) (hv : v ≠ 0)
    (hP₀ : |P₀| ≤ 1) (hparent : |x - x₀| ≤ A)
    (hsize : |x - N * v| ≤ B)
    (hsplit : |P - P₀ - τ * h * (e / v)| ≤ C) :
    |x * P - x₀ * P₀ - τ * h * N * e| ≤
      A + x * C + B * |τ * h * (e / v)| := by
  have hid : x * P - x₀ * P₀ - τ * h * N * e =
      (x - x₀) * P₀ + x * (P - P₀ - τ * h * (e / v)) +
        (x - N * v) * (τ * h * (e / v)) := by
    field_simp
    ring
  rw [hid]
  calc
    _ ≤ (|(x - x₀) * P₀| + |x * (P - P₀ - τ * h * (e / v))|) +
        |(x - N * v) * (τ * h * (e / v))| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (A * 1 + x * C) + B * |τ * h * (e / v)| := by
      simp only [abs_mul, abs_of_nonneg hx]
      exact add_le_add (add_le_add
        (mul_le_mul hparent hP₀ (abs_nonneg _) ((abs_nonneg _).trans hparent))
        (mul_le_mul_of_nonneg_left hsplit hx))
        (mul_le_mul_of_nonneg_right hsize (by positivity))
    _ = _ := by ring

/-- The literal floor used by Theorem 5.2 costs less than one vertex. -/
theorem size_error_floor {x y z E : ℝ} (hy : 0 ≤ y)
    (h : |x - y - z| ≤ E) : |x - (⌊y⌋₊ : ℝ) - z| ≤ E + 1 := by
  have hfloor : |y - (⌊y⌋₊ : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Nat.floor_le hy))]
    have hf := Nat.lt_floor_add_one y
    linarith
  calc
    _ = |(x - y - z) + (y - (⌊y⌋₊ : ℝ))| := by congr 1; ring
    _ ≤ |x - y - z| + |y - (⌊y⌋₊ : ℝ)| := abs_add_le _ _
    _ ≤ E + 1 := add_le_add h hfloor

/-- The actual local half-edge formula, in the E.4 notation. -/
theorem halfEdges_eq_childMean {n : ℕ} (sizes : Sizes n) (q : Tilt n)
    (u : History (n + 2)) (t : History (n + 1)) :
    templateHalfEdges sizes q u t = templateSizes sizes q u *
      LinearResponse.childMean sizes (parent u) (last u) (q (parent u)) t :=
  Process.templateHalfEdges_eq_size_mul_childMean sizes q u t

/-- Exact factorization behind Step 5. Positivity conditions are explicit;
no approximate quotient identity is assumed. -/
theorem edge_ratio_identity {x y a b m x₀ y₀ a₀ b₀ m₀ : ℝ}
    (hx₀ : x₀ ≠ 0) (hy₀ : y₀ ≠ 0) (ha₀ : a₀ ≠ 0)
    (hb₀ : b₀ ≠ 0) (hm₀ : m₀ ≠ 0) :
    (x * a * (y * b) / m) = (x₀ * a₀ * (y₀ * b₀) / m₀) *
      (x / x₀) * (y / y₀) * (a / a₀) * (b / b₀) * (m₀ / m) := by
  field_simp

/-- Operator bound for the Gaussian split functional; its constant depends
only on the universal level, row, and child. -/
theorem gaussianSplitResponse_error {n : ℕ} (s : History (n + 1)) (b : Bool)
    (σ σ₀ : Row (n + 1)) {r : ℝ} (hr : ∀ t, |σ t - σ₀ t| ≤ r) :
    |LinearResponse.gaussianSplitResponse n s b σ -
      LinearResponse.gaussianSplitResponse n s b σ₀| ≤
    (|ν (n + 1) (append s b) / ν n s| *
      ∑ t, |(∫ x, x t ∂childLaw n s b) - (∫ x, x t ∂historyLaw n s)|) * r := by
  let d := fun t => (∫ x, x t ∂childLaw n s b) - (∫ x, x t ∂historyLaw n s)
  have hid : LinearResponse.gaussianSplitResponse n s b σ -
      LinearResponse.gaussianSplitResponse n s b σ₀ =
      (ν (n + 1) (append s b) / ν n s) * ∑ t, (σ t - σ₀ t) * d t := by
    simp only [LinearResponse.gaussianSplitResponse, d, sub_mul,
      Finset.sum_sub_distrib, mul_sub]
    ring
  rw [hid, abs_mul]
  calc
    _ ≤ |ν (n + 1) (append s b) / ν n s| * ∑ t, |(σ t - σ₀ t) * d t| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
    _ ≤ |ν (n + 1) (append s b) / ν n s| * ∑ t, r * |d t| := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply Finset.sum_le_sum
      intro t _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hr t) (abs_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- Removal of the E.4 normalization, retaining both independent error
sources: the E.4 remainder and the distance of the solved parameter from β. -/
theorem split_response_error {P P₀ h g g₀ E F : ℝ} (hh : 0 < h)
    (hresponse : |(P - P₀) / h - g| ≤ E) (hg : |g - g₀| ≤ F) :
    |P - P₀ - h * g₀| ≤ h * (E + F) := by
  have hid : P - P₀ - h * g₀ = h * (((P - P₀) / h - g) + (g - g₀)) := by
    field_simp
    ring
  rw [hid, abs_mul, abs_of_pos hh]
  exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hresponse hg)) hh.le

end MajorityDynamics.Idealized.PerturbedEvolution
