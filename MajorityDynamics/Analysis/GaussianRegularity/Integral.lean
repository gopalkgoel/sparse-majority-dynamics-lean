import MajorityDynamics.Analysis.ConditionalGaussian.Partition
import Mathlib.Analysis.Calculus.MeanValue

/-! # Integrating uniform Lipschitz envelopes

The estimates here are uniform in the measurable conditioning region. They
allow Gaussian parameter estimates to be integrated without differentiating
an indicator or assuming that the region is bounded.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology NNReal

namespace MajorityDynamics.Analysis.GaussianRegularity

variable {P X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [MeasurableSpace X] {μ : Measure X}

omit [NormedSpace ℝ P] in
/-- An integrable pointwise Lipschitz envelope integrates to a Lipschitz
constant. No finite-measure assumption is required. -/
theorem lipschitzOnWith_integral_of_envelope {U : Set P}
    {F : P → X → ℝ} {B : X → ℝ}
    (hB : Integrable B μ) (hBpos : ∀ x, 0 ≤ B x)
    (hF : ∀ p ∈ U, Integrable (F p) μ)
    (hbound : ∀ p ∈ U, ∀ q ∈ U, ∀ x,
      ‖F p x - F q x‖ ≤ B x * ‖p - q‖) :
    LipschitzOnWith (Real.toNNReal (∫ x, B x ∂μ))
      (fun p => ∫ x, F p x ∂μ) U := by
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro p hp q hq
  simp only [Real.coe_toNNReal _ (integral_nonneg hBpos)]
  rw [← integral_sub (hF p hp) (hF q hq)]
  calc
    ‖∫ x, F p x - F q x ∂μ‖ ≤ ∫ x, B x * ‖p - q‖ ∂μ :=
      norm_integral_le_of_norm_le (hB.mul_const _) (ae_of_all _ (hbound p hp q hq))
    _ = (∫ x, B x ∂μ) * ‖p - q‖ := integral_mul_const _ _

/-- A common derivative envelope on a convex parameter set gives the
pointwise estimate required by `lipschitzOnWith_integral_of_envelope`. -/
theorem lipschitzOnWith_integral_of_fderiv_envelope {U : Set P}
    (hU : Convex ℝ U) {F : P → X → ℝ} {B : X → ℝ}
    (hB : Integrable B μ) (hBpos : ∀ x, 0 ≤ B x)
    (hF : ∀ p ∈ U, Integrable (F p) μ)
    (hdiff : ∀ x, ∀ p ∈ U, DifferentiableAt ℝ (fun q => F q x) p)
    (hbound : ∀ x, ∀ p ∈ U, ‖fderiv ℝ (fun q => F q x) p‖ ≤ B x) :
    LipschitzOnWith (Real.toNNReal (∫ x, B x ∂μ))
      (fun p => ∫ x, F p x ∂μ) U := by
  apply lipschitzOnWith_integral_of_envelope hB hBpos hF
  intro p hp q hq x
  exact Convex.norm_image_sub_le_of_norm_fderiv_le (hdiff x) (hbound x) hU hq hp

/-- A common scalar envelope controls the difference of finite products. -/
theorem norm_prod_sub_prod_le_envelope {ι : Type*} (s : Finset ι)
    (f g E : ι → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hE : ∀ i ∈ s, 0 ≤ E i)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ E i) (hg : ∀ i ∈ s, ‖g i‖ ≤ E i)
    (hd : ∀ i ∈ s, ‖f i - g i‖ ≤ E i * δ) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ (s.card : ℝ) * (∏ i ∈ s, E i) * δ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hs : ∀ j ∈ s, j ∈ insert i s := fun j hj => Finset.mem_insert_of_mem hj
    have hp : ‖∏ j ∈ s, g j‖ ≤ ∏ j ∈ s, E j := by
      rw [norm_prod]
      exact Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j hj => hg j (hs j hj))
    have hprod : 0 ≤ ∏ j ∈ s, E j := Finset.prod_nonneg (fun j hj => hE j (hs j hj))
    have hn : 0 ≤ (s.card : ℝ) * (∏ j ∈ s, E j) * δ := by positivity
    have hb := ih (fun j hj => hE j (hs j hj)) (fun j hj => hf j (hs j hj))
      (fun j hj => hg j (hs j hj)) (fun j hj => hd j (hs j hj))
    simp only [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
    calc
      ‖f i * (∏ j ∈ s, f j) - g i * ∏ j ∈ s, g j‖ =
          ‖f i * ((∏ j ∈ s, f j) - ∏ j ∈ s, g j) +
            (f i - g i) * ∏ j ∈ s, g j‖ := by congr 1; ring
      _ ≤ ‖f i‖ * ‖(∏ j ∈ s, f j) - ∏ j ∈ s, g j‖ +
          ‖f i - g i‖ * ‖∏ j ∈ s, g j‖ := by
        simpa only [norm_mul] using norm_add_le
          (f i * ((∏ j ∈ s, f j) - ∏ j ∈ s, g j))
          ((f i - g i) * ∏ j ∈ s, g j)
      _ ≤ E i * ((s.card : ℝ) * (∏ j ∈ s, E j) * δ) +
          (E i * δ) * (∏ j ∈ s, E j) :=
        add_le_add (mul_le_mul (hf i (by simp)) hb (norm_nonneg _) (hE i (by simp)))
          (mul_le_mul (hd i (by simp)) hp (norm_nonneg _) (mul_nonneg (hE i (by simp)) hδ))
      _ = ((s.card : ℝ) + 1) * (E i * ∏ j ∈ s, E j) * δ := by ring

/-- Every polynomial norm moment is integrable against a nondegenerate
Gaussian envelope, including on unbounded conditioning regions. -/
theorem integrable_norm_pow_mul_gaussian {d : ℕ} {c : ℝ} (hc : 0 < c) (n : ℕ) :
    Integrable (fun x : ConditionalGaussian.Space d =>
      ‖x‖ ^ n * Real.exp (-c * ‖x‖ ^ 2)) := by
  let C : ℝ := (n.factorial : ℝ) * Real.exp (1 / (2 * c))
  apply ((ConditionalGaussian.integrable_gaussian_envelope
    (d := d) (by positivity : 0 < c / 2)).const_mul C).mono'
    (by fun_prop)
  apply ae_of_all
  intro x
  rw [Real.norm_of_nonneg (by positivity)]
  have hp : ‖x‖ ^ n ≤ (n.factorial : ℝ) * Real.exp ‖x‖ := by
    have hf : (0 : ℝ) < n.factorial := by positivity
    exact (div_le_iff₀ hf).mp
      (Real.pow_div_factorial_le_exp _ (norm_nonneg _) n) |>.trans_eq (mul_comm _ _)
  have hquad : ‖x‖ - c * ‖x‖ ^ 2 ≤ 1 / (2 * c) - c / 2 * ‖x‖ ^ 2 := by
    have hcn : c ≠ 0 := ne_of_gt hc
    have heq : 2 * c * (1 / (2 * c)) = 1 := by field_simp
    nlinarith [sq_nonneg (c * ‖x‖ - 1), sq_nonneg ‖x‖]
  calc
    ‖x‖ ^ n * Real.exp (-c * ‖x‖ ^ 2) ≤
        ((n.factorial : ℝ) * Real.exp ‖x‖) * Real.exp (-c * ‖x‖ ^ 2) := by gcongr
    _ = (n.factorial : ℝ) * Real.exp (‖x‖ - c * ‖x‖ ^ 2) := by rw [sub_eq_add_neg, Real.exp_add, neg_mul]; ring
    _ ≤ (n.factorial : ℝ) * Real.exp (1 / (2 * c) - c / 2 * ‖x‖ ^ 2) := by gcongr
    _ = C * Real.exp (-(c / 2) * ‖x‖ ^ 2) := by
      simp only [C, sub_eq_add_neg, Real.exp_add, neg_mul, mul_assoc]

/-- A quadratic scalar prefactor is absorbed by halving the Gaussian decay. -/
theorem quadratic_mul_gaussian_le {c : ℝ} (hc : 0 < c) (x : ℝ) :
    (1 + x ^ 2) * Real.exp (-c * x ^ 2) ≤
      (1 + 2 / c) * Real.exp (-(c / 2) * x ^ 2) := by
  have hexp : 1 ≤ Real.exp (c / 2 * x ^ 2) := Real.one_le_exp (by positivity)
  have hlin := Real.add_one_le_exp (c / 2 * x ^ 2)
  have hdiv : c * (2 / c) = 2 := by field_simp
  have hpoly : 1 + x ^ 2 ≤ (1 + 2 / c) * Real.exp (c / 2 * x ^ 2) := by
    have haux : x ^ 2 ≤ (2 / c) * Real.exp (c / 2 * x ^ 2) := by
      apply (mul_le_mul_iff_right₀ hc).mp
      calc
        c * x ^ 2 ≤ 2 * Real.exp (c / 2 * x ^ 2) := by nlinarith
        _ = c * (2 / c * Real.exp (c / 2 * x ^ 2)) := by field_simp
    nlinarith
  calc
    (1 + x ^ 2) * Real.exp (-c * x ^ 2) ≤
        ((1 + 2 / c) * Real.exp (c / 2 * x ^ 2)) * Real.exp (-c * x ^ 2) := by gcongr
    _ = (1 + 2 / c) * Real.exp (-(c / 2) * x ^ 2) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- Products of scalar Gaussian envelopes form a radial Gaussian envelope. -/
theorem prod_gaussian_envelope {d : ℕ} (C c : ℝ) (x : ConditionalGaussian.Space d) :
    (∏ i : Fin d, C * Real.exp (-c * (x i) ^ 2)) =
      C ^ d * Real.exp (-c * ‖x‖ ^ 2) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin, ← Real.exp_sum]
  rw [← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq]

end MajorityDynamics.Analysis.GaussianRegularity
