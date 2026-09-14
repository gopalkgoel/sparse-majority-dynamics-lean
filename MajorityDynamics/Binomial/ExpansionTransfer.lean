import MajorityDynamics.Binomial.WindowExpansion
import MajorityDynamics.Analysis.CovarianceError

/-! # Transfer the common-window expansion to actual unconditioned laws -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace MajorityDynamics.Binomial.Approximation

variable {ι : Type*} [Fintype ι]

theorem integral_abs_le_of_ae_bound (η : ι → ℕ) (q : ι → Probability)
    (f : (ι → ℕ) → ℝ) (H : ℝ) (hf : ∀ᵐ a ∂law η q, |f a| ≤ H) :
    |∫ a, f a ∂law η q| ≤ H := by
  calc
    _ ≤ ∫ a, |f a| ∂law η q := abs_integral_le_integral_abs
    _ ≤ ∫ _a, H ∂law η q :=
      integral_mono_ae (integrable_law η q f).abs (integrable_const H) hf
    _ = H := by simp

/-- Apply a proved finite-window covariance expansion to full expectations.
The discarded masses are those of the actual two product-binomial laws. -/
theorem expansion_transfer (η₀ η₁ : ι → ℕ) (q₀ q₁ : ι → Probability)
    (S : Finset (ι → ℕ)) (hS₀ : 0 < (law η₀ q₀).real S) (hS₁ : 0 < (law η₁ q₁).real S)
    (f z : (ι → ℕ) → ℝ) (G Z b e : ℝ) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hb : 0 ≤ b)
    (hbZ : b ≤ Z)
    (hfS : ∀ a ∈ S, |f a| ≤ G) (hzS : ∀ a ∈ S, |z a| ≤ b)
    (hf₀ : ∀ᵐ a ∂law η₀ q₀, |f a| ≤ G) (hf₁ : ∀ᵐ a ∂law η₁ q₁, |f a| ≤ G)
    (hz₀ : ∀ᵐ a ∂law η₀ q₀, |z a| ≤ Z)
    (hwindow : |finiteExpectation η₁ q₁ S f -
      (finiteExpectation η₀ q₀ S f + finiteExpectation η₀ q₀ S (fun a => z a * f a) -
        finiteExpectation η₀ q₀ S z * finiteExpectation η₀ q₀ S f)| ≤ e) :
    |(∫ a, f a ∂law η₁ q₁) -
      ((∫ a, f a ∂law η₀ q₀) + (∫ a, z a * f a ∂law η₀ q₀) -
        (∫ a, z a ∂law η₀ q₀) * (∫ a, f a ∂law η₀ q₀))| ≤
      e + 2 * G * (law η₁ q₁).real (S : Set (ι → ℕ))ᶜ +
        2 * G * (1 + b + 2 * Z) * (law η₀ q₀).real (S : Set (ι → ℕ))ᶜ := by
  have hnew := finiteExpectation_truncation_error η₁ q₁ S hS₁ f G hfS
    (ae_restrict_of_ae hf₁)
  have hold := finiteExpectation_truncation_error η₀ q₀ S hS₀ f G hfS
    (ae_restrict_of_ae hf₀)
  have hzS' : ∀ a ∈ S, |z a| ≤ Z := fun a ha => (hzS a ha).trans hbZ
  have hzfS : ∀ a ∈ S, |z a * f a| ≤ Z * G := by
    intro a ha
    rw [abs_mul]
    exact mul_le_mul (hzS' a ha) (hfS a ha) (abs_nonneg _) hZ
  have hzf₀ : ∀ᵐ a ∂law η₀ q₀, |z a * f a| ≤ Z * G := by
    filter_upwards [hz₀, hf₀] with a hza hfa
    rw [abs_mul]
    exact mul_le_mul hza hfa (abs_nonneg _) hZ
  have hcross := finiteExpectation_truncation_error η₀ q₀ S hS₀ (fun a => z a * f a)
    (Z * G) hzfS (ae_restrict_of_ae hzf₀)
  have hmean := finiteExpectation_truncation_error η₀ q₀ S hS₀ z Z hzS'
    (ae_restrict_of_ae hz₀)
  have h := Analysis.covariance_expansion_transfer _ _ _ _ _ _ _ _ G b e _ _ _ _ hG hb
    (integral_abs_le_of_ae_bound η₀ q₀ f G hf₀) (finiteExpectation_abs_le η₀ q₀ S hS₀ z b hzS)
    hwindow hnew hold hcross hmean
  convert h using 1
  ring

end MajorityDynamics.Binomial.Approximation
