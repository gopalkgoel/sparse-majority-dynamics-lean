import MajorityDynamics.Binomial.ProductLikelihood
import MajorityDynamics.Analysis.ApproximateFiniteTilt

/-! # Different-trial binomial expansion on a shared finite window -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace MajorityDynamics.Binomial.Approximation
open Analysis.FiniteTiltEstimate

variable {ι : Type*} [Fintype ι]

def finiteExpectation (η : ι → ℕ) (q : ι → Probability)
    (S : Finset (ι → ℕ)) (f : (ι → ℕ) → ℝ) : ℝ :=
  average S (Analysis.FiniteTiltEstimate.normalize S (ambientMass η q)) f

theorem finiteExpectation_eq_integral (η : ι → ℕ) (q : ι → Probability)
    (S : Finset (ι → ℕ)) (f : (ι → ℕ) → ℝ) :
    finiteExpectation η q S f = ∫ a, f a ∂ProbabilityTheory.cond (law η q) (S : Set (ι → ℕ)) := by
  classical
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, ← measureReal_def,
    ← sum_measureReal_singleton, integral_finite_event]
  simp only [law_singleton_ambient, smul_eq_mul, finiteExpectation, Analysis.FiniteTiltEstimate.average, Analysis.FiniteTiltEstimate.normalize,
    Finset.mul_sum, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro a _
  ring

def productTilt (η₀ η₁ : ι → ℕ) (c : ι → ℝ) (q₀ q₁ : ι → Probability)
    (a : ι → ℕ) : ℝ :=
  ∑ i, scalarTiltDifference (η₀ i) (η₁ i) (c i) (q₀ i) (q₁ i) * ((a i : ℝ) - c i)

theorem finiteExpectation_eq_div (η : ι → ℕ) (q : ι → Probability)
    (S : Finset (ι → ℕ)) (f : (ι → ℕ) → ℝ) :
    finiteExpectation η q S f = (∫ a in (S : Set (ι → ℕ)), f a ∂law η q) / (law η q).real S := by
  rw [integral_finite_event, ← sum_measureReal_singleton]
  simp only [law_singleton_ambient, finiteExpectation, Analysis.FiniteTiltEstimate.average,
    Analysis.FiniteTiltEstimate.normalize, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem finiteExpectation_abs_le (η : ι → ℕ) (q : ι → Probability)
    (S : Finset (ι → ℕ)) (hS : 0 < (law η q).real S) (f : (ι → ℕ) → ℝ)
    (H : ℝ) (hf : ∀ a ∈ S, |f a| ≤ H) : |finiteExpectation η q S f| ≤ H := by
  have hsum : (law η q).real S = ∑ a ∈ S, ambientMass η q a := by
    rw [← sum_measureReal_singleton]
    simp only [law_singleton_ambient]
  rw [hsum] at hS
  apply abs_average_le S (Analysis.FiniteTiltEstimate.normalize S (ambientMass η q)) f
    _ (normalize_sum S (ambientMass η q) hS.ne') H hf
  intro a _
  apply div_nonneg _ hS.le
  rw [← law_singleton_ambient]
  exact measureReal_nonneg

/-- Converting a normalized finite-window expectation to the full expectation
costs at most twice the global observable bound times the discarded mass. -/
theorem finiteExpectation_truncation_error (η : ι → ℕ) (q : ι → Probability)
    (S : Finset (ι → ℕ)) (hS : 0 < (law η q).real S) (f : (ι → ℕ) → ℝ)
    (H : ℝ) (hfS : ∀ a ∈ S, |f a| ≤ H)
    (hf : ∀ᵐ a ∂(law η q).restrict (S : Set (ι → ℕ))ᶜ, |f a| ≤ H) :
    |(∫ a, f a ∂law η q) - finiteExpectation η q S f| ≤
      2 * H * (law η q).real (S : Set (ι → ℕ))ᶜ := by
  classical
  have hb := finiteExpectation_abs_le η q S hS f H hfS
  have he := integral_truncation_le η q (S : Set (ι → ℕ)) f H hf
  have hmass : (law η q).real S + (law η q).real (S : Set (ι → ℕ))ᶜ = 1 := by
    simpa using measureReal_add_measureReal_compl (μ := law η q) S.measurableSet
  have hid : (∫ a in (S : Set (ι → ℕ)), f a ∂law η q) =
      finiteExpectation η q S f * (law η q).real S := by
    rw [finiteExpectation_eq_div, div_mul_cancel₀ _ hS.ne']
  have hd : |(∫ a in (S : Set (ι → ℕ)), f a ∂law η q) - finiteExpectation η q S f| ≤
      H * (law η q).real (S : Set (ι → ℕ))ᶜ := by
    rw [hid, ← mul_sub_one, abs_mul]
    have hsub : (law η q).real S - 1 = -(law η q).real (S : Set (ι → ℕ))ᶜ := by linarith
    rw [hsub, abs_neg, abs_of_nonneg measureReal_nonneg]
    exact mul_le_mul_of_nonneg_right hb measureReal_nonneg
  calc
    _ ≤ |(∫ a, f a ∂law η q) - ∫ a in (S : Set (ι → ℕ)), f a ∂law η q| +
        |(∫ a in (S : Set (ι → ℕ)), f a ∂law η q) - finiteExpectation η q S f| := abs_sub_le _ _ _
    _ ≤ H * (law η q).real (S : Set (ι → ℕ))ᶜ + H * (law η q).real (S : Set (ι → ℕ))ᶜ :=
      add_le_add he hd
    _ = _ := by ring

def likelihoodErrorBound (η₀ η₁ : ι → ℕ) (c L : ι → ℝ) : ℝ :=
  ∑ i, 4 * L i ^ 2 * (1 / ((η₀ i : ℝ) - c i) + 1 / ((η₁ i : ℝ) - c i))

/-- Quantitative expansion of two actual binomial laws conditioned on the
same finite window, with distinct trial counts and arbitrary observables.
The final A.2 theorem removes window conditioning using truncation. -/
theorem window_tilt_expansion (η₀ η₁ : ι → ℕ) (c L : ι → ℝ)
    (q₀ q₁ : ι → Probability) (S : Finset (ι → ℕ)) (hS : S.Nonempty)
    (hrect : ∀ a ∈ S, a ∈ rectangle c L)
    (h₀ : ∀ i, c i < η₀ i) (h₁ : ∀ i, c i < η₁ i) (hL : ∀ i, 0 ≤ L i)
    (hL₀ : ∀ i, L i ≤ ((η₀ i : ℝ) - c i) / 2)
    (hL₁ : ∀ i, L i ≤ ((η₁ i : ℝ) - c i) / 2)
    (f : (ι → ℕ) → ℝ) (H b : ℝ) (hH : 0 ≤ H) (hb : 0 ≤ b)
    (hbsmall : b ≤ 1 / 4) (hδsmall : likelihoodErrorBound η₀ η₁ c L ≤ 1 / 4)
    (hf : ∀ a ∈ S, |f a| ≤ H) (hz : ∀ a ∈ S, |productTilt η₀ η₁ c q₀ q₁ a| ≤ b) :
    |finiteExpectation η₁ q₁ S f -
      (finiteExpectation η₀ q₀ S f +
        finiteExpectation η₀ q₀ S (fun a => productTilt η₀ η₁ c q₀ q₁ a * f a) -
        finiteExpectation η₀ q₀ S (productTilt η₀ η₁ c q₀ q₁) * finiteExpectation η₀ q₀ S f)| ≤
      12 * H * b ^ 2 + 8 * H * likelihoodErrorBound η₀ η₁ c L := by
  have hsupp (η : ι → ℕ) (hη : ∀ i, c i < η i)
      (hηL : ∀ i, L i ≤ ((η i : ℝ) - c i) / 2) (a : ι → ℕ) (ha : a ∈ S) :
      ∀ i, a i ≤ η i := by
    intro i
    have hd := hη i
    have hli := hηL i
    have hai := (abs_le.mp (hrect a ha i)).2
    exact_mod_cast (show (a i : ℝ) ≤ η i by linarith)
  have hmass (η : ι → ℕ) (q : ι → Probability) (hη : ∀ i, c i < η i)
      (hηL : ∀ i, L i ≤ ((η i : ℝ) - c i) / 2) : ∀ a ∈ S, 0 < ambientMass η q a := by
    intro a ha
    rw [ambientMass_eq_prod_pointMass]
    exact Finset.prod_pos fun i _ => pointMass_pos (hsupp η hη hηL a ha i) (q i)
  obtain ⟨a₀, ha₀⟩ := hS
  have hδ : 0 ≤ likelihoodErrorBound η₀ η₁ c L := by
    apply Finset.sum_nonneg
    intro i _
    have hd₀ := sub_pos.mpr (h₀ i)
    have hd₁ := sub_pos.mpr (h₁ i)
    positivity
  apply normalized_log_tilt_expansion S a₀ ha₀ (ambientMass η₀ q₀) (ambientMass η₁ q₁)
    f (productTilt η₀ η₁ c q₀ q₁) (hmass η₀ q₀ h₀ hL₀) (hmass η₁ q₁ h₁ hL₁)
    H b (likelihoodErrorBound η₀ η₁ c L) hH hb hδ hbsmall hδsmall hf hz
  intro a ha
  have h := product_changing_trials_log_error η₀ η₁ c L q₀ q₁ h₀ h₁ hL hL₀ hL₁
    a₀ a (hrect a₀ ha₀) (hrect a ha)
  rw [productLikelihoodRemainder_eq η₀ η₁ c q₀ q₁ a (hsupp η₀ h₀ hL₀ a ha) (hsupp η₁ h₁ hL₁ a ha),
    productLikelihoodRemainder_eq η₀ η₁ c q₀ q₁ a₀ (hsupp η₀ h₀ hL₀ a₀ ha₀) (hsupp η₁ h₁ hL₁ a₀ ha₀)] at h
  exact h

end MajorityDynamics.Binomial.Approximation
