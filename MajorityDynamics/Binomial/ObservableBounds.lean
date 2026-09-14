import MajorityDynamics.Binomial.RectangleWindow

/-! # Bounds and integral identities for the actual A.2 observables -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace MajorityDynamics.Binomial.Approximation

variable {d r : ℕ}

theorem monomial_abs_le (c : ℝ) (e : Fin d → ℕ) (x : Fin d → ℝ) (R : ℝ)
    (h : ∀ i, |x i| ≤ R) : |monomial c e x| ≤ |c| * R ^ (∑ i, e i) := by
  rw [monomial, abs_mul, Finset.abs_prod]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
  calc
    ∏ i, |x i ^ e i| ≤ ∏ i, R ^ e i := Finset.prod_le_prod
      (fun i _ => abs_nonneg _) (fun i _ => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (h i) _)
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

def restrictedObservable (M : Fin r → Fin d → ℝ) (strict : Fin r → Bool)
    (p : Probability) (ref : Fin d → ℕ) (f : (Fin d → ℝ) → ℝ) (a : Fin d → ℕ) : ℝ :=
  (inequalityEvent M strict).indicator (fun a => f (centered p ref a)) a

theorem restrictedObservable_abs_le (M : Fin r → Fin d → ℝ) (strict : Fin r → Bool)
    (p : Probability) (ref : Fin d → ℕ) (c : ℝ) (e : Fin d → ℕ)
    (R : ℝ) (hR : 0 ≤ R) (a : Fin d → ℕ) (ha : ∀ i, |centered p ref a i| ≤ R) :
    |restrictedObservable M strict p ref (monomial c e) a| ≤ |c| * R ^ (∑ i, e i) := by
  classical
  by_cases h : a ∈ inequalityEvent M strict
  · simpa [restrictedObservable, h] using monomial_abs_le c e (centered p ref a) R ha
  · simp only [restrictedObservable, Set.indicator_of_notMem h, abs_zero]
    positivity

theorem integral_restrictedObservable (M : Fin r → Fin d → ℝ) (strict : Fin r → Bool)
    (p : Probability) (ref η : Fin d → ℕ) (q : Fin d → Probability)
    (f : (Fin d → ℝ) → ℝ) :
    (∫ a, restrictedObservable M strict p ref f a ∂law η q) = moment M strict p ref η q f := by
  exact integral_indicator (Set.to_countable _).measurableSet

theorem linearTilt_abs_le (β : Fin d → ℝ) (x : Fin d → ℝ) (R : ℝ)
    (h : ∀ i, |x i| ≤ R) : |∑ i, β i * x i| ≤ d * ‖β‖ * R := by
  calc
    _ ≤ ∑ i, |β i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ‖β‖ * R := Finset.sum_le_sum fun i _ => by
      rw [abs_mul]
      exact mul_le_mul (norm_le_pi_norm β i) (h i) (abs_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

theorem integral_linearTilt (η : Fin d → ℕ) (q : Fin d → Probability)
    (β : Fin d → ℝ) (x : (Fin d → ℕ) → Fin d → ℝ) (f : (Fin d → ℕ) → ℝ) :
    (∫ a, (∑ i, β i * x a i) * f a ∂law η q) =
      ∑ i, β i * (∫ a, x a i * f a ∂law η q) := by
  simp only [Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun i _ => integrable_law η q _)]
  simp only [integral_const_mul]

end MajorityDynamics.Binomial.Approximation
