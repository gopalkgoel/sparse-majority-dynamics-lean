import MajorityDynamics.Idealized.RowLimits.Events
import MajorityDynamics.Idealized.RowLimits.Basic
import MajorityDynamics.Binomial.ApproximationStatements

/-! The finite family of degree at most two observables in E.3, and the
exact algebra converting centered raw moments to means and covariances. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace MajorityDynamics.Idealized.RowLimits
attribute [local instance] Classical.propDecidable

/-- Constant, coordinate, and coordinate-product observables. -/
abbrev MomentKind (d : ℕ) := Unit ⊕ (Fin d ⊕ (Fin d × Fin d))

def momentExponent {d : ℕ} : MomentKind d → Fin d → ℕ
  | .inl _ => fun _ => 0
  | .inr (.inl i) => fun j => if j = i then 1 else 0
  | .inr (.inr (i, j)) => fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0)

def momentValue {d : ℕ} : MomentKind d → (Fin d → ℝ) → ℝ
  | .inl _ => fun _ => 1
  | .inr (.inl i) => fun x => x i
  | .inr (.inr (i, j)) => fun x => x i * x j

@[simp] theorem moment_monomial {d : ℕ} (o : MomentKind d) (x : Fin d → ℝ) :
    Binomial.Approximation.monomial 1 (momentExponent o) x = momentValue o x := by
  rcases o with u | (i | ⟨i, j⟩)
  · simp [Binomial.Approximation.monomial, momentExponent, momentValue]
  · simp [Binomial.Approximation.monomial, momentExponent, momentValue]
  · simp only [Binomial.Approximation.monomial, momentExponent, momentValue,
      pow_add, Finset.prod_mul_distrib, one_mul]
    simp

theorem moment_degree_le_two {d : ℕ} (o : MomentKind d) :
    ∑ i, momentExponent o i ≤ 2 := by
  rcases o with u | (i | ⟨i, j⟩)
  · simp [momentExponent]
  · simp [momentExponent]
  · simp [momentExponent, Finset.sum_add_distrib]

/-- Unnormalized integration on a finite binomial event is the literal mass sum. -/
theorem binomial_integral_event {ι : Type*} [Fintype ι]
    (η : ι → ℕ) (q : ι → Binomial.Probability) (S : Finset (Binomial.Box η))
    (f : (ι → ℕ) → ℝ) :
    (∫ a in Binomial.event S, f a ∂Binomial.law η q) =
      ∑ a ∈ S, Binomial.mass η q a * f (Binomial.point a) := by
  classical
  rw [Binomial.event, ← Finset.coe_image,
    MeasureTheory.setIntegral_finset _ MeasureTheory.IntegrableOn.finset]
  rw [Finset.sum_image (fun _ _ _ _ h => Binomial.point_injective η h)]
  simp only [Binomial.law_singleton, smul_eq_mul]

section FiniteAlgebra
variable {α : Type*} (S : Finset α) (w x y : α → ℝ) (c d a : ℝ)

/-- Centering and scaling an unnormalized first moment. -/
theorem weighted_centered_first :
    (∑ z ∈ S, w z * ((x z - c) / a)) =
      ((∑ z ∈ S, w z * x z) - c * ∑ z ∈ S, w z) / a := by
  simp_rw [← mul_div_assoc, ← Finset.sum_div]
  congr 1
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

/-- Centering and scaling an unnormalized second moment. -/
theorem weighted_centered_second :
    (∑ z ∈ S, w z * (((x z - c) / a) * ((y z - d) / a))) =
      ((∑ z ∈ S, w z * (x z * y z)) - d * (∑ z ∈ S, w z * x z) -
        c * (∑ z ∈ S, w z * y z) + c * d * (∑ z ∈ S, w z)) / a ^ 2 := by
  simp_rw [div_mul_div_comm, ← mul_div_assoc, ← Finset.sum_div, pow_two]
  congr 1
  calc
    _ = ∑ z ∈ S, (w z * (x z * y z) - d * (w z * x z) -
        c * (w z * y z) + c * d * w z) := by
      apply Finset.sum_congr rfl
      intro z hz
      ring
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

/-- Positive total mass is needed only for interpreting the normalized mean. -/
theorem weighted_conditional_first (hm : (∑ z ∈ S, w z) ≠ 0) (ha : a ≠ 0) :
    (∑ z ∈ S, w z * ((x z - c) / a)) / (∑ z ∈ S, w z) =
      ((∑ z ∈ S, w z * x z) / (∑ z ∈ S, w z) - c) / a := by
  rw [weighted_centered_first]
  field_simp

/-- Conditional covariance is independent of the centering vector and scales
by the square of the normalization. -/
theorem weighted_conditional_covariance (hm : (∑ z ∈ S, w z) ≠ 0) (ha : a ≠ 0) :
    (∑ z ∈ S, w z * (((x z - c) / a) * ((y z - d) / a))) / (∑ z ∈ S, w z) -
      ((∑ z ∈ S, w z * ((x z - c) / a)) / (∑ z ∈ S, w z)) *
      ((∑ z ∈ S, w z * ((y z - d) / a)) / (∑ z ∈ S, w z)) =
      ((∑ z ∈ S, w z * (x z * y z)) / (∑ z ∈ S, w z) -
        ((∑ z ∈ S, w z * x z) / (∑ z ∈ S, w z)) *
        ((∑ z ∈ S, w z * y z) / (∑ z ∈ S, w z))) / a ^ 2 := by
  rw [weighted_centered_second, weighted_centered_first, weighted_centered_first]
  field_simp
  ring

end FiniteAlgebra
open Universal

variable {n : ℕ}

/-- Unnormalized moment of the normalized binomial row, on a fixed support.
The center is explicit: E.3 first uses `p * trials` and then corrects to `p * sizes`.
-/
def binomialNormalizedMoment (N : ℕ) (p : Binomial.Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (S : Finset (Binomial.Box (Local.trials sizes s)))
    (center : History (n + 1) → ℝ) (scale : ℝ)
    (o : MomentKind (Fintype.card (Fin (n + 1) → Bool))) (σ : Row (n + 1)) : ℝ :=
  ∑ a ∈ S, Binomial.mass (Local.trials sizes s) (rowTilt N p σ) a *
    momentValue o (fun t => (Binomial.vector a t - center t) / scale)

@[simp] theorem binomialNormalizedMoment_zero (N : ℕ) (p : Binomial.Probability)
    (sizes : Local.Sizes n) (s : History (n + 1))
    (S : Finset (Binomial.Box (Local.trials sizes s)))
    (center : History (n + 1) → ℝ) (scale : ℝ) (σ : Row (n + 1)) :
    binomialNormalizedMoment N p sizes s S center scale (.inl ()) σ =
      binomialMass N p sizes s S σ := by
  simp [binomialNormalizedMoment, momentValue, binomialMass, Binomial.eventMass]

theorem binomialNormalizedMoment_mean (N : ℕ) (p : Binomial.Probability)
    (sizes : Local.Sizes n) (s : History (n + 1))
    (S : Finset (Binomial.Box (Local.trials sizes s)))
    (center : History (n + 1) → ℝ) (scale : ℝ) (σ : Row (n + 1))
    (hm : binomialMass N p sizes s S σ ≠ 0) (ha : scale ≠ 0)
    (t : History (n + 1)) :
    binomialNormalizedMoment N p sizes s S center scale (.inr (.inl t)) σ /
      binomialMass N p sizes s S σ =
      (binomialMean N p sizes s S t σ - center t) / scale := by
  exact weighted_conditional_first S
    (fun a => Binomial.mass (Local.trials sizes s) (rowTilt N p σ) a)
    (fun a => Binomial.vector a t) (center t) scale hm ha

theorem binomialNormalizedMoment_covariance (N : ℕ) (p : Binomial.Probability)
    (sizes : Local.Sizes n) (s : History (n + 1))
    (S : Finset (Binomial.Box (Local.trials sizes s)))
    (center : History (n + 1) → ℝ) (scale : ℝ) (σ : Row (n + 1))
    (hm : binomialMass N p sizes s S σ ≠ 0) (ha : scale ≠ 0)
    (t t' : History (n + 1)) :
    binomialNormalizedMoment N p sizes s S center scale (.inr (.inr (t, t'))) σ /
      binomialMass N p sizes s S σ -
      (binomialNormalizedMoment N p sizes s S center scale (.inr (.inl t)) σ /
        binomialMass N p sizes s S σ) *
      (binomialNormalizedMoment N p sizes s S center scale (.inr (.inl t')) σ /
        binomialMass N p sizes s S σ) =
      binomialCovariance N p sizes s S t t' σ / scale ^ 2 := by
  exact weighted_conditional_covariance S
    (fun a => Binomial.mass (Local.trials sizes s) (rowTilt N p σ) a)
    (fun a => Binomial.vector a t) (fun a => Binomial.vector a t')
    (center t) (center t') scale hm ha

/-- The unrestricted mixed event and the finite support formula have exactly
identical raw moments under the actual product-binomial law. -/
theorem binomialNormalizedMoment_eq_integral (N : ℕ) (p : Binomial.Probability)
    (sizes : Local.Sizes n) (s : History (n + 1))
    (S : Finset (Binomial.Box (Local.trials sizes s)))
    (E : Set (History (n + 1) → ℕ))
    (hS : S = Finset.univ.filter (fun a => Binomial.point a ∈ E))
    (center : History (n + 1) → ℝ) (scale : ℝ)
    (o : MomentKind (Fintype.card (Fin (n + 1) → Bool))) (σ : Row (n + 1)) :
    binomialNormalizedMoment N p sizes s S center scale o σ =
      ∫ a in E, momentValue o (fun t => ((a t : ℝ) - center t) / scale)
        ∂Binomial.law (Local.trials sizes s) (rowTilt N p σ) := by
  subst S
  rw [← Measure.restrict_congr_set
    (Binomial.filter_event_ae_eq (Local.trials sizes s) (rowTilt N p σ) E)]
  rw [binomial_integral_event]
  simp only [binomialNormalizedMoment, Binomial.vector, Binomial.point]
  congr 1
  ext a
  simp

theorem binomialNormalizedMoment_history_integral (N : ℕ) (p : Binomial.Probability)
    (sizes : Local.Sizes n) (s : History (n + 1))
    (center : History (n + 1) → ℝ) (scale : ℝ)
    (o : MomentKind (Fintype.card (Fin (n + 1) → Bool))) (σ : Row (n + 1)) :
    binomialNormalizedMoment N p sizes s (Local.historySupport sizes s) center scale o σ =
      ∫ a in Binomial.inequalityEvent (fun r t => (historyIntegerMatrix s r t : ℝ))
        (historyStrict s), momentValue o (fun t => ((a t : ℝ) - center t) / scale)
        ∂Binomial.law (Local.trials sizes s) (rowTilt N p σ) := by
  apply binomialNormalizedMoment_eq_integral
  classical
  ext a
  simp only [Local.mem_historySupport, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (history_inequalityEvent s (Binomial.point a)).symm

theorem binomialNormalizedMoment_child_integral (N : ℕ) (p : Binomial.Probability)
    (sizes : Local.Sizes n) (s : History (n + 1)) (b : Bool)
    (center : History (n + 1) → ℝ) (scale : ℝ)
    (o : MomentKind (Fintype.card (Fin (n + 1) → Bool))) (σ : Row (n + 1)) :
    binomialNormalizedMoment N p sizes s (Local.childSupport sizes s b) center scale o σ =
      ∫ a in Binomial.inequalityEvent (childMatrix s b) (childStrict s b),
        momentValue o (fun t => ((a t : ℝ) - center t) / scale)
        ∂Binomial.law (Local.trials sizes s) (rowTilt N p σ) := by
  apply binomialNormalizedMoment_eq_integral
  classical
  ext a
  simp only [Local.mem_childSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (child_inequalityEvent s b (Binomial.point a)).symm

end MajorityDynamics.Idealized.RowLimits
