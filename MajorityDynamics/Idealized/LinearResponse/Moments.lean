import MajorityDynamics.Idealized.LinearResponse.Basic
import MajorityDynamics.Idealized.RowLimits.Observables
import MajorityDynamics.Idealized.RowLimits.ApproximationLocal

/-! Centered finite moments of the actual product-binomial law and their exact
identification with the Appendix A.2 event integrals. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace MajorityDynamics.Idealized.LinearResponse

attribute [local instance] Classical.propDecidable

open MajorityDynamics.Universal
open MajorityDynamics.Binomial (mass eventMass vector point)
open MajorityDynamics.Idealized.RowLimits (momentExponent momentValue moment_monomial)

section Generic

variable {ι : Type*} [Fintype ι]

/-- `Σ_{a∈S} w(a) (a_i - c_i)`. -/
def cfirst (η : ι → ℕ) (q : ι → Binomial.Probability) (S : Finset (Binomial.Box η))
    (c : ι → ℝ) (i : ι) : ℝ :=
  ∑ a ∈ S, mass η q a * (vector a i - c i)

/-- `Σ_{a∈S} w(a) (a_i - c_i)(a_j - c_j)`. -/
def csecond (η : ι → ℕ) (q : ι → Binomial.Probability) (S : Finset (Binomial.Box η))
    (c : ι → ℝ) (i j : ι) : ℝ :=
  ∑ a ∈ S, mass η q a * ((vector a i - c i) * (vector a j - c j))

theorem cfirst_eq (η : ι → ℕ) (q : ι → Binomial.Probability) (S : Finset (Binomial.Box η))
    (c : ι → ℝ) (i : ι) :
    cfirst η q S c i = (∑ a ∈ S, mass η q a * vector a i) - c i * eventMass η q S := by
  unfold cfirst eventMass
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem csecond_eq (η : ι → ℕ) (q : ι → Binomial.Probability) (S : Finset (Binomial.Box η))
    (c : ι → ℝ) (i j : ι) :
    csecond η q S c i j =
      (∑ a ∈ S, mass η q a * (vector a i * vector a j)) -
        c j * (∑ a ∈ S, mass η q a * vector a i) -
        c i * (∑ a ∈ S, mass η q a * vector a j) + c i * c j * eventMass η q S := by
  unfold csecond eventMass
  calc
    _ = ∑ a ∈ S, (mass η q a * (vector a i * vector a j) - c j * (mass η q a * vector a i) -
          c i * (mass η q a * vector a j) + c i * c j * mass η q a) := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

theorem conditionalMean_eq_div (η : ι → ℕ) (q : ι → Binomial.Probability)
    (S : Finset (Binomial.Box η)) (i : ι) :
    Binomial.conditionalMean η q S i = (∑ a ∈ S, mass η q a * vector a i) / eventMass η q S := by
  simp only [Binomial.conditionalMean, Binomial.expectation, Binomial.conditionalWeight,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The conditional mean is the centered first moment normalized, plus the center. -/
theorem conditionalMean_eq_cfirst (η : ι → ℕ) (q : ι → Binomial.Probability)
    (S : Finset (Binomial.Box η)) (c : ι → ℝ) (i : ι) (hE : eventMass η q S ≠ 0) :
    Binomial.conditionalMean η q S i = cfirst η q S c i / eventMass η q S + c i := by
  rw [conditionalMean_eq_div, cfirst_eq, sub_div, mul_div_assoc, div_self hE, mul_one]
  ring

/-- Centering invariance of the covariance. -/
theorem covariance_eq_csecond (η : ι → ℕ) (q : ι → Binomial.Probability)
    (S : Finset (Binomial.Box η)) (c : ι → ℝ) (i j : ι) (hE : eventMass η q S ≠ 0) :
    (∑ a ∈ S, mass η q a * (vector a i * vector a j)) / eventMass η q S -
        Binomial.conditionalMean η q S i * Binomial.conditionalMean η q S j =
      csecond η q S c i j / eventMass η q S -
        (cfirst η q S c i / eventMass η q S) * (cfirst η q S c j / eventMass η q S) := by
  rw [conditionalMean_eq_div, conditionalMean_eq_div, cfirst_eq, cfirst_eq, csecond_eq]
  field_simp
  ring

theorem eventMass_mono (η : ι → ℕ) (q : ι → Binomial.Probability)
    {S S' : Finset (Binomial.Box η)} (h : S' ⊆ S) : eventMass η q S' ≤ eventMass η q S :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun a _ _ => (Binomial.mass_pos η q a).le)

theorem eventMass_nonneg (η : ι → ℕ) (q : ι → Binomial.Probability)
    (S : Finset (Binomial.Box η)) : 0 ≤ eventMass η q S :=
  Finset.sum_nonneg (fun a _ => (Binomial.mass_pos η q a).le)

theorem abs_mul_le_half (u v : ℝ) : |u * v| ≤ (u * u + v * v) / 2 := by
  rw [abs_mul]
  nlinarith [sq_nonneg (|u| - |v|), sq_abs u, sq_abs v, abs_nonneg u, abs_nonneg v]

/-- A second moment over a sub-support is controlled by diagonal second moments
over the full support. -/
theorem abs_csecond_subset_le (η : ι → ℕ) (q : ι → Binomial.Probability)
    {S S' : Finset (Binomial.Box η)} (h : S' ⊆ S) (c : ι → ℝ) (i j : ι) :
    |csecond η q S' c i j| ≤ (csecond η q S c i i + csecond η q S c j j) / 2 := by
  unfold csecond
  calc
    _ ≤ ∑ a ∈ S', |mass η q a * ((vector a i - c i) * (vector a j - c j))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ S', mass η q a *
        (((vector a i - c i) * (vector a i - c i) + (vector a j - c j) * (vector a j - c j)) / 2) := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul, abs_of_pos (Binomial.mass_pos η q a)]
      exact mul_le_mul_of_nonneg_left (abs_mul_le_half _ _) (Binomial.mass_pos η q a).le
    _ ≤ ∑ a ∈ S, mass η q a *
        (((vector a i - c i) * (vector a i - c i) + (vector a j - c j) * (vector a j - c j)) / 2) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg h
      intro a _ _
      exact mul_nonneg (Binomial.mass_pos η q a).le
        (div_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (by norm_num))
    _ = _ := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      ring

end Generic

section Bridges

variable {d : ℕ}

theorem monomial_kind0 (x : Fin d → ℝ) :
    Binomial.Approximation.monomial 1 (momentExponent (Sum.inl () : RowLimits.MomentKind d)) x = 1 :=
  moment_monomial _ x

theorem monomial_kind1 (t : Fin d) (x : Fin d → ℝ) :
    Binomial.Approximation.monomial 1
      (momentExponent (Sum.inr (Sum.inl t) : RowLimits.MomentKind d)) x = x t :=
  moment_monomial _ x

theorem degree_kind0 : ∑ i, momentExponent (Sum.inl () : RowLimits.MomentKind d) i = 0 := by
  simp [momentExponent]

theorem degree_kind1 (t : Fin d) :
    ∑ i, momentExponent (Sum.inr (Sum.inl t) : RowLimits.MomentKind d) i = 1 := by
  simp [momentExponent]

theorem centered_point {η : Fin d → ℕ} (p : Binomial.Probability) (ref : Fin d → ℕ)
    (a : Binomial.Box η) (i : Fin d) :
    Binomial.Approximation.centered p ref (point a) i = vector a i - (p : ℝ) * ref i := rfl

/-- The A.2 event integral is the finite sum over the enumerated support. -/
theorem moment_eq_support_sum {r : ℕ} {η : Fin d → ℕ} (q : Fin d → Binomial.Probability)
    (p : Binomial.Probability) (ref : Fin d → ℕ) (M : Fin r → Fin d → ℝ)
    (strict : Fin r → Bool) (S : Finset (Binomial.Box η))
    (hS : S = Finset.univ.filter
      (fun a => point a ∈ Binomial.inequalityEvent M strict))
    (f : (Fin d → ℝ) → ℝ) :
    Binomial.Approximation.moment M strict p ref η q f =
      ∑ a ∈ S, mass η q a * f (Binomial.Approximation.centered p ref (point a)) := by
  subst hS
  unfold Binomial.Approximation.moment
  rw [← Measure.restrict_congr_set
    (Binomial.filter_event_ae_eq η q (Binomial.inequalityEvent M strict))]
  convert RowLimits.binomial_integral_event η q
    (Finset.univ.filter (fun a : Binomial.Box η => point a ∈ Binomial.inequalityEvent M strict))
    (fun a => f (Binomial.Approximation.centered p ref a))

theorem moment_kind0_eq {r : ℕ} {η : Fin d → ℕ} (q : Fin d → Binomial.Probability)
    (p : Binomial.Probability) (ref : Fin d → ℕ) (M : Fin r → Fin d → ℝ)
    (strict : Fin r → Bool) (S : Finset (Binomial.Box η))
    (hS : S = Finset.univ.filter (fun a => point a ∈ Binomial.inequalityEvent M strict)) :
    Binomial.Approximation.moment M strict p ref η q
        (Binomial.Approximation.monomial 1 (momentExponent (Sum.inl ()))) =
      eventMass η q S := by
  rw [moment_eq_support_sum q p ref M strict S hS]
  apply Finset.sum_congr rfl
  intro a _
  rw [monomial_kind0, mul_one]

theorem moment_kind0_first_eq {r : ℕ} {η : Fin d → ℕ} (q : Fin d → Binomial.Probability)
    (p : Binomial.Probability) (ref : Fin d → ℕ) (M : Fin r → Fin d → ℝ)
    (strict : Fin r → Bool) (S : Finset (Binomial.Box η))
    (hS : S = Finset.univ.filter (fun a => point a ∈ Binomial.inequalityEvent M strict))
    (i : Fin d) :
    Binomial.Approximation.moment M strict p ref η q
        (fun x => x i * Binomial.Approximation.monomial 1 (momentExponent (Sum.inl ())) x) =
      cfirst η q S (fun j => (p : ℝ) * ref j) i := by
  rw [moment_eq_support_sum q p ref M strict S hS]
  apply Finset.sum_congr rfl
  intro a _
  rw [monomial_kind0, mul_one, centered_point]

theorem moment_kind1_eq {r : ℕ} {η : Fin d → ℕ} (q : Fin d → Binomial.Probability)
    (p : Binomial.Probability) (ref : Fin d → ℕ) (M : Fin r → Fin d → ℝ)
    (strict : Fin r → Bool) (S : Finset (Binomial.Box η))
    (hS : S = Finset.univ.filter (fun a => point a ∈ Binomial.inequalityEvent M strict))
    (t : Fin d) :
    Binomial.Approximation.moment M strict p ref η q
        (Binomial.Approximation.monomial 1 (momentExponent (Sum.inr (Sum.inl t)))) =
      cfirst η q S (fun j => (p : ℝ) * ref j) t := by
  rw [moment_eq_support_sum q p ref M strict S hS]
  apply Finset.sum_congr rfl
  intro a _
  rw [monomial_kind1, centered_point]

theorem moment_kind1_first_eq {r : ℕ} {η : Fin d → ℕ} (q : Fin d → Binomial.Probability)
    (p : Binomial.Probability) (ref : Fin d → ℕ) (M : Fin r → Fin d → ℝ)
    (strict : Fin r → Bool) (S : Finset (Binomial.Box η))
    (hS : S = Finset.univ.filter (fun a => point a ∈ Binomial.inequalityEvent M strict))
    (i t : Fin d) :
    Binomial.Approximation.moment M strict p ref η q
        (fun x => x i *
          Binomial.Approximation.monomial 1 (momentExponent (Sum.inr (Sum.inl t))) x) =
      csecond η q S (fun j => (p : ℝ) * ref j) i t := by
  rw [moment_eq_support_sum q p ref M strict S hS]
  apply Finset.sum_congr rfl
  intro a _
  rw [monomial_kind1, centered_point, centered_point]

end Bridges

section Supports

variable {n : ℕ}

/-- Both row supports are the A.2 inequality events. -/
theorem eventSupport_filter (sizes : Local.Sizes n) (s : History (n + 1)) (b : Option Bool) :
    RowLimits.eventSupport sizes s b = Finset.univ.filter
      (fun a : Binomial.Box (Local.trials sizes s) =>
        point a ∈ Binomial.inequalityEvent (RowLimits.eventMatrix s b) (RowLimits.eventStrict s b)) := by
  cases b with
  | none =>
    ext a
    simp only [RowLimits.eventSupport, Local.mem_historySupport, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact (RowLimits.history_inequalityEvent s (point a)).symm
  | some b =>
    ext a
    simp only [RowLimits.eventSupport, Local.mem_childSupport, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact (RowLimits.child_inequalityEvent s b (point a)).symm

theorem eventSupport_subset (sizes : Local.Sizes n) (s : History (n + 1)) (b : Option Bool) :
    RowLimits.eventSupport sizes s b ⊆ Local.historySupport sizes s := by
  cases b with
  | none => exact le_rfl
  | some b => exact Local.childSupport_subset sizes s b

end Supports

end MajorityDynamics.Idealized.LinearResponse
