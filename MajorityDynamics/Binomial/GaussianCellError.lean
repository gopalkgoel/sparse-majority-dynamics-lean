import MajorityDynamics.Binomial.GaussianMomentBounds
import MajorityDynamics.Binomial.GaussianBoundary
import MajorityDynamics.Binomial.ObservableBounds
import MajorityDynamics.Analysis.MonomialError
import MajorityDynamics.Analysis.CellApproximation

/-! # Polynomial and event errors inside the actual Gaussian cells -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace MajorityDynamics.Binomial.Approximation
variable {d r : ℕ}

def gaussianBoundary (M : Fin r → Fin d → ℤ) (p : Probability) (η : Fin d → ℕ) : Set (Fin d → ℝ) :=
  {x | ∃ j, |(∑ i, (M j i : ℝ) * x i) + (p : ℝ) * (∑ i, (M j i : ℝ) * η i)| ≤ ∑ i, |(M j i : ℝ)|}

theorem gaussianBoundary_measurable (M : Fin r → Fin d → ℤ) (p : Probability) (η : Fin d → ℕ) :
    MeasurableSet (gaussianBoundary M p η) := by unfold gaussianBoundary; measurability

theorem gaussian_boundary_le (M : Fin r → Fin d → ℤ) (p : Probability) (η : Fin d → ℕ)
    (α : Fin d → ℝ) (T s : ℝ) (hT : 1 ≤ T) (hs : 0 < s)
    (hvar : ∀ i, s ^ 2 / T ≤ (p : ℝ) * η i) (hM : ∀ j, ∃ i, M j i ≠ 0) :
    (gaussianLaw p η α).real (gaussianBoundary M p η) ≤
      (2 * T * ∑ j, ∑ i, |(M j i : ℝ)|) / s := by
  classical
  have heq : gaussianBoundary M p η = ⋃ j, {x : Fin d → ℝ |
      |(∑ i, (M j i : ℝ) * x i) + (p : ℝ) * (∑ i, (M j i : ℝ) * η i)| ≤ ∑ i, |(M j i : ℝ)|} := by
    ext x; simp [gaussianBoundary]
  rw [heq]
  apply (measureReal_iUnion_fintype_le _).trans
  have hb (j : Fin r) := gaussian_strip_le p η α (fun i => (M j i : ℝ)) T s hT hs hvar
    (by
      obtain ⟨i, hi⟩ := hM j
      refine ⟨i, ?_⟩
      have hpos : (0 : ℤ) < |M j i| := abs_pos.mpr hi
      have hone : (1 : ℤ) ≤ |M j i| := by omega
      exact_mod_cast hone)
    (-((p : ℝ) * ∑ i, (M j i : ℝ) * η i)) (∑ i, |(M j i : ℝ)|) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hsum := Finset.sum_le_sum (fun j (_hj : j ∈ (Finset.univ : Finset (Fin r))) => hb j)
  simp only [sub_neg_eq_add] at hsum
  convert hsum using 1
  simp only [Finset.sum_div, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

def gaussianRestrictedObservable (M : Fin r → Fin d → ℤ) (p : Probability)
    (η : Fin d → ℕ) (c : ℝ) (e : Fin d → ℕ) : (Fin d → ℝ) → ℝ :=
  (gaussianEvent M p η).indicator (monomial c e)

theorem gaussianEvent_measurable (M : Fin r → Fin d → ℤ) (p : Probability) (η : Fin d → ℕ) :
    MeasurableSet (gaussianEvent M p η) := by unfold gaussianEvent; measurability

theorem integrable_gaussianRestrictedObservable (M : Fin r → Fin d → ℤ) (p : Probability)
    (η : Fin d → ℕ) (α : Fin d → ℝ) (c : ℝ) (e : Fin d → ℕ) :
    Integrable (gaussianRestrictedObservable M p η c e) (gaussianLaw p η α) :=
  (integrable_gaussian_monomial p η α c e).indicator (gaussianEvent_measurable M p η)

theorem monomial_cell_variation (p : Probability) (η a : Fin d → ℕ) (x : Fin d → ℝ)
    (c : ℝ) (e : Fin d → ℕ) (R : ℝ) (hR : 0 < R)
    (ha : ∀ i, |centered p η a i| ≤ R) (hx : ∀ i, |x i| ≤ R)
    (hcell : x ∈ gaussianCell p η a) :
    |monomial c e x - monomial c e (centered p η a)| ≤
      |c| * (∑ i, (e i : ℝ)) * R ^ (∑ i, e i) / R := by
  rw [monomial, monomial, ← mul_sub, abs_mul]
  have h := Analysis.prod_monomial_error Finset.univ e x (centered p η a) R 1 hR zero_le_one
    (fun i _ => hx i) (fun i _ => ha i) (fun i _ => by
      rw [abs_sub_comm]
      exact gaussianCell_coordinate_error p η a hcell i)
  simpa only [one_mul, mul_div_assoc, mul_assoc] using mul_le_mul_of_nonneg_left h (abs_nonneg c)

theorem gaussian_cell_observable_error (M : Fin r → Fin d → ℤ) (strict : Fin r → Bool)
    (p : Probability) (η a : Fin d → ℕ) (x : Fin d → ℝ) (c : ℝ) (e : Fin d → ℕ)
    (R : ℝ) (hR : 0 < R) (ha : ∀ i, |centered p η a i| ≤ R) (hx : ∀ i, |x i| ≤ R)
    (hcell : x ∈ gaussianCell p η a) :
    |gaussianRestrictedObservable M p η c e x -
      restrictedObservable (fun j i => (M j i : ℝ)) strict p η (monomial c e) a| ≤
      |c| * (∑ i, (e i : ℝ)) * R ^ (∑ i, e i) / R +
      2 * (|c| * R ^ (∑ i, e i)) * (gaussianBoundary M p η).indicator (fun _ => (1 : ℝ)) x := by
  classical
  have hε : 0 ≤ |c| * (∑ i, (e i : ℝ)) * R ^ (∑ i, e i) / R := by positivity
  have hA := restrictedObservable_abs_le (fun j i => (M j i : ℝ)) strict p η c e R hR.le a ha
  have hX : |gaussianRestrictedObservable M p η c e x| ≤ |c| * R ^ (∑ i, e i) := by
    by_cases hm : x ∈ gaussianEvent M p η
    · simpa [gaussianRestrictedObservable, hm] using monomial_abs_le c e x R hx
    · simp only [gaussianRestrictedObservable, Set.indicator_of_notMem hm, abs_zero]
      positivity
  by_cases hb : x ∈ gaussianBoundary M p η
  · rw [Set.indicator_of_mem hb, mul_one]
    have h := (abs_sub _ _).trans (add_le_add hX hA)
    linarith
  · rw [Set.indicator_of_notMem hb, mul_zero, add_zero]
    have hsame : a ∈ inequalityEvent (fun j i => (M j i : ℝ)) strict ↔ x ∈ gaussianEvent M p η := by
      by_contra hh
      exact hb (inequality_event_mismatch M strict p η a x (gaussianCell_coordinate_error p η a hcell) hh)
    by_cases haE : a ∈ inequalityEvent (fun j i => (M j i : ℝ)) strict
    · have hxE := hsame.mp haE
      simpa [gaussianRestrictedObservable, restrictedObservable, haE, hxE] using
        monomial_cell_variation p η a x c e R hR ha hx hcell
    · have hxE : x ∉ gaussianEvent M p η := fun hh => haE (hsame.mpr hh)
      simpa [gaussianRestrictedObservable, restrictedObservable, haE, hxE] using hε

end MajorityDynamics.Binomial.Approximation
