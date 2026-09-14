import MajorityDynamics.Binomial.Basic
import Mathlib.Probability.ConditionalProbability

/-! # Support and conditioning bridges for the binomial product law -/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace MajorityDynamics.Binomial

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι]

theorem law_ae_box (η : ι → ℕ) (q : ι → Probability) :
    ∀ᵐ a ∂law η q, ∀ i, a i ≤ η i := by
  rw [ae_all_iff]
  intro i
  exact ae_le_of_hasLaw_binomial
    ⟨(measurable_pi_apply i).aemeasurable, coordinate_law η q i⟩

/-- Restricting an event to the enumerated support preserves its actual probability. -/
theorem filter_event_ae_eq (η : ι → ℕ) (q : ι → Probability) (E : Set (ι → ℕ)) :
    event (Finset.univ.filter fun a : Box η => point a ∈ E) =ᵐ[law η q] E := by
  classical
  filter_upwards [law_ae_box η q] with a ha
  apply propext
  constructor
  · rintro ⟨b, hb, rfl⟩
    change point b ∈ E
    exact (Finset.mem_filter.mp hb).2
  · intro hE
    exact ⟨fun i => ⟨a i, Nat.lt_succ_of_le (ha i)⟩, by simpa [point], rfl⟩

theorem conditionalLaw_eq_cond (η : ι → ℕ) (q : ι → Probability) (S : Finset (Box η)) :
    conditionalLaw η q S = ProbabilityTheory.cond (law η q) (event S) := rfl

theorem conditionalLaw_filter (η : ι → ℕ) (q : ι → Probability) (E : Set (ι → ℕ)) :
    conditionalLaw η q (Finset.univ.filter fun a : Box η => point a ∈ E) =
      ProbabilityTheory.cond (law η q) E := by
  classical
  have h := filter_event_ae_eq η q E
  rw [conditionalLaw, ProbabilityTheory.cond, measure_congr h, Measure.restrict_congr_set h]

theorem conditionalLaw_probability (η : ι → ℕ) (q : ι → Probability)
    {S : Finset (Box η)} (hS : S.Nonempty) : IsProbabilityMeasure (conditionalLaw η q S) := by
  rw [conditionalLaw_eq_cond]
  apply cond_isProbabilityMeasure
  have hp := eventMass_pos η q hS
  rw [eventMass_eq_measure] at hp
  exact ENNReal.toReal_ne_zero.mp hp.ne' |>.1

/-- Bayes' formula for a subevent of the finite conditioning support. -/
theorem conditionalLaw_event (η : ι → ℕ) (q : ι → Probability)
    (S A : Finset (Box η)) (hAS : A ⊆ S) :
    (conditionalLaw η q S).real (event A) = eventMass η q A / eventMass η q S := by
  classical
  have hsub : event A ⊆ event S := Set.image_mono hAS
  have hA : MeasurableSet (event A) := (A.finite_toSet.image point).measurableSet
  rw [measureReal_def, conditionalLaw_eq_cond, cond_apply' hA,
    Set.inter_eq_right.mpr hsub, ENNReal.toReal_mul, ENNReal.toReal_inv]
  rw [← measureReal_def, ← measureReal_def, ← eventMass_eq_measure, ← eventMass_eq_measure]
  ring

/-- The same bridge for first moments restricted to a subevent. -/
theorem conditionalLaw_indicator (η : ι → ℕ) (q : ι → Probability)
    (S A : Finset (Box η)) (hAS : A ⊆ S) (f : (ι → ℕ) → ℝ) :
    ∫ a, (event A).indicator f a ∂conditionalLaw η q S =
      (∑ a ∈ A, mass η q a * f (point a)) / eventMass η q S := by
  classical
  rw [integral_conditionalLaw]
  have he (a : Box η) : point a ∈ event A ↔ a ∈ A := by
    simp [event, (point_injective η).mem_set_image]
  simp only [expectation, Set.indicator_apply, he, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  have hf : S.filter (fun a => a ∈ A) = A := by
    ext a
    simp only [Finset.mem_filter, and_iff_right_iff_imp]
    exact fun ha => hAS ha
  rw [hf]
  simp [conditionalWeight, Finset.sum_div, div_mul_eq_mul_div]

end MajorityDynamics.Binomial
