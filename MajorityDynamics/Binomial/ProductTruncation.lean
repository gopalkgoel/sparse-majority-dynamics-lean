import MajorityDynamics.Binomial.Conditioning
import MajorityDynamics.Binomial.Tails

/-! # Actual product-law sums and truncation

These bridges apply to arbitrary ambient finite sets, so the same lattice
window can be used for two different trial vectors.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace MajorityDynamics.Binomial

variable {ι : Type*} [Fintype ι]

def ambientMass (η : ι → ℕ) (q : ι → Probability) (a : ι → ℕ) : ℝ :=
  ∏ i, (η i).choose (a i) * (q i : ℝ) ^ a i * (1 - (q i : ℝ)) ^ (η i - a i)

theorem law_singleton_ambient (η : ι → ℕ) (q : ι → Probability) (a : ι → ℕ) :
    (law η q).real {a} = ambientMass η q a := by
  simp only [measureReal_def, law, Measure.pi_singleton, ENNReal.toReal_prod]
  simp only [← measureReal_def, ProbabilityTheory.binomial_real_singleton,
    closedProbability, ambientMass]

theorem integrable_law (η : ι → ℕ) (q : ι → Probability) (f : (ι → ℕ) → ℝ) :
    Integrable f (law η q) := by
  classical
  have hfull : event (Finset.univ : Finset (Box η)) =ᵐ[law η q] Set.univ := by
    simpa using filter_event_ae_eq η q Set.univ
  have hfinite : (event (Finset.univ : Finset (Box η))).Finite :=
    Finset.finite_toSet _ |>.image point
  have hi : IntegrableOn f (event (Finset.univ : Finset (Box η))) (law η q) :=
    IntegrableOn.of_finite hfinite
  rwa [IntegrableOn, Measure.restrict_congr_set hfull, Measure.restrict_univ] at hi

theorem integral_finite_event (η : ι → ℕ) (q : ι → Probability)
    (S : Finset (ι → ℕ)) (f : (ι → ℕ) → ℝ) :
    ∫ a in (S : Set (ι → ℕ)), f a ∂law η q = ∑ a ∈ S, ambientMass η q a * f a := by
  rw [setIntegral_finset S IntegrableOn.finset]
  simp only [law_singleton_ambient, smul_eq_mul]

def rectangle (c R : ι → ℝ) : Set (ι → ℕ) :=
  {a | ∀ i, |(a i : ℝ) - c i| ≤ R i}

theorem rectangle_tail_le (η : ι → ℕ) (q : ι → Probability)
    (c R B : ι → ℝ)
    (h : ∀ i, (ProbabilityTheory.binomial (η i) (closedProbability (q i))).real
      {k : ℕ | R i ≤ |(k : ℝ) - c i|} ≤ B i) :
    (law η q).real (rectangle c R)ᶜ ≤ ∑ i, B i := by
  classical
  have hsub : (rectangle c R)ᶜ ⊆ ⋃ i, {a : ι → ℕ | R i ≤ |(a i : ℝ) - c i|} := by
    intro a ha
    have he : ∃ i, R i < |(a i : ℝ) - c i| := by simpa [rectangle] using ha
    obtain ⟨i, hi⟩ := he
    exact mem_iUnion.mpr ⟨i, hi.le⟩
  apply (measureReal_mono hsub).trans
  apply (measureReal_iUnion_fintype_le _).trans
  apply Finset.sum_le_sum
  intro i _
  have hmap := coordinate_law η q i
  have heq : (law η q).real {a : ι → ℕ | R i ≤ |(a i : ℝ) - c i|} =
      (ProbabilityTheory.binomial (η i) (closedProbability (q i))).real
        {k : ℕ | R i ≤ |(k : ℝ) - c i|} := by
    rw [← hmap, map_measureReal_apply (measurable_pi_apply i) (by measurability)]
    rfl
  exact heq.trans_le (h i)

/-- Discarding a common event changes a bounded observable by at most its
bound times the discarded mass. The bound need only hold almost everywhere. -/
theorem integral_truncation_le (η : ι → ℕ) (q : ι → Probability)
    (E : Set (ι → ℕ)) (f : (ι → ℕ) → ℝ) (H : ℝ)
    (hf : ∀ᵐ a ∂(law η q).restrict Eᶜ, |f a| ≤ H) :
    |(∫ a, f a ∂law η q) - ∫ a in E, f a ∂law η q| ≤ H * (law η q).real Eᶜ := by
  classical
  have hE : MeasurableSet E := (Set.to_countable E).measurableSet
  rw [← setIntegral_compl hE (integrable_law η q f)]
  calc
    _ ≤ ∫ a in Eᶜ, |f a| ∂law η q := abs_integral_le_integral_abs
    _ ≤ ∫ _a in Eᶜ, H ∂law η q :=
      integral_mono_ae (integrable_law η q f).abs.integrableOn (integrable_const H) hf
    _ = _ := by rw [setIntegral_const]; simp [smul_eq_mul, mul_comm]

end MajorityDynamics.Binomial
