import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity

/-!
# Finite binomial rows and their actual conditional law

`law` is Mathlib's product of binomial measures. `Box η` enumerates its finite
support, including the endpoints. The finite-sum conditional expectation is
identified with the integral under normalized restriction of that actual law.
Success probabilities are strictly between zero and one; trial counts may be
zero, as required by the diagonal `n[t]-1` correction in the row model.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace MajorityDynamics.Binomial

abbrev Probability := Set.Ioo (0 : ℝ) 1

def closedProbability (q : Probability) : unitInterval := ⟨q, q.property.1.le, q.property.2.le⟩

def logOdds (q : Probability) : ℝ := Real.log (q : ℝ) - Real.log (1 - (q : ℝ))

variable {ι : Type*} [Fintype ι]

abbrev Box (η : ι → ℕ) := (i : ι) → Fin (η i + 1)

def point {η : ι → ℕ} (a : Box η) : ι → ℕ := fun i => a i

def vector {η : ι → ℕ} (a : Box η) : ι → ℝ := fun i => (a i : ℕ)

omit [Fintype ι] in
theorem point_injective (η : ι → ℕ) : Function.Injective (@point ι η) := by
  intro a b h
  funext i
  exact Fin.ext (congrFun h i)

def law (η : ι → ℕ) (q : ι → Probability) : Measure (ι → ℕ) :=
  Measure.pi (fun i => ProbabilityTheory.binomial (η i) (closedProbability (q i)))

instance (η : ι → ℕ) (q : ι → Probability) : IsProbabilityMeasure (law η q) := by
  unfold law
  infer_instance

theorem independent_coordinates (η : ι → ℕ) (q : ι → Probability) :
    iIndepFun (fun i (a : ι → ℕ) => a i) (law η q) :=
  iIndepFun_pi (fun _ => measurable_id.aemeasurable)

theorem coordinate_law (η : ι → ℕ) (q : ι → Probability) (i : ι) :
    (law η q).map (fun a => a i) = ProbabilityTheory.binomial (η i) (closedProbability (q i)) := by
  classical
  exact (measurePreserving_eval (fun j => ProbabilityTheory.binomial (η j) (closedProbability (q j))) i).map_eq

def mass (η : ι → ℕ) (q : ι → Probability) (a : Box η) : ℝ :=
  ∏ i, (η i).choose (a i) * (q i : ℝ) ^ (a i : ℕ) *
    (1 - (q i : ℝ)) ^ (η i - (a i : ℕ))

theorem mass_pos (η : ι → ℕ) (q : ι → Probability) (a : Box η) : 0 < mass η q a := by
  apply Finset.prod_pos
  intro i _
  have hc : (0 : ℝ) < (η i).choose (a i) := by
    exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ (a i).isLt)
  exact mul_pos (mul_pos hc (pow_pos (q i).property.1 _))
    (pow_pos (sub_pos.mpr (q i).property.2) _)

theorem law_singleton (η : ι → ℕ) (q : ι → Probability) (a : Box η) :
    (law η q).real {point a} = mass η q a := by
  simp only [measureReal_def, law, Measure.pi_singleton, ENNReal.toReal_prod]
  simp only [← measureReal_def, ProbabilityTheory.binomial_real_singleton,
    closedProbability, point, mass]

def event {η : ι → ℕ} (S : Finset (Box η)) : Set (ι → ℕ) := point '' (S : Set (Box η))

def eventMass (η : ι → ℕ) (q : ι → Probability) (S : Finset (Box η)) : ℝ :=
  ∑ a ∈ S, mass η q a

theorem eventMass_pos (η : ι → ℕ) (q : ι → Probability) {S : Finset (Box η)}
    (hS : S.Nonempty) : 0 < eventMass η q S :=
  Finset.sum_pos (fun a _ => mass_pos η q a) hS

theorem eventMass_eq_measure (η : ι → ℕ) (q : ι → Probability) (S : Finset (Box η)) :
    eventMass η q S = (law η q).real (event S) := by
  classical
  rw [event, ← Finset.coe_image, ← sum_measureReal_singleton]
  rw [Finset.sum_image (fun _ _ _ _ h => point_injective η h)]
  simp_rw [law_singleton]
  rfl

/-- Literal normalized restriction; the null-event value is zero. -/
def conditionalLaw (η : ι → ℕ) (q : ι → Probability) (S : Finset (Box η)) : Measure (ι → ℕ) :=
  ((law η q) (event S))⁻¹ • (law η q).restrict (event S)

def conditionalWeight (η : ι → ℕ) (q : ι → Probability) (S : Finset (Box η))
    (a : Box η) : ℝ := mass η q a / eventMass η q S

def expectation (η : ι → ℕ) (q : ι → Probability) (S : Finset (Box η))
    (f : Box η → ℝ) : ℝ := ∑ a ∈ S, conditionalWeight η q S a * f a

def conditionalMean (η : ι → ℕ) (q : ι → Probability) (S : Finset (Box η)) : ι → ℝ :=
  fun i => expectation η q S (fun a => vector a i)

theorem integral_conditionalLaw (η : ι → ℕ) (q : ι → Probability)
    (S : Finset (Box η)) (f : (ι → ℕ) → ℝ) :
    ∫ a, f a ∂conditionalLaw η q S = expectation η q S (fun a => f (point a)) := by
  classical
  rw [conditionalLaw, integral_smul_measure, ENNReal.toReal_inv,
    ← measureReal_def, ← eventMass_eq_measure]
  rw [event, ← Finset.coe_image, setIntegral_finset _ IntegrableOn.finset]
  rw [Finset.sum_image (fun _ _ _ _ h => point_injective η h)]
  simp_rw [law_singleton, smul_eq_mul]
  simp [expectation, conditionalWeight, Finset.mul_sum, div_eq_mul_inv, mul_assoc, mul_comm]

theorem conditionalMean_eq_integral (η : ι → ℕ) (q : ι → Probability)
    (S : Finset (Box η)) (i : ι) :
    conditionalMean η q S i = ∫ a, (a i : ℝ) ∂conditionalLaw η q S := by
  rw [integral_conditionalLaw]
  rfl

end MajorityDynamics.Binomial
