import MajorityDynamics.Probability.FixedDegreeSampling.FiniteLaw
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.Basic

/-! The two independent uniform subset laws retained literally in Lemma C.4. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace MajorityDynamics.Probability.NeighborhoodBulk
open FixedDegreeSampling
variable {V : Type*} [Fintype V]

def subsetLaw (A : Finset V) (k : ℕ) : Measure (Finset V) :=
  uniformOn (A.powersetCard k : Set (Finset V))

instance (A : Finset V) (k : ℕ) : IsFiniteMeasure (subsetLaw A k) := by
  unfold subsetLaw
  infer_instance

def subsetPairLaw (A B : Finset V) (k l : ℕ) : Measure (Finset V × Finset V) :=
  (subsetLaw A k).prod (subsetLaw B l)

def subsetExpectation (A B : Finset V) (k l : ℕ) (f : Finset V → ℝ) : ℝ :=
  ∫ R, f (R.1 ∪ R.2) ∂subsetPairLaw A B k l

theorem subsetLaw_integral (A : Finset V) (k : ℕ) (f : Finset V → ℝ) :
    ∫ R, f R ∂subsetLaw A k =
      (∑ R ∈ A.powersetCard k, f R) / (A.card.choose k : ℝ) := by
  rw [subsetLaw, uniform_integral]
  simp

theorem subsetExpectation_eq_average (A B : Finset V) (k l : ℕ)
    (f : Finset V → ℝ) :
    subsetExpectation A B k l f =
      (∑ R₁ ∈ A.powersetCard k, ∑ R₂ ∈ B.powersetCard l, f (R₁ ∪ R₂)) /
        ((A.card.choose k : ℝ) * (B.card.choose l : ℝ)) := by
  unfold subsetExpectation subsetPairLaw
  rw [integral_prod _ (by simp)]
  simp_rw [subsetLaw_integral]
  rw [← Finset.sum_div, div_div, mul_comm]

theorem subsetLaw_normalized (A : Finset V) (k : ℕ) (hk : k ≤ A.card) :
    IsProbabilityMeasure (subsetLaw A k) := by
  apply isProbabilityMeasure_uniformOn (Set.toFinite _)
  exact_mod_cast (Finset.powersetCard_nonempty.mpr hk)

theorem subsetPairLaw_normalized (A B : Finset V) (k l : ℕ)
    (hk : k ≤ A.card) (hl : l ≤ B.card) :
    IsProbabilityMeasure (subsetPairLaw A B k l) := by
  have :=  subsetLaw_normalized A k hk
  have :=  subsetLaw_normalized B l hl
  unfold subsetPairLaw
  infer_instance

theorem subsetPairLaw_independent (A B : Finset V) (k l : ℕ)
    (hk : k ≤ A.card) (hl : l ≤ B.card) :
    IndepFun Prod.fst Prod.snd (subsetPairLaw A B k l) := by
  have :=  subsetLaw_normalized A k hk
  have :=  subsetLaw_normalized B l hl
  exact indepFun_prod (X := id) (Y := id) measurable_id measurable_id

omit [Fintype V] in
theorem subsetLaw_eq_zero (A : Finset V) (k : ℕ) (hk : A.card < k) :
    subsetLaw A k = 0 := by
  simp [subsetLaw, Finset.powersetCard_eq_empty.mpr hk]

omit [Fintype V] in
theorem subsetExpectation_eq_zero_left (A B : Finset V) (k l : ℕ)
    (hk : A.card < k) (f : Finset V → ℝ) :
    subsetExpectation A B k l f = 0 := by
  simp [subsetExpectation, subsetPairLaw, subsetLaw_eq_zero A k hk]

omit [Fintype V] in
theorem subsetExpectation_eq_zero_right (A B : Finset V) (k l : ℕ)
    (hl : B.card < l) (f : Finset V → ℝ) :
    subsetExpectation A B k l f = 0 := by
  simp [subsetExpectation, subsetPairLaw, subsetLaw_eq_zero B l hl]

omit [Fintype V] in
theorem subsetExpectation_nonneg (A B : Finset V) (k l : ℕ)
    (f : Finset V → ℝ) (hf : ∀ R, 0 ≤ f R) :
    0 ≤ subsetExpectation A B k l f :=
  integral_nonneg (fun R => hf (R.1 ∪ R.2))

end MajorityDynamics.Probability.NeighborhoodBulk
