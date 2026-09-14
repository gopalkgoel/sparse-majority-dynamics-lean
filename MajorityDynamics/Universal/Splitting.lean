import MajorityDynamics.Universal.Events
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Positive branch probabilities and the law of total expectation -/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open MajorityDynamics.Analysis

namespace MajorityDynamics.Universal

variable {n : ℕ}

def branchProbability (s : History (n + 1)) (ν : History (n + 1) → ℝ)
    (γ : Row (n + 1)) (b : Bool) : ℝ :=
  (rowLaw ν γ).real (childCone s b) / (rowLaw ν γ).real (historyCone s)

def branchMean (s : History (n + 1)) (ν : History (n + 1) → ℝ)
    (γ : Row (n + 1)) (b : Bool) : Row (n + 1) :=
  ConditionalGaussian.mean (ConditionalGaussian.condition (rowLaw ν γ) (childCone s b))

theorem history_mass_real_pos (s : History (n + 1)) (ν : History (n + 1) → ℝ)
    (hν : ∀ t, 0 < ν t) (γ : Row (n + 1)) : 0 < (rowLaw ν γ).real (historyCone s) :=
  ENNReal.toReal_pos (history_mass_pos s ν hν γ).ne' (measure_ne_top _ _)

theorem child_mass_real_pos (s : History (n + 1)) (b : Bool) (ν : History (n + 1) → ℝ)
    (hν : ∀ t, 0 < ν t) (γ : Row (n + 1)) : 0 < (rowLaw ν γ).real (childCone s b) :=
  ENNReal.toReal_pos (child_mass_pos s b ν hν γ).ne' (measure_ne_top _ _)

theorem branchProbability_pos (s : History (n + 1)) (ν : History (n + 1) → ℝ)
    (hν : ∀ t, 0 < ν t) (γ : Row (n + 1)) (b : Bool) :
    0 < branchProbability s ν γ b :=
  div_pos (child_mass_real_pos s b ν hν γ) (history_mass_real_pos s ν hν γ)

theorem child_mass_add (s : History (n + 1)) (ν : History (n + 1) → ℝ)
    (hν : ∀ t, 0 < ν t) (γ : Row (n + 1)) :
    (rowLaw ν γ).real (childCone s false) + (rowLaw ν γ).real (childCone s true) =
      (rowLaw ν γ).real (historyCone s) := by
  rw [← measureReal_congr (childEvent_ae_eq_cone s false ν hν γ),
    ← measureReal_congr (childEvent_ae_eq_cone s true ν hν γ),
    ← measureReal_union (childEvent_disjoint s) (childEvent_measurable s true),
    childEvent_union, measureReal_congr (historyEvent_ae_eq_cone s ν hν γ)]

theorem branchProbability_add (s : History (n + 1)) (ν : History (n + 1) → ℝ)
    (hν : ∀ t, 0 < ν t) (γ : Row (n + 1)) :
    branchProbability s ν γ false + branchProbability s ν γ true = 1 := by
  rw [branchProbability, branchProbability, ← add_div, child_mass_add s ν hν γ,
    div_self (history_mass_real_pos s ν hν γ).ne']

theorem mean_condition_formula {d : ℕ} (ρ : Measure (ConditionalGaussian.Space d))
    (A : Set (ConditionalGaussian.Space d)) :
    ConditionalGaussian.mean (ConditionalGaussian.condition ρ A) =
      (ρ.real A)⁻¹ • ∫ x in A, x ∂ρ := by
  simp [ConditionalGaussian.mean, ConditionalGaussian.condition, integral_smul_measure,
    ENNReal.toReal_inv, Measure.real]

/-- The open branch integrals sum to the history integral, via the actual tie events. -/
theorem child_integral_add (s : History (n + 1)) (ν : History (n + 1) → ℝ)
    (hν : ∀ t, 0 < ν t) (γ : Row (n + 1)) :
    (∫ x in childCone s false, x ∂rowLaw ν γ) + (∫ x in childCone s true, x ∂rowLaw ν γ) =
      ∫ x in historyCone s, x ∂rowLaw ν γ := by
  have hi : Integrable (fun x => x) (rowLaw ν γ) := IsGaussian.integrable_id
  rw [← setIntegral_congr_set (childEvent_ae_eq_cone s false ν hν γ),
    ← setIntegral_congr_set (childEvent_ae_eq_cone s true ν hν γ),
    ← setIntegral_union (childEvent_disjoint s) (childEvent_measurable s true)
      hi.integrableOn hi.integrableOn,
    childEvent_union, setIntegral_congr_set (historyEvent_ae_eq_cone s ν hν γ)]

/-- The vector law of total expectation used in `eq:children-sum`. -/
theorem branchMean_total (s : History (n + 1)) (ν : History (n + 1) → ℝ)
    (hν : ∀ t, 0 < ν t) (γ : Row (n + 1)) :
    branchProbability s ν γ false • branchMean s ν γ false +
      branchProbability s ν γ true • branchMean s ν γ true = meanMap s ν γ := by
  have cancel (m a : ℝ) (hm : m ≠ 0) : (m / a) * m⁻¹ = a⁻¹ := by
    rw [div_eq_mul_inv]
    calc
      m * a⁻¹ * m⁻¹ = (m * m⁻¹) * a⁻¹ := by ring
      _ = a⁻¹ := by rw [mul_inv_cancel₀ hm, one_mul]
  change _ = ConditionalGaussian.mean (ConditionalGaussian.condition (rowLaw ν γ) (historyCone s))
  simp only [branchMean, mean_condition_formula, branchProbability, smul_smul]
  rw [cancel _ _ (child_mass_real_pos s false ν hν γ).ne',
    cancel _ _ (child_mass_real_pos s true ν hν γ).ne', ← smul_add, child_integral_add s ν hν γ]

theorem branchMean_mem (s : History (n + 1)) (ν : History (n + 1) → ℝ)
    (hν : ∀ t, 0 < ν t) (γ : Row (n + 1)) (b : Bool) :
    branchMean s ν γ b ∈ childCone s b := child_gaussian_mean_mem s b ν hν γ

/-- The quotient in the recursion is precisely probability under normalized restriction. -/
theorem branchProbability_eq_condition (s : History (n + 1)) (ν : History (n + 1) → ℝ)
    (γ : Row (n + 1)) (b : Bool) :
    branchProbability s ν γ b =
      (ConditionalGaussian.condition (rowLaw ν γ) (historyCone s)).real (childCone s b) := by
  simp only [branchProbability, ConditionalGaussian.condition, Measure.real,
    Measure.smul_apply, Measure.restrict_apply (childCone_isOpen s b).measurableSet,
    smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv]
  rw [Set.inter_eq_left.mpr (show childCone s b ⊆ historyCone s from inter_subset_left)]
  exact div_eq_inv_mul _ _

theorem branchMean_coordinate (s : History (n + 1)) (ν : History (n + 1) → ℝ)
    (hν : ∀ t, 0 < ν t) (γ : Row (n + 1)) (b : Bool) (t : History (n + 1)) :
    branchMean s ν γ b t =
      ∫ x, x t ∂ConditionalGaussian.condition (rowLaw ν γ) (childEvent s b) := by
  rw [child_condition_eq s b ν hν γ]
  let hreg := child_gaussian_regular s b ν hν γ
  let := hreg.probability
  exact eval_integral_piLp (fun j => (hreg.memLp_two.eval_piLp j).integrable (by norm_num)) t

theorem branchProbability_eq_event_condition (s : History (n + 1)) (ν : History (n + 1) → ℝ)
    (hν : ∀ t, 0 < ν t) (γ : Row (n + 1)) (b : Bool) :
    branchProbability s ν γ b =
      (ConditionalGaussian.condition (rowLaw ν γ) (historyEvent s)).real (childEvent s b) := by
  simp only [branchProbability, ConditionalGaussian.condition, Measure.real,
    Measure.smul_apply, Measure.restrict_apply (childEvent_measurable s b),
    smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv]
  rw [Set.inter_eq_left.mpr (show childEvent s b ⊆ historyEvent s from inter_subset_left),
    measure_congr (historyEvent_ae_eq_cone s ν hν γ),
    measure_congr (childEvent_ae_eq_cone s b ν hν γ)]
  exact div_eq_inv_mul _ _

end MajorityDynamics.Universal
