import MajorityDynamics.Probability.ConditionedBinomialLocalCLT.MomentsScalar
import MajorityDynamics.Probability.ConditionedBinomialFourier.Characteristic

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace MajorityDynamics.Probability.ConditionedBinomialLocalCLT
namespace Moments

variable {d : ℕ}

def rawConstant (c : ℝ) (k : ℕ) : ℝ := 2 * (k.factorial : ℝ) * Real.exp 1 / c

def centeredConstant (c : ℝ) (k : ℕ) : ℝ :=
  2 ^ (k - 1) * (rawConstant c k + rawConstant c 1 ^ k)

theorem integrable_cond (η : Fin d → ℕ) (q : Fin d → Binomial.Probability)
    (E : Set (Fin d → ℕ)) (hE : (Binomial.law η q) E ≠ 0)
    (f : (Fin d → ℕ) → ℝ) : Integrable f (cond (Binomial.law η q) E) := by
  exact (Binomial.integrable_law η q f).restrict.smul_measure (ENNReal.inv_ne_top.mpr hE)

theorem conditional_integral_le (η : Fin d → ℕ) (q : Fin d → Binomial.Probability)
    (E : Set (Fin d → ℕ)) {c : ℝ} (hc : 0 < c)
    (hE : c ≤ (Binomial.law η q).real E) (f : (Fin d → ℕ) → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    (∫ x, f x ∂cond (Binomial.law η q) E) ≤ (∫ x, f x ∂Binomial.law η q) / c := by
  have hmass : 0 < (Binomial.law η q).real E := hc.trans_le hE
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, ← measureReal_def, smul_eq_mul]
  calc
    _ ≤ ((Binomial.law η q).real E)⁻¹ * (∫ x, f x ∂Binomial.law η q) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hmass.le)
      exact integral_mono_measure Measure.restrict_le_self (ae_of_all _ hf)
        (Binomial.integrable_law η q f)
    _ ≤ (∫ x, f x ∂Binomial.law η q) / c := by
      rw [div_eq_mul_inv, mul_comm]
      exact mul_le_mul_of_nonneg_left (inv_anti₀ hc hE) (integral_nonneg hf)

theorem raw_coordinate (η : Fin d → ℕ) (q : Fin d → Binomial.Probability)
    (E : Set (Fin d → ℕ)) {c s : ℝ} (hc : 0 < c)
    (hE : c ≤ (Binomial.law η q).real E) (hs : 1 ≤ s)
    (hmean : ∀ i, (η i : ℝ) * (q i : ℝ) ≤ s ^ 2) (i : Fin d) (k : ℕ) :
    (∫ x, |(x i : ℝ) - η i * (q i : ℝ)| ^ k ∂cond (Binomial.law η q) E) ≤
      rawConstant c k * s ^ k := by
  apply (conditional_integral_le η q E hc hE _ (fun _ => pow_nonneg (abs_nonneg _) _)).trans
  have heq : (∫ x, |(x i : ℝ) - η i * (q i : ℝ)| ^ k ∂Binomial.law η q) =
      ∫ x, |(x : ℝ) - η i * (q i : ℝ)| ^ k
        ∂binomial (η i) (Binomial.closedProbability (q i)) := by
    rw [← Binomial.coordinate_law η q i, integral_map .of_discrete .of_discrete]
  rw [heq]
  have h := div_le_div_of_nonneg_right (binomial_absolute_moment (η i) (q i) s hs (hmean i) k) hc.le
  simpa [rawConstant, div_mul_eq_mul_div] using h

theorem mean_shift (η : Fin d → ℕ) (q : Fin d → Binomial.Probability)
    (E : Set (Fin d → ℕ)) {c s : ℝ} (hc : 0 < c)
    (hE : c ≤ (Binomial.law η q).real E) (hs : 1 ≤ s)
    (hmean : ∀ i, (η i : ℝ) * (q i : ℝ) ≤ s ^ 2) (i : Fin d) :
    |ConditionedBinomialFourier.mean (cond (Binomial.law η q) E) i - η i * (q i : ℝ)| ≤
      rawConstant c 1 * s := by
  have hmass : (Binomial.law η q) E ≠ 0 :=
    (ENNReal.toReal_pos_iff.mp (hc.trans_le hE)).1.ne'
  have := cond_isProbabilityMeasure hmass
  have heq : ConditionedBinomialFourier.mean (cond (Binomial.law η q) E) i - η i * (q i : ℝ) =
      ∫ x, (x i : ℝ) - η i * (q i : ℝ) ∂cond (Binomial.law η q) E := by
    rw [integral_sub (integrable_cond η q E hmass _) (integrable_const _), integral_const]
    simp [ConditionedBinomialFourier.mean]
  rw [heq]
  exact abs_integral_le_integral_abs.trans (by simpa using raw_coordinate η q E hc hE hs hmean i 1)

theorem centered_coordinate (η : Fin d → ℕ) (q : Fin d → Binomial.Probability)
    (E : Set (Fin d → ℕ)) {c s : ℝ} (hc : 0 < c)
    (hE : c ≤ (Binomial.law η q).real E) (hs : 1 ≤ s)
    (hmean : ∀ i, (η i : ℝ) * (q i : ℝ) ≤ s ^ 2) (i : Fin d) (k : ℕ) :
    (∫ x, |(x i : ℝ) - ConditionedBinomialFourier.mean (cond (Binomial.law η q) E) i| ^ k
      ∂cond (Binomial.law η q) E) ≤ centeredConstant c k * s ^ k := by
  have hmass : (Binomial.law η q) E ≠ 0 :=
    (ENNReal.toReal_pos_iff.mp (hc.trans_le hE)).1.ne'
  have := cond_isProbabilityMeasure hmass
  have hs0 : 0 ≤ s := by linarith
  have hshift := mean_shift η q E hc hE hs hmean i
  let a := ConditionedBinomialFourier.mean (cond (Binomial.law η q) E) i
  have hpt (x : Fin d → ℕ) : |(x i : ℝ) - a| ^ k ≤
      2 ^ (k - 1) * (|(x i : ℝ) - η i * (q i : ℝ)| ^ k +
        (rawConstant c 1 * s) ^ k) := by
    have htri : |(x i : ℝ) - a| ≤ |(x i : ℝ) - η i * (q i : ℝ)| + rawConstant c 1 * s := by
      have h := abs_sub_le (x i : ℝ) (η i * (q i : ℝ)) a
      rw [abs_sub_comm (η i * (q i : ℝ)) a] at h
      exact h.trans (add_le_add le_rfl hshift)
    exact (pow_le_pow_left₀ (abs_nonneg _) htri k).trans
      (add_pow_le (abs_nonneg _) (by unfold rawConstant; positivity) k)
  calc
    _ ≤ ∫ x, 2 ^ (k - 1) * (|(x i : ℝ) - η i * (q i : ℝ)| ^ k +
        (rawConstant c 1 * s) ^ k) ∂cond (Binomial.law η q) E :=
      integral_mono (integrable_cond η q E hmass _) (integrable_cond η q E hmass _) hpt
    _ = 2 ^ (k - 1) * ((∫ x, |(x i : ℝ) - η i * (q i : ℝ)| ^ k
        ∂cond (Binomial.law η q) E) + (rawConstant c 1 * s) ^ k) := by
      rw [integral_const_mul, integral_add (integrable_cond η q E hmass _) (integrable_const _)]
      simp
    _ ≤ 2 ^ (k - 1) * (rawConstant c k * s ^ k + (rawConstant c 1 * s) ^ k) :=
      mul_le_mul_of_nonneg_left (add_le_add (raw_coordinate η q E hc hE hs hmean i k) le_rfl) (by positivity)
    _ = centeredConstant c k * s ^ k := by simp only [centeredConstant, mul_pow]; ring

end Moments
end MajorityDynamics.Probability.ConditionedBinomialLocalCLT
