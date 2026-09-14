import MajorityDynamics.Probability.ConditionedBinomialLocalCLT.MomentsConditional
import MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Taylor
import Mathlib.Analysis.MeanInequalities

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace MajorityDynamics.Probability.ConditionedBinomialLocalCLT
namespace Moments

theorem sum_abs_pow {d : ℕ} (a : Fin d → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    (∑ i, |a i|) ^ k ≤ (d : ℝ) ^ (k - 1) * ∑ i, |a i| ^ k := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow Finset.univ a
    (p := (k : ℝ)) (by exact_mod_cast hk)
  rw [show (k : ℝ) - 1 = ((k - 1 : ℕ) : ℝ) by rw [Nat.cast_sub hk]; norm_num] at h
  simpa only [Finset.card_univ, Fintype.card_fin, Real.rpow_natCast] using h

theorem dot_abs_le {d : ℕ} (t a : Fin d → ℝ) :
    |ConditionedBinomialFourier.dot t a| ≤ ‖t‖ * ∑ i, |a i| := by
  unfold ConditionedBinomialFourier.dot
  calc
    _ ≤ ∑ i, |t i * a i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ‖t‖ * |a i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (by simpa using norm_le_pi_norm t i) (abs_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

def directionalConstant (d : ℕ) (c : ℝ) (k : ℕ) : ℝ :=
  (d : ℝ) ^ (k - 1) * d * centeredConstant c k

theorem directional_moment {d : ℕ}
    (η : Fin d → ℕ) (q : Fin d → Binomial.Probability)
    (E : Set (Fin d → ℕ)) {c s : ℝ} (hc : 0 < c)
    (hE : c ≤ (Binomial.law η q).real E) (hs : 1 ≤ s)
    (hmean : ∀ i, (η i : ℝ) * (q i : ℝ) ≤ s ^ 2) (t : Fin d → ℝ)
    (k : ℕ) (hk : 1 ≤ k) :
    (∫ x, |centeredProjection (cond (Binomial.law η q) E) t x| ^ k
      ∂cond (Binomial.law η q) E) ≤ directionalConstant d c k * s ^ k * ‖t‖ ^ k := by
  classical
  let ρ := cond (Binomial.law η q) E
  have hmass : (Binomial.law η q) E ≠ 0 :=
    (ENNReal.toReal_pos_iff.mp (hc.trans_le hE)).1.ne'
  have hpt (x : Fin d → ℕ) : |centeredProjection ρ t x| ^ k ≤
      (‖t‖ ^ k * (d : ℝ) ^ (k - 1)) *
        ∑ i, |(x i : ℝ) - ConditionedBinomialFourier.mean ρ i| ^ k := by
    have hdot := dot_abs_le t ((fun i => (x i : ℝ)) - ConditionedBinomialFourier.mean ρ)
    have hsum := sum_abs_pow ((fun i => (x i : ℝ)) - ConditionedBinomialFourier.mean ρ) k hk
    calc
      _ ≤ (‖t‖ * ∑ i, |(x i : ℝ) - ConditionedBinomialFourier.mean ρ i|) ^ k :=
        pow_le_pow_left₀ (abs_nonneg _) hdot k
      _ = ‖t‖ ^ k * (∑ i, |(x i : ℝ) - ConditionedBinomialFourier.mean ρ i|) ^ k := mul_pow _ _ _
      _ ≤ ‖t‖ ^ k * ((d : ℝ) ^ (k - 1) *
          ∑ i, |(x i : ℝ) - ConditionedBinomialFourier.mean ρ i| ^ k) :=
        mul_le_mul_of_nonneg_left hsum (pow_nonneg (norm_nonneg _) _)
      _ = _ := by ring
  calc
    _ ≤ ∫ x, (‖t‖ ^ k * (d : ℝ) ^ (k - 1)) *
        ∑ i, |(x i : ℝ) - ConditionedBinomialFourier.mean ρ i| ^ k ∂ρ :=
      integral_mono (integrable_cond η q E hmass _) (integrable_cond η q E hmass _) hpt
    _ = (‖t‖ ^ k * (d : ℝ) ^ (k - 1)) *
        ∑ i, ∫ x, |(x i : ℝ) - ConditionedBinomialFourier.mean ρ i| ^ k ∂ρ := by
      rw [integral_const_mul, integral_finsetSum _ (fun _ _ => integrable_cond η q E hmass _)]
    _ ≤ (‖t‖ ^ k * (d : ℝ) ^ (k - 1)) *
        ∑ _i : Fin d, centeredConstant c k * s ^ k := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun i _ => centered_coordinate η q E hc hE hs hmean i k)
    _ = directionalConstant d c k * s ^ k * ‖t‖ ^ k := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, directionalConstant]
      ring

end Moments

/-- All constants precede the varying conditional binomial law and scale. The only
input about the conditioning event is its actual probability lower bound. -/
theorem uniform_directional_moments (d : ℕ) {c U : ℝ} (hc : 0 < c) (hU : 1 ≤ U) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (η : Fin d → ℕ) (q : Fin d → Binomial.Probability)
        (E : Set (Fin d → ℕ)) (s : ℝ),
        c ≤ (Binomial.law η q).real E → 1 ≤ s →
        (∀ i, (η i : ℝ) * (q i : ℝ) ≤ U * s ^ 2) →
        (∀ f : (Fin d → ℕ) → ℝ, Integrable f (cond (Binomial.law η q) E)) ∧
        IsProbabilityMeasure (cond (Binomial.law η q) E) ∧
        ∀ t : Fin d → ℝ,
          varianceForm (cond (Binomial.law η q) E) t ≤ C * s ^ 2 * ‖t‖ ^ 2 ∧
          thirdMoment (cond (Binomial.law η q) E) t ≤ C * s ^ 3 * ‖t‖ ^ 3 := by
  let C := max 1 (max (Moments.directionalConstant d c 2 * U ^ 2)
    (Moments.directionalConstant d c 3 * U ^ 3))
  refine ⟨C, le_max_left _ _, ?_⟩
  intro η q E s hE hs hmean
  have hmass : (Binomial.law η q) E ≠ 0 :=
    (ENNReal.toReal_pos_iff.mp (hc.trans_le hE)).1.ne'
  refine ⟨Moments.integrable_cond η q E hmass, cond_isProbabilityMeasure hmass, ?_⟩
  intro t
  have hs0 : 0 ≤ s := by linarith
  have hU0 : 0 ≤ U := by linarith
  have hscale : 1 ≤ U * s := by nlinarith [mul_nonneg (sub_nonneg.mpr hU) (sub_nonneg.mpr hs)]
  have hmean' (i : Fin d) : (η i : ℝ) * (q i : ℝ) ≤ (U * s) ^ 2 := by
    apply (hmean i).trans
    have hUU : U ≤ U ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hUU (sq_nonneg s)]
  have htwo := Moments.directional_moment η q E hc hE hscale hmean' t 2 (by norm_num)
  have hthree := Moments.directional_moment η q E hc hE hscale hmean' t 3 (by norm_num)
  have hC2 : Moments.directionalConstant d c 2 * U ^ 2 ≤ C :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hC3 : Moments.directionalConstant d c 3 * U ^ 3 ≤ C :=
    (le_max_right _ _).trans (le_max_right _ _)
  constructor
  · simp only [sq_abs] at htwo
    change (∫ x, centeredProjection _ t x ^ 2 ∂_) ≤ _
    calc
      _ ≤ Moments.directionalConstant d c 2 * (U * s) ^ 2 * ‖t‖ ^ 2 := htwo
      _ = (Moments.directionalConstant d c 2 * U ^ 2) * s ^ 2 * ‖t‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2 (sq_nonneg s)) (sq_nonneg _)
  · change (∫ x, |centeredProjection _ t x| ^ 3 ∂_) ≤ _
    calc
      _ ≤ Moments.directionalConstant d c 3 * (U * s) ^ 3 * ‖t‖ ^ 3 := hthree
      _ = (Moments.directionalConstant d c 3 * U ^ 3) * s ^ 3 * ‖t‖ ^ 3 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC3 (pow_nonneg hs0 _)) (by positivity)

end MajorityDynamics.Probability.ConditionedBinomialLocalCLT
