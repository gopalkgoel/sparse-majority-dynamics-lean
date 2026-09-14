import MajorityDynamics.Binomial.GaussianProbability
import MajorityDynamics.Analysis.GaussianMoments
import MajorityDynamics.Analysis.TailMoment

/-! # Integrability and uniform second moments of the actual Gaussian monomials -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace MajorityDynamics.Binomial.Approximation
variable {d : ℕ}

theorem integrable_gaussian_monomial (p : Probability) (η : Fin d → ℕ) (α : Fin d → ℝ)
    (c : ℝ) (e : Fin d → ℕ) : Integrable (monomial c e) (gaussianLaw p η α) :=
  (Integrable.fintype_prod (fun i => Analysis.integrable_gaussian_power
    (gaussianMean p η α i) (gaussianVariance p η i) (e i))).const_mul c

theorem monomial_sq (c : ℝ) (e : Fin d → ℕ) (x : Fin d → ℝ) :
    monomial c e x ^ 2 = monomial (c ^ 2) (fun i => 2 * e i) x := by
  simp only [monomial, mul_pow, ← Finset.prod_pow, ← pow_mul, Nat.mul_comm]

theorem memLp_gaussian_monomial (p : Probability) (η : Fin d → ℕ) (α : Fin d → ℝ)
    (c : ℝ) (e : Fin d → ℕ) : MemLp (monomial c e) 2 (gaussianLaw p η α) := by
  apply (memLp_two_iff_integrable_sq (integrable_gaussian_monomial p η α c e).aestronglyMeasurable).mpr
  simpa only [monomial_sq] using integrable_gaussian_monomial p η α (c ^ 2) (fun i => 2 * e i)

def monomialMomentConstant (T c : ℝ) (e : Fin d → ℕ) : ℝ :=
  c ^ 2 * ∏ i, Analysis.normalMomentBound T (2 * e i)

theorem monomialMomentConstant_nonneg (T c : ℝ) (e : Fin d → ℕ) (hT : 0 ≤ T) :
    0 ≤ monomialMomentConstant T c e :=
  mul_nonneg (sq_nonneg _) (Finset.prod_nonneg fun _ _ => Analysis.normalMomentBound_nonneg T _ hT)

theorem gaussian_second_moment_le (p : Probability) (η : Fin d → ℕ) (α : Fin d → ℝ)
    (c : ℝ) (e : Fin d → ℕ) (T U : ℝ) (hT : 0 ≤ T) (_hU : 0 ≤ U)
    (hα : ∀ i, |α i| ≤ T) (hscale : ∀ i, Real.sqrt ((p : ℝ) * η i) ≤ U) :
    (∫ x, monomial c e x ^ 2 ∂gaussianLaw p η α) ≤
      monomialMomentConstant T c e * U ^ (2 * ∑ i, e i) := by
  have hcoord (i : Fin d) :
      (∫ x, x ^ (2 * e i) ∂gaussianReal (gaussianMean p η α i) (gaussianVariance p η i)) ≤
        U ^ (2 * e i) * Analysis.normalMomentBound T (2 * e i) := by
    have h := Analysis.gaussian_absolute_moment_le (Real.sqrt ((p : ℝ) * η i)) (α i) T (2 * e i)
      (Real.sqrt_nonneg _) hT (hα i)
    have hμ : 0 ≤ (p : ℝ) * η i := mul_nonneg p.property.1.le (Nat.cast_nonneg _)
    have hv : NNReal.mk ((Real.sqrt ((p : ℝ) * η i)) ^ 2) (sq_nonneg _) = gaussianVariance p η i := by
      apply NNReal.eq
      exact Real.sq_sqrt hμ
    rw [hv] at h
    have habs : (fun x : ℝ => |x| ^ (2 * e i)) = (fun x : ℝ => x ^ (2 * e i)) := by
      funext x
      rw [pow_mul, pow_mul, sq_abs]
    rw [habs] at h
    exact h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.sqrt_nonneg _) (hscale i) _)
      (Analysis.normalMomentBound_nonneg T _ hT))
  simp_rw [monomial_sq]
  simp only [monomial]
  change (∫ x, c ^ 2 * ∏ i, x i ^ (2 * e i) ∂Measure.pi (fun i => gaussianReal (gaussianMean p η α i) (gaussianVariance p η i))) ≤ _
  rw [integral_const_mul, integral_fintype_prod_eq_prod (fun (i : Fin d) (x : ℝ) => x ^ (2 * e i)), monomialMomentConstant, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg c)
  calc
    _ ≤ ∏ i, U ^ (2 * e i) * Analysis.normalMomentBound T (2 * e i) := by
      apply Finset.prod_le_prod
      · intro i _
        apply integral_nonneg
        intro x
        change 0 ≤ x ^ (2 * e i)
        rw [pow_mul]
        positivity
      · exact fun i _ => hcoord i
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum]
      ring

end MajorityDynamics.Binomial.Approximation
