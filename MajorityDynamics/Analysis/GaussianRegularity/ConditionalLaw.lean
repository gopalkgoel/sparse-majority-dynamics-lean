import MajorityDynamics.Analysis.GaussianRegularity.Positive
import MajorityDynamics.Analysis.ConditionalGaussian.Conditioning

/-!
# Literal conditioned Gaussian integrals

The normalized quantities in Lemma E.2 agree with expectations and centered
covariances under the actual Gaussian restricted to its conditioning event.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory

namespace MajorityDynamics.Analysis.GaussianRegularity

open ConditionalGaussian

variable {d r : ℕ}

/-- The normalization identity holds for every real observable. -/
theorem integral_condition_eq (M : Matrix (Fin r) (Fin d) ℝ)
    (p : Parameters d r) (f : Space d → ℝ) :
    (∫ x, f x ∂condition (law p) (event M p.2)) =
      (∫ x in event M p.2, f x ∂law p) / mass M p := by
  simp only [condition, integral_smul_measure, ENNReal.toReal_inv,
    smul_eq_mul, mass, div_eq_mul_inv, mul_comm]

theorem conditionalFirst_eq_integral (M : Matrix (Fin r) (Fin d) ℝ)
    (p : Parameters d r) (t : Fin d) :
    conditionalFirst M t p =
      ∫ x, x t ∂condition (law p) (event M p.2) :=
  (integral_condition_eq M p (fun x => x t)).symm

theorem conditionalSecond_eq_integral (M : Matrix (Fin r) (Fin d) ℝ)
    (p : Parameters d r) (t t' : Fin d) :
    conditionalSecond M t t' p =
      ∫ x, x t * x t' ∂condition (law p) (event M p.2) :=
  (integral_condition_eq M p (fun x => x t * x t')).symm

theorem conditioned_isProbabilityMeasure (M : Matrix (Fin r) (Fin d) ℝ)
    (hM : M.rank = r) (p : Parameters d r) (hp : positiveVariance p) :
    IsProbabilityMeasure (condition (law p) (event M p.2)) :=
  condition_isProbabilityMeasure _ _ (event_mass_pos M hM p hp)
    (gaussianLaw_mass_lt_top _ _ _)

theorem conditioned_memLp_two (M : Matrix (Fin r) (Fin d) ℝ)
    (hM : M.rank = r) (p : Parameters d r) (hp : positiveVariance p) :
    MemLp id 2 (condition (law p) (event M p.2)) :=
  memLp_condition _ _ (gaussianLaw_memLp_two _ _) (event_mass_pos M hM p hp)

theorem conditionalCovariance_eq_covariance (M : Matrix (Fin r) (Fin d) ℝ)
    (hM : M.rank = r) (p : Parameters d r) (hp : positiveVariance p)
    (t t' : Fin d) :
    conditionalCovariance M t t' p =
      covariance (fun x : Space d => x t) (fun x => x t')
        (condition (law p) (event M p.2)) := by
  let := conditioned_isProbabilityMeasure M hM p hp
  have h := conditioned_memLp_two M hM p hp
  have hc := covariance_eq_sub (h.eval_piLp t) (h.eval_piLp t')
  simpa only [id_eq, Pi.mul_apply, conditionalCovariance, conditionalSecond_eq_integral,
    conditionalFirst_eq_integral] using hc.symm

end MajorityDynamics.Analysis.GaussianRegularity
