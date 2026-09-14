import MajorityDynamics.Analysis.GaussianRegularity.Basic
import Mathlib.MeasureTheory.Group.MeasurableEquiv

/-!
# Translating moving Gaussian thresholds

A right inverse of a full-row-rank linear map turns a varying orthant threshold
into a translation of the mean and of the moment observable. This exact change
of variables avoids a separate conditional Gaussian calculation on each boundary
hyperplane in the proof of paper Lemma E.2. It does not, by itself, assert the
uniform analytic estimates in that lemma.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MajorityDynamics.Analysis.GaussianRegularity
open ConditionalGaussian

variable {d r : ℕ}

/-- Rectangular matrix action in Euclidean norms. -/
def rectangularCLM (M : Matrix (Fin r) (Fin d) ℝ) : Space d →L[ℝ] Space r :=
  (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin r)).symm.toContinuousLinearMap.comp
    ((Matrix.toLin' M).toContinuousLinearMap.comp
      (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin d)).toContinuousLinearMap)

@[simp] theorem rectangularCLM_apply (M : Matrix (Fin r) (Fin d) ℝ)
    (x : Space d) (i : Fin r) : rectangularCLM M x i = ∑ j, M i j * x j := rfl

/-- Orthant constraint for a linear map, allowing zero rows. -/
def linearThreshold (M : Space d →L[ℝ] Space r) (u : Space r) : Set (Space d) :=
  {x | ∀ i, -u i ≤ M x i}

theorem linearThreshold_rectangularCLM (M : Matrix (Fin r) (Fin d) ℝ)
    (u : Space r) : linearThreshold (rectangularCLM M) u = event M u := rfl

/-- Surjectivity supplies a continuous linear choice of threshold translation. -/
theorem exists_threshold_rightInverse (M : Space d →L[ℝ] Space r)
    (hM : Function.Surjective M) :
    ∃ R : Space r →L[ℝ] Space d, M.comp R = ContinuousLinearMap.id ℝ (Space r) := by
  exact M.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hM)

/-- The paper's full row rank hypothesis supplies the required right inverse. -/
theorem exists_matrix_threshold_rightInverse (M : Matrix (Fin r) (Fin d) ℝ)
    (hM : M.rank = r) :
    ∃ R : Space r →L[ℝ] Space d,
      (rectangularCLM M).comp R = ContinuousLinearMap.id ℝ (Space r) := by
  apply exists_threshold_rightInverse
  have hrange : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa only [Matrix.rank, Module.finrank_pi, Module.finrank_self, mul_one,
      Fintype.card_fin] using hM
  have hsurj := LinearMap.range_eq_top.mp hrange
  intro y
  obtain ⟨x, hx⟩ := hsurj (fun i => y i)
  refine ⟨(EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin d)).symm x, ?_⟩
  ext i
  exact congrFun hx i

/-- A threshold becomes zero after translation by a right inverse. -/
theorem mem_linearThreshold_iff_add (M : Space d →L[ℝ] Space r)
    (R : Space r →L[ℝ] Space d) (hR : M.comp R = ContinuousLinearMap.id ℝ (Space r))
    (u : Space r) (x : Space d) :
    x ∈ linearThreshold M u ↔ x + R u ∈ linearThreshold M 0 := by
  have hRu : M (R u) = u := congrArg (fun f : Space r →L[ℝ] Space r => f u) hR
  simp only [linearThreshold, Set.mem_ofPred_eq, map_add, hRu]
  simp only [PiLp.zero_apply, neg_zero, PiLp.add_apply]
  exact forall_congr' (fun i => by constructor <;> intro h <;> linarith)

/-- Translating a multivariate Gaussian changes its mean and preserves covariance. -/
theorem gaussianLaw_map_add (S : Covariance d) (m a : Space d) :
    (gaussianLaw S m).map (fun x => x + a) = gaussianLaw S (m + a) := by
  unfold gaussianLaw multivariateGaussian
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  ext x
  simp only [Function.comp_apply]
  abel_nf

/-- Exact integral transport, valid for any observable (without integrability hypotheses). -/
theorem integral_gaussianLaw_translate (S : Covariance d) (m a : Space d)
    (f : Space d → ℝ) :
    (∫ x, f x ∂gaussianLaw S m) =
      ∫ y, f (y - a) ∂gaussianLaw S (m + a) := by
  rw [← gaussianLaw_map_add S m a]
  have h := integral_map_equiv (μ := gaussianLaw S m)
    (MeasurableEquiv.addRight a) (fun y => f (y - a))
  simpa using h.symm

/-- The moving domain is exactly a fixed orthant after shifting the Gaussian mean. -/
theorem threshold_integral_translate (M : Space d →L[ℝ] Space r)
    (R : Space r →L[ℝ] Space d) (hR : M.comp R = ContinuousLinearMap.id ℝ (Space r))
    (S : Covariance d) (m : Space d) (u : Space r) (f : Space d → ℝ) :
    (∫ x in linearThreshold M u, f x ∂gaussianLaw S m) =
      ∫ y in linearThreshold M 0, f (y - R u) ∂gaussianLaw S (m + R u) := by
  have hmeas : MeasurableSet (linearThreshold M u) := by
    simp only [linearThreshold, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le measurable_const (by fun_prop)
  have hmeas0 : MeasurableSet (linearThreshold M (0 : Space r)) := by
    simp only [linearThreshold, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le measurable_const (by fun_prop)
  rw [← integral_indicator hmeas, ← integral_indicator hmeas0]
  rw [integral_gaussianLaw_translate S m (R u)]
  apply integral_congr_ae
  filter_upwards [] with y
  have hy := mem_linearThreshold_iff_add M R hR u (y - R u)
  simp only [sub_add_cancel] at hy
  change (linearThreshold M u).indicator f (y - R u) =
    (linearThreshold M 0).indicator (fun z => f (z - R u)) y
  classical
  by_cases h : y ∈ linearThreshold M 0
  · rw [Set.indicator_of_mem (hy.mpr h), Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem (fun hz => h (hy.mp hz)), Set.indicator_of_notMem h]

/-- The probability is also an exact fixed-event integral after translation. -/
theorem mass_translate (M : Matrix (Fin r) (Fin d) ℝ)
    (R : Space r →L[ℝ] Space d)
    (hR : (rectangularCLM M).comp R = ContinuousLinearMap.id ℝ (Space r))
    (p : Parameters d r) :
    mass M p = ∫ _y in event M 0, (1 : ℝ)
      ∂gaussianLaw (Matrix.diagonal (fun i => p.1.2 i)) (p.1.1 + R p.2) := by
  have h := threshold_integral_translate (rectangularCLM M) R hR
    (Matrix.diagonal (fun i => p.1.2 i)) p.1.1 p.2 (fun _ => (1 : ℝ))
  simpa [linearThreshold_rectangularCLM, mass, law, Measure.real] using h

/-- Exact first-moment reduction to a fixed event and a translated coordinate. -/
theorem firstMoment_translate (M : Matrix (Fin r) (Fin d) ℝ)
    (R : Space r →L[ℝ] Space d)
    (hR : (rectangularCLM M).comp R = ContinuousLinearMap.id ℝ (Space r))
    (p : Parameters d r) (t : Fin d) :
    firstMoment M t p =
      ∫ y in event M 0, (y t - R p.2 t)
        ∂gaussianLaw (Matrix.diagonal (fun i => p.1.2 i)) (p.1.1 + R p.2) := by
  exact threshold_integral_translate (rectangularCLM M) R hR _ _ _ (fun x => x t)

/-- Exact second-moment reduction; the translated observable is quadratic. -/
theorem secondMoment_translate (M : Matrix (Fin r) (Fin d) ℝ)
    (R : Space r →L[ℝ] Space d)
    (hR : (rectangularCLM M).comp R = ContinuousLinearMap.id ℝ (Space r))
    (p : Parameters d r) (t t' : Fin d) :
    secondMoment M t t' p =
      ∫ y in event M 0, (y t - R p.2 t) * (y t' - R p.2 t')
        ∂gaussianLaw (Matrix.diagonal (fun i => p.1.2 i)) (p.1.1 + R p.2) := by
  exact threshold_integral_translate (rectangularCLM M) R hR _ _ _ (fun x => x t * x t')

end MajorityDynamics.Analysis.GaussianRegularity
