import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! # Gaussian independence of orthogonal projections

All independence assertions here concern the original standard Gaussian law.
Conditioning on history is handled separately in `Conditioning.lean`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace MajorityDynamics.Analysis.GaussianSplit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Covariance of linear forms under the standard Gaussian is the Euclidean
inner product of their coefficient vectors. -/
theorem covariance_inner_stdGaussian (a b : E) :
    covariance (fun x : E ↦ ⟪a, x⟫) (fun x : E ↦ ⟪b, x⟫) (stdGaussian E) = ⟪a, b⟫ := by
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian, innerSL_apply_apply]

/-- Orthogonal Gaussian projections are independent, including when one
subspace is zero-dimensional. -/
theorem indepFun_orthogonal_starProjection (V : Submodule ℝ E) :
    IndepFun Vᗮ.starProjection V.starProjection (stdGaussian E) := by
  have hg : HasGaussianLaw
      (fun x : E ↦ (Vᗮ.starProjection x, V.starProjection x)) (stdGaussian E) :=
    IsGaussian.hasGaussianLaw_id.map (Vᗮ.starProjection.prod V.starProjection)
  apply hg.indepFun_of_covariance_inner
  intro a b
  simp_rw [← Vᗮ.inner_starProjection_left_eq_right, ← V.inner_starProjection_left_eq_right]
  rw [covariance_inner_stdGaussian]
  exact (Submodule.mem_orthogonal' V _).mp (Vᗮ.starProjection_apply_mem a)
    (V.starProjection b) (V.starProjection_apply_mem b)

/-- A scalar Gaussian residual orthogonal to the history subspace is
independent of the complete projected history vector. -/
theorem indepFun_inner_starProjection (V : Submodule ℝ E) {a : E} (ha : a ∈ Vᗮ) :
    IndepFun (fun x : E ↦ ⟪a, x⟫) V.starProjection (stdGaussian E) := by
  have h := (indepFun_orthogonal_starProjection V).comp
    (innerSL ℝ a).measurable measurable_id
  have hfun : (fun x : E ↦ ⟪a, Vᗮ.starProjection x⟫) = (fun x : E ↦ ⟪a, x⟫) := by
    ext x
    rw [← Vᗮ.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr ha]
  change IndepFun (fun x : E ↦ ⟪a, Vᗮ.starProjection x⟫) V.starProjection (stdGaussian E) at h
  rw [hfun] at h
  exact h

/-- Two scalar residuals in the orthogonal complement are jointly independent
of the projected history, even when the residuals are correlated with one
another. -/
theorem indepFun_inner_pair_starProjection (V : Submodule ℝ E) {a b : E}
    (ha : a ∈ Vᗮ) (hb : b ∈ Vᗮ) :
    IndepFun (fun x : E ↦ (⟪a, x⟫, ⟪b, x⟫)) V.starProjection (stdGaussian E) := by
  have h := (indepFun_orthogonal_starProjection V).comp
    ((innerSL ℝ a).prod (innerSL ℝ b)).measurable measurable_id
  have hfun :
      (fun x : E ↦ (⟪a, Vᗮ.starProjection x⟫, ⟪b, Vᗮ.starProjection x⟫)) =
        (fun x : E ↦ (⟪a, x⟫, ⟪b, x⟫)) := by
    funext x
    apply Prod.ext
    · change ⟪a, Vᗮ.starProjection x⟫ = ⟪a, x⟫
      rw [← Vᗮ.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr ha]
    · change ⟪b, Vᗮ.starProjection x⟫ = ⟪b, x⟫
      rw [← Vᗮ.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr hb]
  change IndepFun
    (fun x : E ↦ (⟪a, Vᗮ.starProjection x⟫, ⟪b, Vᗮ.starProjection x⟫))
    V.starProjection (stdGaussian E) at h
  rw [hfun] at h
  exact h

/-- A residual orthogonal to the history and to a final scalar direction is
independent of their joint tuple. This is the independence used to discard the
centered residual after additionally conditioning on the majority decision. -/
theorem indepFun_inner_prod_starProjection (V : Submodule ℝ E) {a y : E}
    (ha : a ∈ Vᗮ) (hay : ⟪a, y⟫ = 0) :
    IndepFun (fun x : E ↦ ⟪a, x⟫)
      (fun x : E ↦ (⟪y, x⟫, V.starProjection x)) (stdGaussian E) := by
  let W : Submodule ℝ E := V ⊔ ℝ ∙ y
  have hVW : V ≤ W := le_sup_left
  have hyW : y ∈ W :=
    (show ℝ ∙ y ≤ W from le_sup_right) (Submodule.mem_span_singleton.mpr ⟨1, one_smul ℝ y⟩)
  have haW : a ∈ Wᗮ := by
    apply (Submodule.mem_orthogonal' W a).mpr
    intro z hz
    obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.mp hz
    rw [inner_add_right, (Submodule.mem_orthogonal' V a).mp ha v hv, zero_add]
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    simp [inner_smul_right, hay]
  have h := (indepFun_inner_starProjection W haW).comp measurable_id
    ((innerSL ℝ y).prod V.starProjection).measurable
  have hfun :
      (fun x : E ↦ (⟪y, W.starProjection x⟫, V.starProjection (W.starProjection x))) =
        (fun x : E ↦ (⟪y, x⟫, V.starProjection x)) := by
    funext x
    apply Prod.ext
    · rw [← W.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr hyW]
    · exact DFunLike.congr_fun (Submodule.starProjection_comp_starProjection_of_le hVW) x
  change IndepFun (fun x : E ↦ ⟪a, x⟫)
    (fun x : E ↦ (⟪y, W.starProjection x⟫, V.starProjection (W.starProjection x)))
    (stdGaussian E) at h
  rw [hfun] at h
  exact h

end MajorityDynamics.Analysis.GaussianSplit
