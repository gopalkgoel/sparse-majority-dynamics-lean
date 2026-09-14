import MajorityDynamics.StrongBijection
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Positive derivatives and smooth global inverses

These generic analytic helpers implement the injectivity and inverse-function
steps of `latest/main.tex`, Appendix D.2, `thm:orthant-bijection`.
They have no Gaussian hypotheses or dependencies.

Strict positivity of the derivative's quadratic form gives strict increase
along each line, and hence injectivity. A smooth injective map with invertible
derivatives has a smooth chosen inverse on its range: its global left inverse
agrees locally with the inverse supplied by the inverse function theorem.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff RealInnerProductSpace

namespace MajorityDynamics.Analysis

section PositiveDerivative

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Positive quadratic forms of all derivatives imply strict monotonicity
between any two distinct points. The scalar restriction to their joining line
has a strictly positive derivative. -/
theorem inner_sub_pos_of_hasFDerivAt_pos
    {G : E → E} {A : E → E →L[ℝ] E}
    (hderiv : ∀ x, HasFDerivAt G (A x) x)
    (hpos : ∀ x v, v ≠ 0 → 0 < ⟪A x v, v⟫)
    {x y : E} (hxy : x ≠ y) :
    0 < ⟪G y - G x, y - x⟫ := by
  have hv : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have hline (t : ℝ) :
      HasDerivAt (fun s : ℝ => x + s • (y - x)) (y - x) t := by
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id t).smul_const (y - x)).const_add x
  have hscalar (t : ℝ) :
      HasDerivAt (fun s : ℝ => ⟪G (x + s • (y - x)), y - x⟫)
        ⟪A (x + t • (y - x)) (y - x), y - x⟫ t := by
    simpa only [Function.comp_apply, inner_zero_right, zero_add] using
      ((hderiv (x + t • (y - x))).comp_hasDerivAt t (hline t)).inner ℝ
        (hasDerivAt_const t (y - x))
  have hmono := strictMono_of_hasDerivAt_pos hscalar
    (fun t => hpos (x + t • (y - x)) (y - x) hv)
  have hlt := hmono (show (0 : ℝ) < 1 by norm_num)
  simpa only [zero_smul, add_zero, one_smul, ← add_sub_assoc, add_sub_cancel_left,
    inner_sub_left, sub_pos] using hlt

/-- A vector-valued map whose derivative has positive quadratic form
everywhere is injective. Symmetry and uniform lower bounds are unnecessary. -/
theorem injective_of_hasFDerivAt_pos
    {G : E → E} {A : E → E →L[ℝ] E}
    (hderiv : ∀ x, HasFDerivAt G (A x) x)
    (hpos : ∀ x v, v ≠ 0 → 0 < ⟪A x v, v⟫) :
    Function.Injective G := by
  intro x y hG
  by_contra hxy
  have hlt := inner_sub_pos_of_hasFDerivAt_pos hderiv hpos hxy
  simp only [hG, sub_self, inner_zero_left, lt_self_iff_false] at hlt

end PositiveDerivative

section SmoothInverse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The globally chosen inverse of an injective smooth map is smooth at the
image of a point where its derivative is invertible. Its global left-inverse
identity identifies it locally with the checked local inverse. -/
theorem contDiffAt_invFun_of_hasFDerivAt
    {f : E → E} {a : E} {n : WithTop ℕ∞} {e : E ≃L[ℝ] E}
    (hf : ContDiffAt ℝ n f a) (hinj : Function.Injective f)
    (hderiv : HasFDerivAt f (e : E →L[ℝ] E) a) (hn : n ≠ 0) :
    ContDiffAt ℝ n (Function.invFun f) (f a) := by
  apply (hf.to_localInverse hderiv hn).congr_of_eventuallyEq
  exact (hf.hasStrictFDerivAt' hderiv hn).localInverse_unique
    (Eventually.of_forall (Function.leftInverse_invFun hinj))

/-- Package a smooth bijection onto an open set as a `StrongBijection`, deriving
smoothness of its ambient chosen inverse from the inverse function theorem.
The forward map is exactly the prescribed function. -/
theorem exists_strongBijection_of_hasFDerivAt
    {O : Set E} {f : E → E} (hO : IsOpen O) (hf : ContDiff ℝ ∞ f)
    (hmaps : MapsTo f univ O) (hinj : Function.Injective f)
    (hsurj : ∀ y ∈ O, ∃ x, f x = y)
    (hderiv : ∀ x, ∃ e : E ≃L[ℝ] E, HasFDerivAt f (e : E →L[ℝ] E) x) :
    ∃ b : StrongBijection O, b.toFun = f := by
  refine ⟨{
    toFun := f
    invFun := Function.invFun f
    isOpen_target := hO
    mapsTo := hmaps
    left_inv := Function.leftInverse_invFun hinj
    right_inv := fun y hy => Function.invFun_eq (hsurj y hy)
    smooth := hf
    smooth_inv := ?_ }, rfl⟩
  intro y hy
  obtain ⟨x, rfl⟩ := hsurj y hy
  obtain ⟨e, he⟩ := hderiv x
  exact (contDiffAt_invFun_of_hasFDerivAt hf.contDiffAt hinj he (by simp)).contDiffWithinAt

end SmoothInverse

end MajorityDynamics.Analysis
