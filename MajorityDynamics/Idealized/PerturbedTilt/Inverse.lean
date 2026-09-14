import MajorityDynamics.Idealized.PerturbedTilt.Basic
import MajorityDynamics.Idealized.Process.SolvabilityRows

/-! Appendix D applied to the actual universal covariance matrix. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace MajorityDynamics.Idealized.PerturbedTilt
open Universal LinearResponse

def covarianceBijection (n : ℕ) (s : History (n + 1)) :
    StrongBijection (Set.univ : Set (Row (n + 1))) where
  toFun x := WithLp.toLp 2 (Matrix.vecMul (fun t => x t) (conditionalCovariance n s))
  invFun y := WithLp.toLp 2 (betaFor n s (fun t => y t))
  isOpen_target := isOpen_univ
  mapsTo _ _ := mem_univ _
  left_inv x := by
    ext t
    exact congrFun (betaFor_unique n s _ (fun t => x t) rfl).symm t
  right_inv y _ := by
    ext t
    exact congrFun (betaFor_spec n s (fun t => y t)) t
  smooth := by
    apply (contDiff_piLp 2).mpr
    intro t
    change ContDiff ℝ ∞ (fun x : Row (n + 1) => ∑ u, x u * conditionalCovariance n s u t)
    fun_prop
  smooth_inv := by
    apply ContDiff.contDiffOn
    apply (contDiff_piLp 2).mpr
    intro t
    change ContDiff ℝ ∞ (fun x : Row (n + 1) => ∑ u, x u * (conditionalCovariance n s)⁻¹ u t)
    fun_prop

theorem covarianceBijection_apply (n : ℕ) (s : History (n + 1)) (x : Row (n + 1)) (t) :
    (covarianceBijection n s).toFun x t = covarianceAction n s x t := by
  change (∑ u, x u * conditionalCovariance n s u t) = _
  unfold covarianceAction
  apply Finset.sum_congr rfl
  intro u _
  rw [conditionalCovariance_symm n s u t, mul_comm]

theorem covarianceBijection_beta (n : ℕ) (s : History (n + 1)) (t) :
    (covarianceBijection n s).toFun (WithLp.toLp 2 (β n s)) t = ε n t :=
  β_spec n s t

/-- A named uniqueness theorem for all open-cube solutions, independent of
any approximation certificate. Support geometry is proved from trial sizes. -/
theorem all_solving_tilts_unique {n : ℕ} (sizes : Local.Sizes n)
    (hsize : ∀ t, 2 * n + 5 ≤ sizes t) (edges : Local.EdgeCounts n)
    {q q' : Local.Tilt n} (hq : Local.Solves sizes edges q)
    (hq' : Local.Solves sizes edges q') : q = q' :=
  Process.solving_tilt_unique sizes hsize edges hq hq'

/-- Uniform inverse constants for the finitely many actual Gaussian rows. -/
theorem stable_covariance_inverse (n : ℕ) :
    ∃ R : ℝ, 0 < R ∧ ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 < C ∧
      ∀ E : ℝ, 0 < E → E < a → ∀ s : History (n + 1),
      ∀ g : Row (n + 1) → Row (n + 1), Continuous g →
        (∀ x, (∀ t, |x t| ≤ R) → ∀ t, |g x t - covarianceAction n s x t| ≤ E) →
        ∀ y : Row (n + 1), (∀ t, |y t - ε n t| ≤ E) →
        ∃ x : Row (n + 1), g x = y ∧ (∀ t, |x t| ≤ R) ∧
          ∀ t, |x t - β n s t| ≤ C * E := by
  classical
  have hdim : 1 ≤ Fintype.card (Fin (n + 1) → Bool) := Fintype.card_pos
  have hsingle (s : History (n + 1)) := Process.stable_inverse_coordinates hdim
    (covarianceBijection n s) (WithLp.toLp 2 (β n s))
  choose R hR a ha C hC hsolve using hsingle
  let R' := 1 + ∑ s, |R s|
  let C' := 1 + ∑ s, |C s|
  have hR' : 0 < R' := by dsimp [R']; positivity
  have hC' : 0 < C' := by dsimp [C']; positivity
  have bound (f : History (n + 1) → ℝ) (s) : f s ≤ 1 + ∑ u, |f u| := by
    have := Finset.single_le_sum (fun u _ => abs_nonneg (f u)) (Finset.mem_univ s)
    linarith [le_abs_self (f s)]
  obtain ⟨a', ha', hamin⟩ := RowLimits.finite_common_positive a ha
  refine ⟨R', hR', a', ha', C', hC', ?_⟩
  intro E hE hEa s g hg hgclose y hy
  obtain ⟨x, hx, hxR, hxβ⟩ := hsolve s E hE (hEa.trans_le (hamin s)) g hg
    (fun z hz t => by
      rw [covarianceBijection_apply]
      exact hgclose z (fun u => (hz u).trans (bound R s)) t)
    y (fun t => by rw [covarianceBijection_beta]; exact hy t)
  exact ⟨x, hx, fun t => (hxR t).trans (bound R s),
    fun t => (hxβ t).trans (mul_le_mul_of_nonneg_right (bound C s) hE.le)⟩

end MajorityDynamics.Idealized.PerturbedTilt
