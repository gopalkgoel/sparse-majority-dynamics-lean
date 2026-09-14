import MajorityDynamics.Binomial.GaussianComparison

/-! Uniform simultaneous applications of the proved A.2 Gaussian comparison.
The finite family may contain different numbers of constraints and different
monomials. Its constants and threshold precede all varying parameters. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace MajorityDynamics.Idealized.RowLimits
open Binomial Binomial.Approximation

/-- All finitely many row/event/moment applications share one uniform constant
and one large-N threshold. This applies the proved theorem, not a new input. -/
theorem gaussian_comparison_finite {ι : Type*} [Fintype ι]
    (θ T : ℝ) (hθ : 1 / 2 < θ) (hθ' : θ < 1) (hT : 1 < T)
    (d : ℕ) (hd : 0 < d) (r : ι → ℕ)
    (M : ∀ j, Fin (r j) → Fin d → ℤ) (hM : ∀ j, OrthogonalRows (M j))
    (strict : ∀ j, Fin (r j) → Bool) (c : ι → ℝ) (e : ι → Fin d → ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ p : Probability, Density θ T N p →
      ∀ η : Fin d → ℕ, Sizes T N η → ∀ α : Fin d → ℝ,
      (∀ i, |α i| < T) → ∀ j,
      (∀ k, |∑ i, (M j k i : ℝ) * η i| < T * N / scale N p) →
      |(∫ a in inequalityEvent (fun k i => (M j k i : ℝ)) (strict j),
          monomial (c j) (e j) (centered p η a) ∂Binomial.law η (gaussianTilt p η α)) -
        (∫ x in gaussianEvent (M j) p η, monomial (c j) (e j) x ∂gaussianLaw p η α)| ≤
        C * (scale N p) ^ (((∑ i, e j i : ℕ) : ℝ) - 1) *
          (Real.log N) ^ (3 + (∑ i, e j i) + d) := by
  classical
  choose C hC N₀ h using fun j =>
    gaussian_comparison θ T hθ hθ' hT d hd (r j) (M j) (hM j) (strict j) (c j) (e j)
  let C' : ℝ := 1 + ∑ j, |C j|
  have hC' : 0 < C' := by dsimp [C']; positivity
  refine ⟨C', hC', max 1 (Finset.univ.sup N₀), le_max_left _ _, ?_⟩
  intro N hN p hp η hη α hα j hbal
  have hNj : N₀ j ≤ N :=
    (Finset.le_sup (f := N₀) (Finset.mem_univ j)).trans ((le_max_right _ _).trans hN)
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hbound := h j N hNj p hp η hη hbal α hα
  have hCj : C j ≤ C' := by
    have hi := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => abs_nonneg (C i))
      (Finset.mem_univ j)
    dsimp [C']
    linarith [le_abs_self (C j)]
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
  apply hbound.trans
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_right hCj
    exact Real.rpow_nonneg (Real.sqrt_nonneg _) _
  · positivity

end MajorityDynamics.Idealized.RowLimits
