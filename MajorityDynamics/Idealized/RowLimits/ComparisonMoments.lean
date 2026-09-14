import MajorityDynamics.Idealized.RowLimits.AssemblyInterfaces
import MajorityDynamics.Idealized.RowLimits.RawComparison

/-! Uniform event-indexed compact controls for the final E.3 assembly. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped NNReal
namespace MajorityDynamics.Idealized.RowLimits
open Universal Analysis
variable {n : ℕ}

theorem actualGaussianMoment_eq_parameterMoment (N : ℕ) (p : Binomial.Probability)
    (sizes : Local.Sizes n) (s : History (n + 1)) (σ : Row (n + 1)) (b : Option Bool)
    (o : MomentKind (Fintype.card (Fin (n + 1) → Bool))) :
    actualGaussianMoment N p sizes s σ b o =
      parameterMoment (eventMatrix s b) o (actualNormalizedParameters N p sizes s σ b) := by
  exact (parameterMoment_eq_integral _ _ _).symm

/-- The canonical lower constant is precisely the choice made before ell and θ
in the final theorem, so this adapter does not change its dependency. -/
theorem eventwise_compact_lower (n : ℕ) (R T : ℝ) :
    ∀ (s : History (n + 1)) (b : Option Bool), ∀ z ∈ gaussianBox n (eventRows n b) R T,
      (gaussian_boxes_uniform_lower n R T).choose ≤ GaussianRegularity.mass (eventMatrix s b) z := by
  intro s b
  have h := (gaussian_boxes_uniform_lower n R T).choose_spec
  cases b with
  | none => simpa only [eventMatrix_none, eventRows] using h.2.1 s
  | some b => simpa only [eventMatrix_some, eventRows] using h.2.2 s b

/-- A common raw-moment bound at least one also accommodates probabilities. -/
theorem eventwise_compact_control (n : ℕ) (R T : ℝ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∃ L : ℝ≥0, ∀ (s : History (n + 1)) (b : Option Bool),
      GaussianControl (eventMatrix s b) (gaussianBox n (eventRows n b) R T) B L := by
  obtain ⟨B, _, L, hh, hc⟩ := gaussian_boxes_uniform_control n R T
  refine ⟨max B 1, le_max_right _ _, L, ?_⟩
  intro s b
  cases b with
  | none => simpa only [eventMatrix_none, eventRows] using (hh s).mono (le_max_left B 1) le_rfl
  | some b => simpa only [eventMatrix_some, eventRows] using (hc s b).mono (le_max_left B 1) le_rfl

end MajorityDynamics.Idealized.RowLimits
