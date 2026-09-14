import MajorityDynamics.Idealized.RowLimits.AssemblyInterfaces

/-! Uniform geometry packaged over history and child events simultaneously. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace MajorityDynamics.Idealized.RowLimits
open Universal Binomial Binomial.Approximation
variable {n : ℕ}

def distanceConstant (n : ℕ) (R : ℝ) : ℝ :=
  (Fintype.card (Fin (n + 1) → Bool) + (n + 1) + 1 : ℝ) * parameterErrorConstant n R

theorem distanceConstant_pos (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    0 < distanceConstant n R := by
  have hK := (parameterErrorConstant_bounds (n := n) R hR).1
  dsimp [distanceConstant]
  positivity

structure EventGeometry (N : ℕ) (p : Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (σ : Row (n + 1)) (T R : ℝ) (ell : ℕ) (ξ : ℝ) : Prop where
  actual_mem : ∀ b, actualNormalizedParameters N p sizes s σ b ∈ gaussianBox n (eventRows n b) R T
  target_mem : ∀ b, targetParameters σ b (shift N p sizes) ∈ gaussianBox n (eventRows n b) R T
  target_zero_mem : ∀ b, targetParameters σ b 0 ∈ gaussianBox n (eventRows n b) R T
  distance : ∀ b, dist (actualNormalizedParameters N p sizes s σ b)
    (targetParameters σ b (shift N p sizes)) ≤ distanceConstant n R * error ell N p ξ
  distance_zero : |shift N p sizes| ≤ ξ → ∀ b,
    dist (actualNormalizedParameters N p sizes s σ b) (targetParameters σ b 0) ≤
      distanceConstant n R * error ell N p ξ

 theorem eventual_event_geometry (θ T R : ℝ) (ell : ℕ)
    (hθ : θ < 1) (hT : 0 < T) (hR : 0 ≤ R) :
    ∀ᶠ N : ℕ in atTop, 0 < N ∧ 1 ≤ Real.log (N : ℝ) ∧
      ∀ p : Probability, Density θ T N p → ∀ ξ : ℝ, 0 ≤ ξ → ξ ≤ T →
      ∀ s : History (n + 1), ∀ sizes : Local.Sizes n,
        AdmissibleSizes N p ell T ξ s sizes →
        (∀ t, 0 < sizes t) ∧ ∀ σ : Row (n + 1), (∀ t, |σ t| ≤ R) →
          |shift N p sizes| ≤ T ∧ EventGeometry N p sizes s σ T R ell ξ := by
  filter_upwards [eventual_parameters_mem (n := n) θ T R ell hθ hT hR] with N hN
  refine ⟨hN.1, hN.2.1, ?_⟩
  intro p hp ξ hξ hξT s sizes ha
  have hs := hN.2.2 p hp ξ hξ hξT s sizes ha
  refine ⟨hs.1, ?_⟩
  intro σ hσ
  have hg := hs.2 σ hσ
  have hd := normalized_parameter_distances hN.1 hN.2.1 ha hs.1 hξ hR σ hσ
  refine ⟨hg.1, ?_⟩
  constructor
  · intro b
    cases b with
    | none => simpa only [actualNormalizedParameters_none, eventRows,
        ← rowParameterBox_eq_gaussianBox] using hg.2.1
    | some b => simpa only [actualNormalizedParameters_some, eventRows,
        ← rowParameterBox_eq_gaussianBox] using (hg.2.2.2 b).1
  · intro b
    cases b with
    | none => simpa only [targetParameters, eventRows,
        ← rowParameterBox_eq_gaussianBox] using hg.2.2.1
    | some b => simpa only [targetParameters, eventRows,
        ← rowParameterBox_eq_gaussianBox] using (hg.2.2.2 b).2.1
  · intro b
    cases b with
    | none => simpa only [targetParameters, eventRows,
        ← rowParameterBox_eq_gaussianBox] using hg.2.2.1
    | some b => simpa only [targetParameters, eventRows,
        ← rowParameterBox_eq_gaussianBox] using (hg.2.2.2 b).2.2
  · intro b
    cases b with
    | none => simpa only [actualNormalizedParameters_none, targetParameters,
        distanceConstant] using hd.1
    | some b => simpa only [actualNormalizedParameters_some, targetParameters,
        distanceConstant] using hd.2.1 b
  · intro hu b
    cases b with
    | none => simpa only [actualNormalizedParameters_none, targetParameters,
        distanceConstant] using hd.1
    | some b => simpa only [actualNormalizedParameters_some, targetParameters,
        distanceConstant] using hd.2.2 hu b

end MajorityDynamics.Idealized.RowLimits
