import MajorityDynamics.Idealized.RowLimits.RawEstimates
import MajorityDynamics.Idealized.RowLimits.ComparisonTargets

/-! Turn the A.2 raw-moment approximation and E.2 parameter regularity into
raw estimates at the limiting row. Positivity uses the vanishing A.2 error
alone, so it never incorrectly requires the imbalance parameter to vanish. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal
open MajorityDynamics.Universal MajorityDynamics.Analysis
namespace MajorityDynamics.Idealized.RowLimits

/-- The finite family of Gaussian raw moments. -/
def parameterMoment {d r : ℕ} (M : Matrix (Fin r) (Fin d) ℝ) :
    MomentKind d → GaussianRegularity.Parameters d r → ℝ
  | .inl _ => GaussianRegularity.mass M
  | .inr (.inl t) => GaussianRegularity.firstMoment M t
  | .inr (.inr (t,t')) => GaussianRegularity.secondMoment M t t'

theorem parameterMoment_eq_integral {d r : ℕ} (M : Matrix (Fin r) (Fin d) ℝ)
    (o : MomentKind d) (x : GaussianRegularity.Parameters d r) :
    parameterMoment M o x = ∫ z in GaussianRegularity.event M x.2,
      momentValue o z.ofLp ∂GaussianRegularity.law x := by
  rcases o with u | (t | ⟨t,t'⟩)
  · simp [parameterMoment, momentValue, GaussianRegularity.mass, measureReal_def]
  · rfl
  · rfl

theorem GaussianControl.parameterMoment_lipschitz {d r : ℕ}
    {M : Matrix (Fin r) (Fin d) ℝ} {P : Set (GaussianRegularity.Parameters d r)}
    {B : ℝ} {L : ℝ≥0} (h : GaussianControl M P B L) (o : MomentKind d) :
    LipschitzOnWith L (parameterMoment M o) P := by
  rcases o with u | (t | ⟨t,t'⟩)
  · exact h.mass_lipschitz
  · exact h.first_lipschitz t
  · exact h.second_lipschitz t t'

/-- Generic raw comparison adapter for the history or either child event. -/
theorem eventRawEstimates_of_comparison {n r N : ℕ} {p : Binomial.Probability}
    {sizes : Local.Sizes n} {s : History (n + 1)} {σ : Row (n + 1)}
    {S : Finset (Binomial.Box (Local.trials sizes s))} {E : Set (Row (n + 1))}
    {M : Matrix (Fin r) (History (n + 1)) ℝ}
    {P : Set (GaussianRegularity.Parameters (Fintype.card (Fin (n + 1) → Bool)) r)}
    {B A K c₀ δ ε : ℝ} {L : ℝ≥0}
    (hcontrol : GaussianControl M P B L)
    {x y : GaussianRegularity.Parameters (Fintype.card (Fin (n + 1) → Bool)) r}
    (hx : x ∈ P) (hy : y ∈ P) (hc : 0 < c₀) (hA : 0 ≤ A)
    (hmx : c₀ ≤ GaussianRegularity.mass M x)
    (hmy : c₀ ≤ GaussianRegularity.mass M y)
    (hraw : ∀ o, |binomialNormalizedMoment N p sizes s S
      (fun t => (p : ℝ) * Local.trials sizes s t) (Real.sqrt ((p : ℝ) * N)) o σ -
      parameterMoment M o x| ≤ A * δ)
    (hxy : dist x y ≤ K * ε) (hδε : δ ≤ ε) (hsmall : A * δ ≤ c₀ / 2)
    (hzero : gaussianMass σ E = GaussianRegularity.mass M y)
    (hfirst : ∀ t, gaussianFirst σ E t = GaussianRegularity.firstMoment M t y)
    (hsecond : ∀ t t', gaussianSecond σ E t t' = GaussianRegularity.secondMoment M t t' y) :
    EventRawEstimates N p sizes s σ S E (c₀ / 2) B (A + (L : ℝ) * K) ε := by
  have hall (o) := raw_error_of_comparison (hcontrol.parameterMoment_lipschitz o)
    hx hy (hraw o) hxy
  have herror (o) : |binomialNormalizedMoment N p sizes s S
      (fun t => (p : ℝ) * Local.trials sizes s t) (Real.sqrt ((p : ℝ) * N)) o σ -
      parameterMoment M o y| ≤ (A + (L : ℝ) * K) * ε := by
    exact (hall o).trans (by nlinarith [mul_le_mul_of_nonneg_left hδε hA])
  have hmass := hraw (.inl ())
  simp only [binomialNormalizedMoment_zero, parameterMoment] at hmass
  refine ⟨denominator_lower_bound hmx hmass hsmall, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hzero]
    linarith
  · intro t
    rw [hfirst]
    exact hcontrol.first_bound y hy t
  · intro t t'
    rw [hsecond]
    exact hcontrol.second_bound y hy t t'
  · rw [hzero]
    simpa only [binomialNormalizedMoment_zero, parameterMoment] using herror (.inl ())
  · intro t
    rw [hfirst]
    exact herror (.inr (.inl t))
  · intro t t'
    rw [hsecond]
    exact herror (.inr (.inr (t,t')))

end MajorityDynamics.Idealized.RowLimits
