import MajorityDynamics.Idealized.RowLimits.Centering
import MajorityDynamics.Idealized.RowLimits.Observables
import MajorityDynamics.Idealized.RowLimits.Comparison

/-! Quantitative division of the actual row moments, with independent mass bounds. -/
noncomputable section
open MajorityDynamics.Universal
namespace MajorityDynamics.Idealized.RowLimits
variable {n : ℕ}

def ratioConstant (c B : ℝ) : ℝ := 1 / c + B / c ^ 2

def finalConstant (c B D E : ℝ) : ℝ :=
  1 + D + (ratioConstant c B * D + 1) +
    (1 + 2 * (B / c) + ratioConstant c B * D * E) * (ratioConstant c B * D)

structure EventRawEstimates (N : ℕ) (p : Binomial.Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (σ : Row (n + 1))
    (S : Finset (Binomial.Box (Local.trials sizes s))) (A : Set (Row (n + 1)))
    (c B D ε : ℝ) : Prop where
  binomial_lower : c ≤ binomialMass N p sizes s S σ
  gaussian_lower : c ≤ gaussianMass σ A
  first_bound : ∀ t, |gaussianFirst σ A t| ≤ B
  second_bound : ∀ t t', |gaussianSecond σ A t t'| ≤ B
  mass_error : |binomialMass N p sizes s S σ - gaussianMass σ A| ≤ D * ε
  first_error : ∀ t, |binomialNormalizedMoment N p sizes s S
    (fun t => (p : ℝ) * Local.trials sizes s t) (Real.sqrt ((p : ℝ) * N))
    (.inr (.inl t)) σ - gaussianFirst σ A t| ≤ D * ε
  second_error : ∀ t t', |binomialNormalizedMoment N p sizes s S
    (fun t => (p : ℝ) * Local.trials sizes s t) (Real.sqrt ((p : ℝ) * N))
    (.inr (.inr (t,t'))) σ - gaussianSecond σ A t t'| ≤ D * ε

variable {N : ℕ} {p : Binomial.Probability} {sizes : Local.Sizes n}
    {s : History (n + 1)} {σ : Row (n + 1)}
    {S : Finset (Binomial.Box (Local.trials sizes s))} {A : Set (Row (n + 1))}
    {c B D ε E : ℝ}

theorem EventRawEstimates.mean (h : EventRawEstimates N p sizes s σ S A c B D ε)
    (hc : 0 < c) (hN : 0 < N) (t : History (n + 1)) :
    |(binomialMean N p sizes s S t σ - (p : ℝ) * Local.trials sizes s t) /
      Real.sqrt ((p : ℝ) * N) - gaussianMean σ A t| ≤ ratioConstant c B * (D * ε) := by
  have ha : Real.sqrt ((p : ℝ) * N) ≠ 0 :=
    (Real.sqrt_pos.mpr (mul_pos p.property.1 (Nat.cast_pos.mpr hN))).ne'
  have hm := (hc.trans_le h.binomial_lower).ne'
  have hr := ratio_error hc h.binomial_lower h.gaussian_lower (h.first_bound t)
    (h.first_error t) h.mass_error
  rw [binomialNormalizedMoment_mean N p sizes s S _ _ σ hm ha t] at hr
  exact hr

theorem EventRawEstimates.covariance (h : EventRawEstimates N p sizes s σ S A c B D ε)
    (hc : 0 < c) (hB : 0 ≤ B) (hD : 0 ≤ D) (hE : ε ≤ E)
    (hN : 0 < N) (t t' : History (n + 1)) :
    |binomialCovariance N p sizes s S t t' σ / ((p : ℝ) * N) -
      gaussianCovariance σ A t t'| ≤
        (1 + 2 * (B / c) + ratioConstant c B * D * E) *
          (ratioConstant c B * D) * ε := by
  have ha : Real.sqrt ((p : ℝ) * N) ≠ 0 :=
    (Real.sqrt_pos.mpr (mul_pos p.property.1 (Nat.cast_pos.mpr hN))).ne'
  have hm := (hc.trans_le h.binomial_lower).ne'
  have hk : 0 ≤ ratioConstant c B := by unfold ratioConstant; positivity
  have hb (t) : |gaussianMean σ A t| ≤ B / c := by
    rw [gaussianMean, abs_div, abs_of_pos (hc.trans_le h.gaussian_lower)]
    exact div_le_div₀ hB (h.first_bound t) hc h.gaussian_lower
  have hf (t) := ratio_error hc h.binomial_lower h.gaussian_lower (h.first_bound t)
    (h.first_error t) h.mass_error
  have hs := ratio_error hc h.binomial_lower h.gaussian_lower (h.second_bound t t')
    (h.second_error t t') h.mass_error
  have he : ratioConstant c B * (D * ε) ≤ ratioConstant c B * D * E := by
    nlinarith [mul_nonneg hk hD]
  have hh := covariance_error (hb t) (hb t') (hf t) (hf t') hs he (le_refl _)
  rw [binomialNormalizedMoment_covariance N p sizes s S _ _ σ hm ha t t',
    Real.sq_sqrt (mul_nonneg p.property.1.le (Nat.cast_nonneg N))] at hh
  simpa only [gaussianCovariance, ratioConstant, mul_assoc] using hh

theorem estimates_of_raw {u : ℝ}
    (hH : EventRawEstimates N p sizes s σ (Local.historySupport sizes s)
      (historyEvent s) c B D ε)
    (hJ : ∀ b, EventRawEstimates N p sizes s σ (Local.childSupport sizes s b)
      (shiftedChildEvent s b u) c B D ε)
    (hc : 0 < c) (hB : 0 ≤ B) (hD : 0 ≤ D) (hε : 0 ≤ ε) (hE : ε ≤ E)
    (hN : 0 < N) (hsizes : ∀ t, 0 < sizes t)
    (hJB : ∀ b, |gaussianMass σ (shiftedChildEvent s b u)| ≤ B)
    (hcenter : (p : ℝ) / Real.sqrt ((p : ℝ) * N) ≤ ε) :
    Estimates N p sizes s σ u (finalConstant c B D E) ε := by
  have hk : 0 ≤ ratioConstant c B := by unfold ratioConstant; positivity
  have hE0 : 0 ≤ E := hε.trans hE
  have hKD : 0 ≤ ratioConstant c B * D := mul_nonneg hk hD
  have hcov : 0 ≤ (1 + 2 * (B / c) + ratioConstant c B * D * E) *
      (ratioConstant c B * D) := by positivity
  have hC0 : D ≤ finalConstant c B D E := by unfold finalConstant; nlinarith
  have hC1 : ratioConstant c B * D + 1 ≤ finalConstant c B D E := by
    unfold finalConstant; nlinarith
  have hC2 : (1 + 2 * (B / c) + ratioConstant c B * D * E) *
      (ratioConstant c B * D) ≤ finalConstant c B D E := by
    unfold finalConstant; nlinarith
  refine ⟨hH.mass_error.trans (mul_le_mul_of_nonneg_right hC0 hε), ?_, ?_, ?_, ?_⟩
  · intro b
    have hh := ratio_error hc hH.binomial_lower hH.gaussian_lower (hJB b)
      (hJ b).mass_error hH.mass_error
    change |binomialSplit N p sizes s b σ - _| ≤ _ at hh
    exact hh.trans (by
      change ratioConstant c B * (D * ε) ≤ _
      nlinarith [mul_le_mul_of_nonneg_right hC1 hε])
  · intro t
    have hh := recenter_estimate N p sizes s t (hsizes t) _ _
      (ratioConstant c B * D) ε (by simpa only [mul_assoc] using hH.mean hc hN t) hcenter
    exact hh.trans (mul_le_mul_of_nonneg_right hC1 hε)
  · intro b t
    have hh := recenter_estimate N p sizes s t (hsizes t) _ _
      (ratioConstant c B * D) ε (by simpa only [mul_assoc] using (hJ b).mean hc hN t) hcenter
    exact hh.trans (mul_le_mul_of_nonneg_right hC1 hε)
  · intro t t'
    exact (hH.covariance hc hB hD hE hN t t').trans
      (mul_le_mul_of_nonneg_right hC2 hε)

theorem finalConstant_pos (hc : 0 < c) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hE : 0 ≤ E) : 0 < finalConstant c B D E := by
  unfold finalConstant ratioConstant
  positivity

end MajorityDynamics.Idealized.RowLimits
