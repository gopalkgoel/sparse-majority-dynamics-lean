import MajorityDynamics.Idealized.CriticalDay.SolvedRows
import MajorityDynamics.Idealized.Process.TiltEstimates

noncomputable section
open Filter Topology
open scoped BigOperators
namespace MajorityDynamics.Idealized.CriticalDay
open Universal LinearResponse
open Binomial.Approximation (Density)

/-- Polynomial closeness of the solved mean parameters implies the exact
coefficient-one tilt approximation, after halving the exponent. -/
theorem tilt_approximation (θ T R C ρ : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hR : 0 ≤ R) (hC : 0 < C) (hρ : 0 < ρ) (n : ℕ)
    (hγ : ∀ s t, |γ n s t| ≤ R) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Binomial.Probability, Density θ T N p →
    ∀ σ : History (n + 1) → Row (n + 1),
      (∀ s t, |σ s t| ≤ R) →
      (∀ s t, |σ s t - γ n s t| ≤ C * (N : ℝ) ^ (-ρ)) →
    ∀ s t, |(RowLimits.rowTilt N p (σ s) t : ℝ) - logitTilt N p (γ n s t) (ν n t)| ≤
      (p : ℝ) / Real.sqrt ((p : ℝ) * N) * (N : ℝ) ^ (-(ρ / 2)) := by
  let L : ℝ := 1 + ∑ t : History (n + 1), 2 * Real.exp (R / ν n t) / ν n t
  have hcoef : ∀ t, 0 ≤ 2 * Real.exp (R / ν n t) / ν n t := by
    intro t
    exact div_nonneg (by positivity) (ν_positive n t).le
  have hL : 0 < L := by
    have : 0 ≤ ∑ t : History (n + 1), 2 * Real.exp (R / ν n t) / ν n t :=
      Finset.sum_nonneg (fun t _ => hcoef t)
    dsimp [L]
    linarith
  have hLt : ∀ t, 2 * Real.exp (R / ν n t) / ν n t ≤ L := by
    intro t
    have := Finset.single_le_sum (fun t _ => hcoef t) (Finset.mem_univ t)
    dsimp [L]
    linarith
  filter_upwards [eventually_basic θ T hθlo hθhi hT,
    eventually_poly_log_le (L * C) ρ (ρ / 2) 0 (mul_pos hL hC).le (by linarith)]
    with N hbasic hsmall
  simp only [pow_zero, mul_one] at hsmall
  intro p hp σ hσ hclose s t
  have hs := hbasic.2.2 p hp
  have h := Process.logitTilt_lipschitz N p (ν n t) R (σ s t) (γ n s t)
    (ν_positive n t) hR (by linarith [hs.2.2]) hs.1 (hσ s t) (hγ s t)
  have hp0 := p.property.1
  have hpS : 0 ≤ (p : ℝ) / Real.sqrt ((p : ℝ) * N) := by positivity
  have h1 := mul_le_mul_of_nonneg_left (hclose s t)
    (mul_nonneg (hcoef t) hpS)
  have h2 := mul_le_mul_of_nonneg_right (hLt t)
    (show 0 ≤ C * (N : ℝ) ^ (-ρ) by positivity)
  have h3 := mul_le_mul_of_nonneg_left hsmall hpS
  have h2' := mul_le_mul_of_nonneg_left h2 hpS
  change |(logitTilt N p (σ s t) (ν n t) : ℝ) - logitTilt N p (γ n s t) (ν n t)| ≤ _
  nlinarith

end MajorityDynamics.Idealized.CriticalDay
