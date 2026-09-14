import MajorityDynamics.Idealized.RowLimits.ParameterBudget

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped BigOperators
namespace MajorityDynamics.Idealized.RowLimits
open Universal Binomial Binomial.Approximation Analysis
variable {n : ℕ}

/-- Coordinate control gives the history compactness needed by the actual
nonlinear solver. No condition is imposed on the final decision imbalance. -/
theorem history_parameters_mem_of_budget {N : ℕ} (hN : 0 < N) (p : Probability)
    (sizes : Local.Sizes n) (s : History (n+1)) (σ : Row (n+1))
    {R d : ℝ} (hσ : ∀ t, |σ t| ≤ R)
    (hlo : ∀ t, (N:ℝ)*ν n t/2 ≤ (Local.trials sizes s t:ℝ))
    (hhi : ∀ t, (Local.trials sizes s t:ℝ) ≤ 2*N*ν n t)
    (hh : ∀ j, |normalizedThreshold N p sizes s (historyMatrix s) j| ≤ d)
    (hd : d ≤ 1) :
    actualNormalizedParameters N p sizes s σ none ∈ gaussianBox n n R 0 := by
  rw [actualNormalizedParameters_none, ← rowParameterBox_eq_gaussianBox]
  exact normalized_parameters_mem hN p sizes s σ (historyMatrix s) 0 R hσ hlo hhi
    (fun j => by simpa using (hh j).trans hd)

/-- Common coordinate errors control every event parameter, preserving the
actual (possibly unbounded) child shift. -/
theorem event_parameters_dist_of_budget {N : ℕ} (p : Probability)
    (sizes : Local.Sizes n) (s : History (n+1)) (σ : Row (n+1))
    {d : ℝ} (hd : 0 ≤ d)
    (hm : ∀ t, |normalizedMean N sizes s σ t-σ t| ≤ d)
    (hv : ∀ t, |normalizedVariance N sizes s t-ν n t| ≤ d)
    (hh : ∀ j, |normalizedThreshold N p sizes s (historyMatrix s) j| ≤ d)
    (hc : ∀ b j, |normalizedThreshold N p sizes s (childMatrix s b) j-
      childThreshold b (shift N p sizes) j| ≤ d) :
    ∀ b : Option Bool,
      dist (actualNormalizedParameters N p sizes s σ b)
        (targetParameters σ b (shift N p sizes)) ≤
        (Fintype.card (Fin (n+1) → Bool)+n+2:ℝ)*d := by
  intro b
  have hdim : (Fintype.card (Fin (n+1) → Bool)+n+1:ℝ)*d ≤
      (Fintype.card (Fin (n+1) → Bool)+n+2:ℝ)*d := by nlinarith
  cases b with
  | none =>
    apply le_trans (parameters_dist_le_of_coordinates hd hm hv
      (fun j => by simpa [actualNormalizedParameters, normalizedParameters,
        targetParameters, historyParameters, eventMatrix_none] using hh j)) hdim
  | some b =>
    have h := parameters_dist_le_of_coordinates (x :=
      actualNormalizedParameters N p sizes s σ (some b))
      (y := targetParameters σ (some b) (shift N p sizes)) hd hm hv (hc b)
    simpa only [eventRows, Nat.cast_add, Nat.cast_one, add_assoc,
      show (1:ℝ)+1=2 from by norm_num] using h

/-- The split comparison uses a sum of two block norms rather than the
product metric; twice the preceding distance bound suffices. -/
theorem event_parameters_norm_of_budget {N : ℕ} (p : Probability)
    (sizes : Local.Sizes n) (s : History (n+1)) (σ : Row (n+1))
    {d : ℝ} (hd : 0 ≤ d)
    (hm : ∀ t, |normalizedMean N sizes s σ t-σ t| ≤ d)
    (hv : ∀ t, |normalizedVariance N sizes s t-ν n t| ≤ d)
    (hh : ∀ j, |normalizedThreshold N p sizes s (historyMatrix s) j| ≤ d)
    (hc : ∀ b j, |normalizedThreshold N p sizes s (childMatrix s b) j-
      childThreshold b (shift N p sizes) j| ≤ d) :
    ∀ b : Option Bool,
      ‖(actualNormalizedParameters N p sizes s σ b).1-
        (targetParameters σ b (shift N p sizes)).1‖+
      ‖(actualNormalizedParameters N p sizes s σ b).2-
        (targetParameters σ b (shift N p sizes)).2‖ ≤
        2*(Fintype.card (Fin (n+1) → Bool)+n+2:ℝ)*d := by
  intro b
  have h := event_parameters_dist_of_budget p sizes s σ hd hm hv hh hc b
  rw [Prod.dist_eq, max_le_iff, dist_eq_norm, dist_eq_norm] at h
  linarith [h.1,h.2]

end MajorityDynamics.Idealized.RowLimits
