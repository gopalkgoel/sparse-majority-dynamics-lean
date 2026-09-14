import MajorityDynamics.Idealized.CriticalDay.Solver
import MajorityDynamics.Idealized.CriticalDay.CenteredTarget
import MajorityDynamics.Idealized.CriticalDay.RowInputs

noncomputable section
open Filter Topology
namespace MajorityDynamics.Idealized.CriticalDay
open Universal LinearResponse PerturbedTilt
open Binomial.Approximation (Density)

/-- Closed nonlinear solving package, with no analytic premises beyond the
original faithful arrays. All E.3 estimates retain the actual decision shift. -/
theorem solved_rows (θ T δ : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hδ : 0 < δ) (n ell : ℕ)
    (hk : (n : ℝ) + 1 = 1 / (1 - θ)) :
    ∃ R C ρ : ℝ, 0 < R ∧ 0 < C ∧ 0 < ρ ∧ (∀ s t, |γ n s t| ≤ R) ∧ ∀ᶠ N : ℕ in atTop,
    ∀ p : Binomial.Probability, Density θ T N p →
    ∀ a : Process.Data, Process.Specification N p (responseHorizon θ) ell a →
    ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
    ∀ η : History (n + 1) → ℤ, ∀ e : History (n + 1) → History (n + 1) → ℤ,
    FaithfulNumericalData N (p : ℝ) T δ τ a n η e →
    ∃ σ : History (n + 1) → Row (n + 1),
      (∀ s t, |σ s t| ≤ R) ∧
      (∀ s t, |σ s t - γ n s t| ≤ C * (N : ℝ) ^ (-ρ)) ∧
      Local.Solves (naturalSizes η) (realEdges e) (fun s => RowLimits.rowTilt N p (σ s)) ∧
      ∀ s, RowLimits.Estimates N p (naturalSizes η) s (σ s)
        (RowLimits.shift N p (naturalSizes η)) C ((N : ℝ) ^ (-ρ)) := by
  have hT0 : 0 < T := by linarith
  obtain ⟨U, Cξ, hTU, hCξ, hinputs⟩ := faithful_row_inputs θ T δ hθlo hθhi hT hδ n ell hk
  obtain ⟨Kt, hKt, htarget⟩ := centered_target θ T δ hθlo hθhi hT hδ n ell hk
  obtain ⟨R, hR, hγR, r, hr, Cs, hCs, ell', N₀, hsolve⟩ := solve_of_row_inputs n (ell + 1)
    (by omega) θ U hθlo hθhi (hT.trans_le hTU)
  let ρ := targetRate θ δ / 2
  have hρ : 0 < ρ := half_pos ((targetRate_bounds (rate_pos hθlo hθhi) hδ).1)
  have hρt : ρ < targetRate θ δ := by dsimp [ρ] at hρ ⊢; linarith
  have hρδ : ρ < δ := hρt.trans (targetRate_bounds (rate_pos hθlo hθhi) hδ).2.2
  have hρκ : ρ < responseRate θ 0 := by
    have h := hρt.trans (targetRate_bounds (rate_pos hθlo hθhi) hδ).2.1
    unfold rate at h
    linarith [responseRate_pos hθlo hθhi (first_day_subcritical hθlo hθhi)]
  let C := max 1 Cs
  have hC : 0 < C := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨R, C, ρ, hR, hC, hρ, hγR, ?_⟩
  filter_upwards [hinputs, htarget, faithful_geometry θ T δ hθlo hθhi hT hδ n ell hk,
    eventually_basic θ T hθlo hθhi hT, eventually_ge_atTop N₀,
    eventually_small θ T hθlo hθhi hT 0 ell' (first_day_subcritical hθlo hθhi),
    eventually_poly_log_le (2 * Cs) (responseRate θ 0) ρ 0 (by positivity) hρκ,
    eventually_poly_log_le (2 * Cs * Cξ) δ ρ 0 (by positivity) hρδ,
    eventually_poly_log_le Kt (targetRate θ δ) ρ 0 hKt.le hρt,
    eventually_rpow_neg_le ρ (r / 2) hρ (half_pos hr)]
    with N hinput htar hgeo hbasic hN hsmall he1 he2 het heSmall
  simp only [pow_zero, mul_one] at he1 he2 het
  intro p hp a ha τ hτ hτT η e hf
  obtain ⟨hξ, hin⟩ := hinput p hp a ha τ hτ hτT η e hf
  obtain ⟨_, hcast, hsizes, _⟩ := hgeo p hp a ha τ hτ hτT η e hf
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hbasic.1
  have hE : 0 < (N : ℝ) ^ (-ρ) := Real.rpow_pos_of_pos hNpos _
  have herror : Cs * RowLimits.error ell' N p (Cξ * (N : ℝ) ^ (-δ)) ≤ (N : ℝ) ^ (-ρ) := by
    have hh := mul_le_mul_of_nonneg_left ((hsmall p hp).2.2.1) hCs.le
    unfold RowLimits.error
    nlinarith
  have ht : ∀ s t,
      |((realEdges e) s t / (naturalSizes η s : ℝ) - (p : ℝ) * (naturalSizes η t : ℝ)) /
        Real.sqrt ((p : ℝ) * N) - ν n t * μ n s t| ≤ (N : ℝ) ^ (-ρ) := by
    intro s t
    rw [hcast s, hcast t]
    exact (htar p hp a ha τ hτ hτT η e hf s t).trans het
  obtain ⟨σ, hσR, hσγ, hq, hest⟩ := hsolve N hN p (density_mono hT0 hTU hp)
    (Cξ * (N : ℝ) ^ (-δ)) ((N : ℝ) ^ (-ρ)) hξ.1 hξ.2 hE
    (heSmall.trans_lt (half_lt_self hr)) herror (naturalSizes η)
    (fun s => Nat.lt_of_lt_of_le (by omega) (hsizes s)) hin (realEdges e) ht
  refine ⟨σ, hσR, ?_, hq, ?_⟩
  · intro s t
    exact (hσγ s t).trans (mul_le_mul_of_nonneg_right (le_max_right 1 Cs) hE.le)
  · intro s
    apply Process.enlarge_estimates (hest s)
    exact herror.trans (le_mul_of_one_le_left hE.le (le_max_left _ _))

end MajorityDynamics.Idealized.CriticalDay
