import MajorityDynamics.Idealized.PerturbedTilt.Inverse
import MajorityDynamics.Idealized.PerturbedTilt.Target

/-! Solve the actual row equations and identify the literal logarithm. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace MajorityDynamics.Idealized.PerturbedTilt
open Universal LinearResponse
open Binomial.Approximation (Density)

theorem effectiveParameter_eq {n : ℕ} {p : ℝ} {ref sizes : Local.Sizes n}
    (hp : 0 < p) (hr : ∀ t, 0 < ref t) (q : Local.Tilt n) (s t : History (n + 1))
    (hres : 0 < residual p ref sizes s t) :
    effectiveParameter p ref sizes q s t = Binomial.logOdds (q s t) +
      Real.log (residual p ref sizes s t / (p * (ref t : ℝ))) := by
  have hq := (q s t).property.1
  have hq1 : 0 < 1 - (q s t : ℝ) := sub_pos.mpr (q s t).property.2
  have hr0 : (0 : ℝ) < ref t := Nat.cast_pos.mpr (hr t)
  unfold effectiveParameter Binomial.logOdds
  rw [Real.log_div (mul_pos hq hres).ne' (mul_pos (mul_pos hq1 hp) hr0).ne',
    Real.log_mul hq.ne' hres.ne',
    Real.log_mul (mul_pos hq1 hp).ne' hr0.ne', Real.log_mul hq1.ne' hp.ne',
    Real.log_div hres.ne' (mul_pos hp hr0).ne', Real.log_mul hp.ne' hr0.ne']
  ring

def perturbedMeanMap {n : ℕ} (N : ℕ) (p : Binomial.Probability) (a : Process.Data)
    (sizes : Local.Sizes n) (s : History (n + 1)) (τ : ℝ) (σ : Row (n + 1)) : Row (n + 1) :=
  WithLp.toLp 2 (fun t =>
    (historyMean sizes s (processEffectiveTilt N p a n sizes s τ σ) t -
      (a.state n).edges s t / ((a.state n).sizes s : ℝ)) /
        (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)))

theorem perturbedMeanMap_continuous {n N : ℕ} {p : Binomial.Probability} {a : Process.Data}
    {sizes : Local.Sizes n} {s : History (n + 1)} {τ R C κ : ℝ}
    (h : ResponseConclusion N p a n sizes s τ R C κ) :
    Continuous (perturbedMeanMap N p a sizes s τ) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro t
  exact ((h.smooth.history_mean t).continuous.sub continuous_const).div_const _

/-- The solving construction retains its effective-tilt coordinates and all
linear-response estimates. Every solving tilt uses these same coordinates by
uniqueness. All bounds are selected before the numerical input arrays. -/
theorem perturbed_tilt_response_spec (θ T δ : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hδ : 0 < δ) (n ell : ℕ) (hell : 1 ≤ ell)
    (hk : (n : ℝ) + 1 < 1 / (1 - θ)) :
    ∃ T₁ : ℝ, T ≤ T₁ ∧ ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ, 0 < C ∧
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ p : Binomial.Probability, Density θ T N p →
      ∀ a : Process.Data, Process.Specification N p (responseHorizon θ) ell a →
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ η : History (n + 1) → ℤ, ∀ e : History (n + 1) → History (n + 1) → ℤ,
      FaithfulNumericalData N (p : ℝ) T δ τ a n η e →
      TiltConclusion N p a n η e τ T₁ (tiltRate θ δ n) ∧
        (∀ s, ResponseConclusion N p a n (naturalSizes η) s τ R C (responseRate θ n)) ∧
        ∀ q : Local.Tilt n, Local.Solves (naturalSizes η) (realEdges e) q →
          ∃ σ : History (n + 1) → Row (n + 1),
            (∀ s, q s = processEffectiveTilt N p a n (naturalSizes η) s τ (σ s)) ∧
            (∀ s t, |σ s t| ≤ R) ∧
            ∀ s t, |σ s t - β n s t| ≤ B * (N : ℝ) ^ (-tiltRate θ δ n) := by
  have hT0 : 0 < T := by linarith
  have hTU := comparisonConstant_ge n hT0.le
  have hU : 1 < comparisonConstant n T := hT.trans_le hTU
  obtain ⟨hρ, hρκ, _⟩ := tiltRate_bounds (responseRate_pos hθlo hθhi hk) hδ
  obtain ⟨R, hR, r, hr, Ci, hCi, hinverse⟩ := stable_covariance_inverse n
  obtain ⟨Cl, hCl, Nl, hNl, hlinear⟩ := linear_response_spec θ hθlo hθhi n hk
    (comparisonConstant n T) R hU hR ell hell
  obtain ⟨Kt, hKt, htarget⟩ := faithful_target θ T δ hθlo hθhi hT hδ n ell hk
  let T₁ := max T (T * Ci * (Kt + 1))
  have hCut : ∀ᶠ N : ℕ in atTop,
      (0 < N) ∧ Nl ≤ N ∧
      (Cl * (N : ℝ) ^ (-responseRate θ n) ≤ (N : ℝ) ^ (-tiltRate θ δ n)) ∧
      ((Kt + 1) * (N : ℝ) ^ (-tiltRate θ δ n) < r) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), eventually_ge_atTop Nl,
      eventually_poly_log_le Cl (responseRate θ n) (tiltRate θ δ n) 0 hCl.le hρκ,
      eventually_rpow_neg_le (tiltRate θ δ n) (r / (2 * (Kt + 1))) hρ (by positivity)]
      with N hN hNl h1 h2
    refine ⟨hN, hNl, by simpa using h1, ?_⟩
    have h := mul_le_mul_of_nonneg_left h2 (show 0 ≤ Kt + 1 by linarith)
    have heq : (Kt + 1) * (r / (2 * (Kt + 1))) = r / 2 := by field_simp
    rw [heq] at h
    linarith
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (hCut.and (htarget.and
    (faithful_geometry θ T δ hθlo hθhi hT hδ n ell hk)))
  refine ⟨T₁, le_max_left _ _, R, hR, Cl, hCl, Ci * (Kt + 1),
    mul_pos hCi (by linarith), max 1 N₀, le_max_left _ _, ?_⟩
  intro N hN p hp a ha τ hτ hτT η e hf
  obtain ⟨⟨hNpos, hNNl, hlinerr, hEsmall⟩, htar, hgeo⟩ := hN₀ N ((le_max_right _ _).trans hN)
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hp0 := p.property.1
  have hτ0 : 0 < τ := (inv_pos.mpr hT0).trans_le hτ
  have hβ : 0 < betaScale N (p : ℝ) n := by unfold betaScale; positivity
  obtain ⟨hηpos, hcast, hclose, hgf⟩ := hgeo p hp a ha τ hτ hτT η e hf
  have hpU := density_mono hT0 hTU hp
  have hτU : (comparisonConstant n T)⁻¹ ≤ τ := by
    have hh : (comparisonConstant n T)⁻¹ ≤ T⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hT0 hTU
    exact hh.trans hτ
  have hresp : ∀ s, ResponseConclusion N p a n (naturalSizes η) s τ R Cl (responseRate θ n) := by
    intro s
    apply hlinear N hNNl p hpU a ha τ hτU (hτT.trans hTU) (naturalSizes η) _ s
    intro t
    rw [hcast t]
    exact hclose t
  let E := (Kt + 1) * (N : ℝ) ^ (-tiltRate θ δ n)
  have hE : 0 < E := by dsimp [E]; positivity
  have hE1 : (N : ℝ) ^ (-tiltRate θ δ n) ≤ E := by
    dsimp [E]
    nlinarith [Real.rpow_nonneg (Nat.cast_nonneg N) (-tiltRate θ δ n)]
  have hEK : Kt * (N : ℝ) ^ (-tiltRate θ δ n) ≤ E := by
    dsimp [E]
    nlinarith [Real.rpow_nonneg (Nat.cast_nonneg N) (-tiltRate θ δ n)]
  have hsolve : ∀ s : History (n + 1), ∃ σ : Row (n + 1),
      perturbedMeanMap N p a (naturalSizes η) s τ σ = edgeTarget N (p : ℝ) a τ η e s ∧
      (∀ t, |σ t| ≤ R) ∧ ∀ t, |σ t - β n s t| ≤ Ci * E := by
    intro s
    apply hinverse E hE hEsmall s _ (perturbedMeanMap_continuous (hresp s))
      (fun σ hσ t => ((hresp s).mean_response σ hσ t).trans (hlinerr.trans hE1))
      _ (fun t => (htar p hp a ha τ hτ hτT η e hf s t).trans hEK)
  choose σ hσsolve hσR hσβ using hsolve
  let q : Local.Tilt n := fun s => processEffectiveTilt N p a n (naturalSizes η) s τ (σ s)
  have hq : Local.Solves (naturalSizes η) (realEdges e) q := by
    intro s t
    have heq := congrArg (fun x : Row (n + 1) => x t) (hσsolve s)
    change (_ - _) / (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)) =
      ((e s t : ℝ) / (η s : ℝ) - _) / (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)) at heq
    have hden : τ * betaScale N (p : ℝ) n * ((p : ℝ) * N) ≠ 0 := by positivity
    have hmean := sub_left_inj.mp ((div_left_inj' hden).mp heq)
    change (naturalSizes η s : ℝ) * historyMean (naturalSizes η) s (q s) t = (e s t : ℝ)
    rw [hcast s, hmean]
    have hη : (η s : ℝ) ≠ 0 := (show (0 : ℝ) < η s by exact_mod_cast hηpos s).ne'
    field_simp
  have hunique : ∀ q' : Local.Tilt n, Local.Solves (naturalSizes η) (realEdges e) q' → q' = q :=
    fun q' hq' => all_solving_tilts_unique _ hgf.sizes_support _ hq' hq
  refine ⟨?_, hresp, ?_⟩
  swap
  · intro q' hq'
    rw [hunique q' hq']
    refine ⟨σ, fun _ => rfl, hσR, ?_⟩
    intro s t
    simpa only [E, mul_assoc] using hσβ s t
  refine ⟨hηpos, hcast, ?_, (fun s => (hresp s).reference_residual_pos),
    (fun s => (hresp s).residual_pos), ⟨q, hq, hunique⟩, ?_⟩
  · intro s t
    rw [RowLimits.trials_cast _ s t (hgf.sizes_pos t), hcast t]
    rfl
  · intro q' hq'
    rw [hunique q' hq']
    refine ⟨fun s => Process.history_eventMass_pos _ hgf.sizes_support s (q s), ?_, ?_, ?_⟩
    · intro s t
      exact mul_pos (mul_pos (sub_pos.mpr (q s t).property.2) hp0)
        (Nat.cast_pos.mpr (hgf.ref_pos t))
    · intro s t
      exact mul_pos (mul_pos (sub_pos.mpr (a.tilt n s t).property.2) hp0)
        (Nat.cast_pos.mpr (hgf.ref_pos t))
    · intro s t
      rw [effectiveParameter_eq hp0 hgf.ref_pos q s t ((hresp s).residual_pos t),
        effectiveParameter_eq hp0 hgf.ref_pos (a.tilt n) s t ((hresp s).reference_residual_pos t)]
      have heq := (hresp s).tilt_equation (σ s) t
      change Binomial.logOdds (q s t) + _ = _ at heq
      rw [heq]
      have hid : Binomial.logOdds (a.tilt n s t) +
          Real.log (residual (p : ℝ) (a.state n).sizes (a.state n).sizes s t /
            ((p : ℝ) * ((a.state n).sizes t : ℝ))) + τ * betaScale N (p : ℝ) n * σ s t -
          (Binomial.logOdds (a.tilt n s t) + Real.log
            (residual (p : ℝ) (a.state n).sizes (a.state n).sizes s t /
              ((p : ℝ) * ((a.state n).sizes t : ℝ)))) - τ * betaScale N (p : ℝ) n * β n s t =
          τ * betaScale N (p : ℝ) n * (σ s t - β n s t) := by ring
      rw [hid, abs_mul, abs_of_pos (mul_pos hτ0 hβ)]
      have hbnd := mul_le_mul_of_nonneg_left (hσβ s t) (mul_pos hτ0 hβ).le
      have hτbnd := mul_le_mul_of_nonneg_right hτT
        (show 0 ≤ betaScale N (p : ℝ) n * Ci * E by positivity)
      have hmax := mul_le_mul_of_nonneg_right (le_max_right T (T * Ci * (Kt + 1)))
        (show 0 ≤ betaScale N (p : ℝ) n * (N : ℝ) ^ (-tiltRate θ δ n) by positivity)
      dsimp [E, T₁] at *
      nlinarith

/-- LA6, LA7 and LA9 at the very same effective tilt used by the solver. -/
theorem response_local_bounds {n N : ℕ} {p : Binomial.Probability} {a : Process.Data}
    {sizes : Local.Sizes n} {τ R C κ : ℝ} {q : Local.Tilt n}
    (hresp : ∀ s, ResponseConclusion N p a n sizes s τ R C κ)
    (σ : History (n + 1) → Row (n + 1))
    (hq : ∀ s, q s = processEffectiveTilt N p a n sizes s τ (σ s))
    (hσ : ∀ s t, |σ s t| ≤ R) :
    (∀ s t, |(q s t : ℝ) - p| ≤ C * (p : ℝ) / Real.sqrt ((p : ℝ) * N)) ∧
    (∀ s, φStar n / 4 ≤ Binomial.eventMass (Local.trials sizes s) (q s)
      (Local.historySupport sizes s)) ∧
    (∀ s b, φStar n / 4 ≤ Local.splitProbability sizes q s b ∧
      Local.splitProbability sizes q s b ≤ 1 - φStar n / 4) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s t
    rw [hq s]
    exact (hresp s).tilt_bound (σ s) (hσ s) t
  · intro s
    rw [hq s]
    exact (hresp s).history_nondegenerate (σ s) (hσ s)
  · intro s b
    have h := (hresp s).split_nondegenerate (σ s) (hσ s) b
    have heq : Local.splitProbability sizes q s b =
        LinearResponse.splitProbability sizes s b
          (processEffectiveTilt N p a n sizes s τ (σ s)) := by
      unfold Local.splitProbability LinearResponse.splitProbability childMass historyMass
      rw [hq s]
    rw [heq]
    have hφ := (universal_nondegeneracy n).probability_pos
    constructor <;> linarith [h.1, h.2]

/-- Preserve the original solving-tilt contract as a projection. -/
theorem perturbed_tilt_spec (θ T δ : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hδ : 0 < δ) (n ell : ℕ) (hell : 1 ≤ ell)
    (hk : (n : ℝ) + 1 < 1 / (1 - θ)) :
    ∃ T₁ : ℝ, T ≤ T₁ ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ p : Binomial.Probability, Density θ T N p →
      ∀ a : Process.Data, Process.Specification N p (responseHorizon θ) ell a →
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ η : History (n + 1) → ℤ, ∀ e : History (n + 1) → History (n + 1) → ℤ,
      FaithfulNumericalData N (p : ℝ) T δ τ a n η e →
      TiltConclusion N p a n η e τ T₁ (tiltRate θ δ n) := by
  obtain ⟨T₁, hT₁, R, hR, C, hC, B, hB, N₀, hN₀, h⟩ :=
    perturbed_tilt_response_spec θ T δ hθlo hθhi hT hδ n ell hell hk
  refine ⟨T₁, hT₁, N₀, hN₀, ?_⟩
  intro N hN p hp a ha τ hτ hτT η e hf
  exact (h N hN p hp a ha τ hτ hτT η e hf).1

end MajorityDynamics.Idealized.PerturbedTilt

