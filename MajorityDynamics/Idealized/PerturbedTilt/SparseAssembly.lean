import MajorityDynamics.Idealized.PerturbedTilt.Assembly
import MajorityDynamics.Idealized.PerturbedTilt.SparseTarget

noncomputable section
open Filter Topology
open scoped BigOperators
namespace MajorityDynamics.Idealized.PerturbedTilt
open Universal LinearResponse
open Binomial.Approximation (SparseRange)
set_option maxHeartbeats 3000000

theorem perturbed_tilt_response_spec_sparse (θ T δ : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hδ : 0 < δ) (n ell : ℕ) (hell : 1 ≤ ell)
    (D : ℕ) (hDlt : n + 1 < D) :
    ∃ T₁ : ℝ, T ≤ T₁ ∧ ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ, 0 < C ∧
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ p : Binomial.Probability, SparseRange θ T N p → ResponseSmall θ N p n →
      ∀ a : Process.Data, Process.Specification N p D ell a →
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ η : History (n + 1) → ℤ, ∀ e : History (n + 1) → History (n + 1) → ℤ,
      FaithfulNumericalData N (p : ℝ) T δ τ a n η e →
      TiltConclusion N p a n η e τ T₁ (sparseTiltRate θ δ) ∧
        (∀ s, ResponseConclusion N p a n (naturalSizes η) s τ R C (sparseResponseRate θ)) ∧
        ∀ q : Local.Tilt n, Local.Solves (naturalSizes η) (realEdges e) q →
          ∃ σ : History (n + 1) → Row (n + 1),
            (∀ s, q s = processEffectiveTilt N p a n (naturalSizes η) s τ (σ s)) ∧
            (∀ s t, |σ s t| ≤ R) ∧
            ∀ s t, |σ s t - β n s t| ≤ B * (N : ℝ) ^ (-sparseTiltRate θ δ) := by
  have hT0 : 0 < T := by linarith
  have hTU := comparisonConstant_ge n hT0.le
  have hU : 1 < comparisonConstant n T := hT.trans_le hTU
  obtain ⟨hρ, hρκ, _⟩ := sparseTiltRate_bounds (sparseResponseRate_pos hθhi) hδ
  obtain ⟨R, hR, r, hr, Ci, hCi, hinverse⟩ := stable_covariance_inverse n
  obtain ⟨Cl, hCl, Nl, hNl, hlinear⟩ := linear_response_spec_sparse θ hθlo hθhi n D hDlt
    (comparisonConstant n T) R hU hR ell hell
  obtain ⟨Kt, hKt, htarget⟩ := faithful_target_sparse θ T δ hθlo hθhi hT hδ n ell D hDlt
  let T₁ := max T (T * Ci * (Kt + 1))
  have hCut : ∀ᶠ N : ℕ in atTop,
      (0 < N) ∧ Nl ≤ N ∧
      (Cl * (N : ℝ) ^ (-sparseResponseRate θ) ≤ (N : ℝ) ^ (-sparseTiltRate θ δ)) ∧
      ((Kt + 1) * (N : ℝ) ^ (-sparseTiltRate θ δ) < r) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), eventually_ge_atTop Nl,
      eventually_poly_log_le Cl (sparseResponseRate θ) (sparseTiltRate θ δ) 0 hCl.le hρκ,
      eventually_rpow_neg_le (sparseTiltRate θ δ) (r / (2 * (Kt + 1))) hρ (by positivity)]
      with N hN hNl h1 h2
    refine ⟨hN, hNl, by simpa using h1, ?_⟩
    have h := mul_le_mul_of_nonneg_left h2 (show 0 ≤ Kt + 1 by linarith)
    have heq : (Kt + 1) * (r / (2 * (Kt + 1))) = r / 2 := by field_simp
    rw [heq] at h
    linarith
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (hCut.and (htarget.and
    (faithful_geometry_sparse θ T δ hθlo hθhi hT hδ n ell D hDlt)))
  refine ⟨T₁, le_max_left _ _, R, hR, Cl, hCl, Ci * (Kt + 1),
    mul_pos hCi (by linarith), max 1 N₀, le_max_left _ _, ?_⟩
  intro N hN p hp hsub a ha τ hτ hτT η e hf
  obtain ⟨⟨hNpos, hNNl, hlinerr, hEsmall⟩, htar, hgeo⟩ := hN₀ N ((le_max_right _ _).trans hN)
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hp0 := p.property.1
  have hτ0 : 0 < τ := (inv_pos.mpr hT0).trans_le hτ
  have hβ : 0 < betaScale N (p : ℝ) n := by unfold betaScale; positivity
  obtain ⟨hηpos, hcast, hclose, hgf⟩ := hgeo p hp hsub a ha τ hτ hτT η e hf
  have hpU := RowLimits.sparseRange_enlarge hT0 hTU hp
  have hτU : (comparisonConstant n T)⁻¹ ≤ τ := by
    have hh : (comparisonConstant n T)⁻¹ ≤ T⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hT0 hTU
    exact hh.trans hτ
  have hresp : ∀ s, ResponseConclusion N p a n (naturalSizes η) s τ R Cl (sparseResponseRate θ) := by
    intro s
    apply hlinear N hNNl p hpU hsub a ha τ hτU (hτT.trans hTU) (naturalSizes η) _ s
    intro t
    rw [hcast t]
    exact hclose t
  let E := (Kt + 1) * (N : ℝ) ^ (-sparseTiltRate θ δ)
  have hE : 0 < E := by dsimp [E]; positivity
  have hE1 : (N : ℝ) ^ (-sparseTiltRate θ δ) ≤ E := by
    dsimp [E]
    nlinarith [Real.rpow_nonneg (Nat.cast_nonneg N) (-sparseTiltRate θ δ)]
  have hEK : Kt * (N : ℝ) ^ (-sparseTiltRate θ δ) ≤ E := by
    dsimp [E]
    nlinarith [Real.rpow_nonneg (Nat.cast_nonneg N) (-sparseTiltRate θ δ)]
  have hsolve : ∀ s : History (n + 1), ∃ σ : Row (n + 1),
      perturbedMeanMap N p a (naturalSizes η) s τ σ = edgeTarget N (p : ℝ) a τ η e s ∧
      (∀ t, |σ t| ≤ R) ∧ ∀ t, |σ t - β n s t| ≤ Ci * E := by
    intro s
    apply hinverse E hE hEsmall s _ (perturbedMeanMap_continuous (hresp s))
      (fun σ hσ t => ((hresp s).mean_response σ hσ t).trans (hlinerr.trans hE1))
      _ (fun t => (htar p hp hsub a ha τ hτ hτT η e hf s t).trans hEK)
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
        (show 0 ≤ betaScale N (p : ℝ) n * (N : ℝ) ^ (-sparseTiltRate θ δ) by positivity)
      dsimp [E, T₁] at *
      nlinarith

theorem perturbed_tilt_spec_sparse (θ T δ : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hδ : 0 < δ) (n ell : ℕ) (hell : 1 ≤ ell)
    (D : ℕ) (hDlt : n + 1 < D) :
    ∃ T₁ : ℝ, T ≤ T₁ ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ p : Binomial.Probability, SparseRange θ T N p → ResponseSmall θ N p n →
      ∀ a : Process.Data, Process.Specification N p D ell a →
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ η : History (n + 1) → ℤ, ∀ e : History (n + 1) → History (n + 1) → ℤ,
      FaithfulNumericalData N (p : ℝ) T δ τ a n η e →
      TiltConclusion N p a n η e τ T₁ (sparseTiltRate θ δ) := by
  obtain ⟨T₁, hT₁, R, hR, C, hC, B, hB, N₀, hN₀, h⟩ :=
    perturbed_tilt_response_spec_sparse θ T δ hθlo hθhi hT hδ n ell hell D hDlt
  refine ⟨T₁, hT₁, N₀, hN₀, ?_⟩
  intro N hN p hp hsub a ha τ hτ hτT η e hf
  exact (h N hN p hp hsub a ha τ hτ hτT η e hf).1

end MajorityDynamics.Idealized.PerturbedTilt

