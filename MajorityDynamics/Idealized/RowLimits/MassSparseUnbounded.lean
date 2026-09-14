import MajorityDynamics.Idealized.RowLimits.RowsSparse
import MajorityDynamics.Idealized.RowLimits.ComparisonMoments
import MajorityDynamics.Analysis.GaussianRegularity.UniformThresholds

/-! Actual binomial event probabilities on the sparse range, with no bound
on the final decision shift. Parameter errors remain explicit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped BigOperators
namespace MajorityDynamics.Idealized.RowLimits
open Universal Binomial Binomial.Approximation Analysis
variable {n : ℕ}

theorem eventMatrix_rank (s : History (n + 1)) (b : Option Bool) :
    (eventMatrix s b).rank = eventRows n b := by
  cases b with
  | none => simpa [eventRows] using historyMatrix_rank s
  | some b => simpa [eventRows] using childMatrix_rank s b

theorem row_mass_sparse_unbounded (θ T R : ℝ)
    (hθ : 1 / 2 < θ) (hθ' : θ < 1) (hT : 1 < T) (hR : 0 ≤ R) :
    ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, 1 ≤ Real.log (N : ℝ) →
      ∀ p : Probability, SparseRange θ T N p →
      ∀ (s : History (n + 1)) (sizes : Local.Sizes n),
      (∀ t, (N : ℝ) * ν n t / 2 ≤ (Local.trials sizes s t : ℝ)) →
      (∀ t, (Local.trials sizes s t : ℝ) ≤ 2 * N * ν n t) →
      ∀ σ : Row (n + 1), (∀ t, |σ t| ≤ R) →
      ∀ (b : Option Bool) (u : ℝ),
      ‖(actualNormalizedParameters N p sizes s σ b).2 - (targetParameters σ b u).2‖ ≤ 1 →
      |binomialMass N p sizes s (eventSupport sizes s b) σ -
        gaussianMass σ (targetEvent s b u)| ≤
        C * Real.log N ^ (5 + Fintype.card (Fin (n + 1) → Bool)) / scale N p +
        K * (‖(actualNormalizedParameters N p sizes s σ b).1 - (targetParameters σ b u).1‖ +
          ‖(actualNormalizedParameters N p sizes s σ b).2 - (targetParameters σ b u).2‖) := by
  classical
  obtain ⟨vmin, hvmin, hvlo⟩ := finite_common_positive (fun t : History (n + 1) => ν n t)
    (ν_positive n)
  let vmax : ℝ := 1 + ∑ t : History (n + 1), 2 * ν n t
  have hvmax : 0 < vmax := by
    have hh : 0 ≤ ∑ t : History (n + 1), 2 * ν n t :=
      Finset.sum_nonneg (fun t _ => by have := ν_positive n t; positivity)
    dsimp [vmax]
    linarith
  have hvhi (t : History (n + 1)) : 2 * ν n t ≤ vmax := by
    have hh := Finset.single_le_sum (f := fun t : History (n + 1) => 2 * ν n t)
      (fun t _ => (mul_pos (by norm_num) (ν_positive n t)).le)
      (Finset.mem_univ t)
    dsimp [vmax]
    linarith
  have hsingle (j : History (n + 1) × Option Bool) :=
    GaussianRegularity.gaussian_mass_unbounded_threshold_parameters
      (eventMatrix j.1 j.2) (eventMatrix_rank j.1 j.2)
      (M := 2 * R) (by positivity) (half_pos hvmin) hvmax
  choose K hK hbound using hsingle
  let K₀ := ∑ j, K j
  have hK₀ : 0 ≤ K₀ := Finset.sum_nonneg (fun j _ => hK j)
  have hKK (j) : K j ≤ K₀ := Finset.single_le_sum (fun j _ => hK j) (Finset.mem_univ j)
  obtain ⟨C, hC, N₀, hN₀, hrow⟩ := row_normalized_comparison_sparse θ T R hθ hθ' hT hR
  refine ⟨C, K₀, hC, hK₀, N₀, hN₀, ?_⟩
  intro N hN hlog p hp s sizes hlo hhi σ hσ b u hu
  have hn : 0 < N := by omega
  have hparams := normalized_parameters_bounds N hn sizes s σ R hσ hlo hhi
  have hactualmean : ∀ i, |(actualNormalizedParameters N p sizes s σ b).1.1 i| ≤ 2 * R :=
    hparams.2
  have hactualvarlo : ∀ i, vmin / 2 ≤ (actualNormalizedParameters N p sizes s σ b).1.2 i := by
    intro i
    exact (div_le_div_of_nonneg_right (hvlo i) (by norm_num)).trans (hparams.1 i).1
  have hactualvarhi : ∀ i, (actualNormalizedParameters N p sizes s σ b).1.2 i ≤ vmax :=
    fun i => (hparams.1 i).2.trans (hvhi i)
  have htargetmean : ∀ i, |(targetParameters σ b u).1.1 i| ≤ 2 * R := by
    intro i
    have hh : |σ i| ≤ 2 * R := (hσ i).trans (by linarith)
    cases b <;> exact hh
  have htargetvarlo : ∀ i, vmin / 2 ≤ (targetParameters σ b u).1.2 i := by
    intro i
    have hh : vmin / 2 ≤ ν n i := by linarith [hvlo i]
    cases b <;> exact hh
  have htargetvarhi : ∀ i, (targetParameters σ b u).1.2 i ≤ vmax := by
    intro i
    have hh : ν n i ≤ vmax := by linarith [hvhi i, ν_positive n i]
    cases b <;> exact hh
  have hg := hbound (s, b) _ _ _ _ hactualmean hactualvarlo hactualvarhi
    htargetmean htargetvarlo htargetvarhi _ _ hu
  have hr := hrow N hN hlog p hp s sizes hlo hhi σ hσ b (.inl ())
  rw [actualGaussianMoment_eq_parameterMoment] at hr
  simp only [binomialNormalizedMoment_zero, parameterMoment] at hr
  rw [target_mass_eq]
  have hh := (abs_sub_le (binomialMass N p sizes s (eventSupport sizes s b) σ)
    (GaussianRegularity.mass (eventMatrix s b) (actualNormalizedParameters N p sizes s σ b))
    (GaussianRegularity.mass (eventMatrix s b) (targetParameters σ b u))).trans
      (add_le_add hr hg)
  exact hh.trans (add_le_add_right
    (mul_le_mul_of_nonneg_right (hKK (s, b)) (add_nonneg (norm_nonneg _) (norm_nonneg _))) _)

/-- Conditional child probabilities need a lower bound only on the history
event, not on both children. Consequently the final shift can be unbounded. -/
theorem row_split_sparse_unbounded (θ T R : ℝ)
    (hθ : 1 / 2 < θ) (hθ' : θ < 1) (hT : 1 < T) (hR : 0 ≤ R) :
    ∃ c C K : ℝ, 0 < c ∧ 0 < C ∧ 0 ≤ K ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, 1 ≤ Real.log (N : ℝ) →
      ∀ p : Probability, SparseRange θ T N p →
      ∀ (s : History (n + 1)) (sizes : Local.Sizes n),
      (∀ t, (N : ℝ) * ν n t / 2 ≤ (Local.trials sizes s t : ℝ)) →
      (∀ t, (Local.trials sizes s t : ℝ) ≤ 2 * N * ν n t) →
      ∀ σ : Row (n + 1), (∀ t, |σ t| ≤ R) →
      ∀ u E : ℝ, E ≤ 1 →
      (∀ b : Option Bool,
        ‖(actualNormalizedParameters N p sizes s σ b).1 - (targetParameters σ b u).1‖ +
          ‖(actualNormalizedParameters N p sizes s σ b).2 - (targetParameters σ b u).2‖ ≤ E) →
      let δ := C * Real.log N ^ (5 + Fintype.card (Fin (n + 1) → Bool)) / scale N p + K * E
      δ ≤ c / 2 →
      c / 2 ≤ binomialMass N p sizes s (Local.historySupport sizes s) σ ∧
      ∀ b : Bool, |binomialSplit N p sizes s b σ -
        gaussianMass σ (shiftedChildEvent s b u) / gaussianMass σ (historyEvent s)| ≤
        ratioConstant (c / 2) 1 * δ := by
  obtain ⟨c, hc, hgaussian⟩ := gaussian_probabilities_uniform_lower n (T := 0) hR le_rfl
  obtain ⟨C, K, hC, hK, N₀, hN₀, hmass⟩ := row_mass_sparse_unbounded θ T R hθ hθ' hT hR
  refine ⟨c, C, K, hc, hC, hK, N₀, hN₀, ?_⟩
  intro N hN hlog p hp s sizes hlo hhi σ hσ u E hE hparams
  dsimp only
  intro hsmall
  have hall (b : Option Bool) :
      |binomialMass N p sizes s (eventSupport sizes s b) σ - gaussianMass σ (targetEvent s b u)| ≤
        C * Real.log N ^ (5 + Fintype.card (Fin (n + 1) → Bool)) / scale N p + K * E := by
    have hthreshold : ‖(actualNormalizedParameters N p sizes s σ b).2 - (targetParameters σ b u).2‖ ≤ 1 :=
      (le_add_of_nonneg_left (norm_nonneg _)).trans ((hparams b).trans hE)
    exact (hmass N hN hlog p hp s sizes hlo hhi σ hσ b u hthreshold).trans
      (add_le_add_right (mul_le_mul_of_nonneg_left (hparams b) hK) _)
  have hg : c ≤ gaussianMass σ (historyEvent s) := (hgaussian s σ hσ).1
  have hactual := denominator_lower_bound hg (hall none) hsmall
  refine ⟨hactual, ?_⟩
  intro b
  exact ratio_error (half_pos hc) hactual (by linarith)
    (gaussianMass_le_one σ (shiftedChildEvent s b u)) (hall (some b)) (hall none)

end MajorityDynamics.Idealized.RowLimits
