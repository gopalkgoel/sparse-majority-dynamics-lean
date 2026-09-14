import MajorityDynamics.Idealized.CriticalDay.DecisionCompression
import MajorityDynamics.Idealized.CriticalDay.GaussianGainUnbounded
import MajorityDynamics.Analysis.ConditionalGaussian.SmallSetLower

/-! Quantitative linear small-shift gain, proved by rank-one slab compression.
The mean perturbation costs K e, uniformly for unbounded actual shifts. -/
noncomputable section
open Set MeasureTheory
open MajorityDynamics.Universal MajorityDynamics.Analysis
namespace MajorityDynamics.Idealized.CriticalDay
open RowLimits
variable {n : ℕ}

theorem gainSlab_mass_linear_lower (s : History (n + 1)) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : ℝ, 0 < u → u ≤ 1 →
      c * u ≤ (rowLaw (ν n) (γ n s)).real (gainSlab s u) := by
  obtain ⟨x, hx⟩ := gainSlab_nonempty s (by norm_num : (0 : ℝ) < 1)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (gainSlab_open s 1) x hx
  obtain ⟨c, hc, hbound⟩ := ConditionalGaussian.gaussianLaw_compressed_ball_lower
    (covariance (ν n)) (covariance_posDef _ (ν_positive n)) (γ n s) x hr
    (decisionProjection n)
  refine ⟨c, hc, ?_⟩
  intro u hu hu1
  have h := hbound u hu hu1
  change c * |LinearMap.det (decisionCompression n u).toLinearMap| ≤ _ at h
  rw [decisionCompression_det, abs_of_pos hu] at h
  apply h.trans
  exact measureReal_mono (μ := rowLaw (ν n) (γ n s))
    ((Set.image_mono hball).trans (decisionCompression_slab s hu))

theorem gaussian_gain_linear (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (s : History (n + 1)) (u : ℝ),
      0 < u → u ≤ 1 → ∀ (v : ℝ), u ≤ v → ∀ b : Bool,
      c * u ≤ sign b * (gaussianMass (γ n s) (shiftedChildEvent s b v) /
        gaussianMass (γ n s) (historyEvent s) - ν (n + 1) (append s b) / ν n s) := by
  classical
  choose c hc hb using (gainSlab_mass_linear_lower (n := n))
  let f : History (n + 1) → ℝ := fun s => c s / gaussianMass (γ n s) (historyEvent s)
  have hden (s : History (n + 1)) : 0 < gaussianMass (γ n s) (historyEvent s) :=
    universal_history_probability_pos n s
  have hf (s : History (n + 1)) : 0 < f s := div_pos (hc s) (hden s)
  obtain ⟨q, hq, hqbound⟩ := finite_common_positive f hf
  refine ⟨q, hq, ?_⟩
  intro s u hu hu1 v huv b
  have hslab := (hb s u hu hu1).trans (gaussian_signed_gain s hu huv b)
  have h := div_le_div_of_nonneg_right hslab (hden s).le
  have hqmul := mul_le_mul_of_nonneg_right (hqbound s) hu.le
  rw [← gaussian_child_quotient]
  apply hqmul.trans
  dsimp [f]
  convert h using 1 <;> ring

theorem gaussian_gain_linear_stable (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ R : ℝ, 0 ≤ R →
      (∀ s t, |γ n s t| ≤ R) → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (s : History (n + 1)) (σ : Row (n + 1)) (u v e : ℝ),
      0 < u → u ≤ 1 → u ≤ v → 0 ≤ e →
      (∀ t, |σ t| ≤ R) → (∀ t, |σ t - γ n s t| ≤ e) → ∀ b : Bool,
      c * u - K * e ≤ sign b * (gaussianMass σ (shiftedChildEvent s b v) /
        gaussianMass σ (historyEvent s) - ν (n + 1) (append s b) / ν n s) := by
  obtain ⟨c, hc, hgain⟩ := gaussian_gain_linear n
  refine ⟨c, hc, ?_⟩
  intro R hR hγ
  obtain ⟨K, hK, hlip⟩ := gaussian_shifted_lipschitz n R 1 hR (by norm_num)
  refine ⟨K, hK, ?_⟩
  intro s σ u v e hu hu1 huv he hσ hclose b
  have hL := hlip s σ (γ n s) hσ (hγ s) u
    (by simpa only [abs_of_pos hu] using hu1) e he hclose b
  have hG := hgain s u hu hu1 u le_rfl b
  have hM := gaussian_shifted_signed_quotient_mono s σ huv b
  have hA := abs_le.mp hL
  cases b <;> simp only [sign_false, sign_true] at hG hM ⊢ <;>
    nlinarith [hA.1, hA.2]

end MajorityDynamics.Idealized.CriticalDay
