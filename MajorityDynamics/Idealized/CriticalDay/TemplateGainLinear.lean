import MajorityDynamics.Idealized.CriticalDay.GaussianGainLinear
import MajorityDynamics.Idealized.CriticalDay.TemplateGain

/-! Linear-in-shift gain for the exact binomial template. The approximation
and faithful-size errors must be small relative to the comparison shift. -/
noncomputable section
open Set MeasureTheory
namespace MajorityDynamics.Idealized.CriticalDay
open Universal RowLimits

theorem template_gain_linear (n : ℕ) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ R : ℝ, 0 ≤ R →
      (∀ s t, |γ n s t| ≤ R) → ∃ e₀ : ℝ, 0 < e₀ ∧
      ∀ (N : ℕ) (p : Binomial.Probability) (sizes : Local.Sizes n)
        (σ : History (n + 1) → Row (n + 1)) (u v e : ℝ),
      0 < u → u ≤ 1 → u ≤ v → 0 ≤ e → e ≤ e₀ * u →
      (∀ s t, |σ s t| ≤ R) → (∀ s t, |σ s t - γ n s t| ≤ e) →
      (∀ s, |(sizes s : ℝ) - (N : ℝ) * ν n s| ≤ e * N) →
      (∀ s b, |binomialSplit N p sizes s b (σ s) -
        gaussianMass (σ s) (shiftedChildEvent s b v) /
          gaussianMass (σ s) (historyEvent s)| ≤ e) →
      ∀ s b, ζ * u * N ≤ sign b *
        (Local.templateSizes sizes (fun s => rowTilt N p (σ s)) (append s b) -
          (N : ℝ) * ν (n + 1) (append s b)) := by
  obtain ⟨g, hg, hgaussian⟩ := gaussian_gain_linear_stable n
  obtain ⟨m, hm, hmin⟩ := finite_common_positive (ν n) (ν_positive n)
  let ζ := m * g / 4
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  refine ⟨ζ, hζ, ?_⟩
  intro R hR hγ
  obtain ⟨K, hK, hgain⟩ := hgaussian R hR hγ
  let e₀ := min (g / (2 * (K + 1))) ζ
  have he₀ : 0 < e₀ := lt_min (by positivity) hζ
  refine ⟨e₀, he₀, ?_⟩
  intro N p sizes σ u v e hu hu1 huv he he0 hσ hclose hsizes hsplit s b
  have heK : (K + 1) * e ≤ g * u / 2 := by
    have h := he0.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hu.le)
    have hmul := mul_le_mul_of_nonneg_left h (show 0 ≤ 2 * (K + 1) by positivity)
    have hid : 2 * (K + 1) * (g / (2 * (K + 1)) * u) = g * u := by field_simp
    rw [hid] at hmul
    linarith
  have heζ : e ≤ ζ * u := he0.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hu.le)
  have hG := hgain s (σ s) u v e hu hu1 huv he (hσ s) (hclose s) b
  let q := binomialSplit N p sizes s b (σ s)
  let r := ν (n + 1) (append s b) / ν n s
  have hq : g * u / 2 ≤ sign b * (q - r) := by
    have h1 := abs_le.mp (hsplit s b)
    cases b <;> simp only [sign_false, sign_true] at hG ⊢ <;>
      dsimp [q, r] <;> nlinarith [h1.1, h1.2]
  have hqb := binomialSplit_bounds N p sizes s b (σ s)
  have habs : |sign b| = 1 := by cases b <;> norm_num [sign]
  have herror : -(e * N) ≤ sign b * ((sizes s : ℝ) - (N : ℝ) * ν n s) * q := by
    have hh : |sign b * ((sizes s : ℝ) - (N : ℝ) * ν n s) * q| ≤ e * N := by
      rw [abs_mul, abs_mul, habs, one_mul, abs_of_nonneg hqb.1]
      exact (mul_le_mul_of_nonneg_left hqb.2 (abs_nonneg _)).trans
        (by simpa using hsizes s)
    exact (abs_le.mp hh).1
  have hNg := mul_le_mul_of_nonneg_left hq
    (mul_nonneg (Nat.cast_nonneg N) (ν_positive n s).le)
  have hNm := mul_le_mul_of_nonneg_right (hmin s)
    (show 0 ≤ (N : ℝ) * (g * u / 2) by positivity)
  have hNe := mul_le_mul_of_nonneg_right heζ (Nat.cast_nonneg N)
  have hr : ν n s * r = ν (n + 1) (append s b) := by
    dsimp [r]
    exact mul_div_cancel₀ _ (ν_positive n s).ne'
  have ht : Local.templateSizes sizes (fun s => rowTilt N p (σ s)) (append s b) =
      (sizes s : ℝ) * q := by
    simp only [Local.templateSizes, parent_append, last_append]
    rfl
  rw [ht]
  have heq : sign b * ((sizes s : ℝ) * q - (N : ℝ) * ν (n + 1) (append s b)) =
      sign b * ((sizes s : ℝ) - (N : ℝ) * ν n s) * q +
        (N : ℝ) * ν n s * (sign b * (q - r)) := by
    rw [← hr]
    ring
  rw [heq]
  dsimp [ζ] at hNe ⊢
  nlinarith only [herror, hNg, hNm, hNe]

end MajorityDynamics.Idealized.CriticalDay
