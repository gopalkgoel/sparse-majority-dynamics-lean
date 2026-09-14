import MajorityDynamics.Probability.ConditionedBinomialBox.Regime

noncomputable section

namespace MajorityDynamics.Probability.ConditionedBinomialFourier

/-- A fixed loss in scale passes through the clipped quadratic frequency. -/
theorem min_mul_lower {a x : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) :
    min a 1 * min x 1 ≤ min (a*x) 1 := by
  apply le_min
  · exact mul_le_mul (min_le_left _ _) (min_le_left _ _)
      (le_min hx zero_le_one) ha
  · calc
      min a 1 * min x 1 ≤ 1 * 1 := mul_le_mul (min_le_right _ _)
        (min_le_right _ _) (le_min hx zero_le_one) zero_le_one
      _ = 1 := by ring

/-- The literal side-length lower bound supplies the required density scale. -/
theorem width_min_lower {w s z : ℝ} {L : ℕ}
    (hw : 0 ≤ w) (hs : 0 ≤ s) (hwidth : w*Real.sqrt s ≤ (L : ℝ)) :
    min (w^2) 1 * min (s*z^2) 1 ≤ min ((L : ℝ)^2*z^2) 1 := by
  have hsquare : w^2*s ≤ (L : ℝ)^2 := by
    have h := sq_le_sq₀ (mul_nonneg hw (Real.sqrt_nonneg s)) (Nat.cast_nonneg L)
    have heq : (w * Real.sqrt s)^2 = w^2*s := by
      rw [mul_pow, Real.sq_sqrt hs]
    rw [heq] at h
    exact h.mpr hwidth
  calc
    min (w^2) 1 * min (s*z^2) 1 ≤ min (w^2*(s*z^2)) 1 :=
      min_mul_lower (sq_nonneg w) (mul_nonneg hs (sq_nonneg z))
    _ ≤ min ((L : ℝ)^2*z^2) 1 :=
      min_le_min_right 1 (by nlinarith [mul_le_mul_of_nonneg_right hsquare (sq_nonneg z)])

/-- Scalar amplification of a characteristic-function gap. -/
theorem pow_le_exp_of_gap {x u : ℝ} (m : ℕ) (hx : 0 ≤ x)
    (hgap : x ≤ 1-u) : x^m ≤ Real.exp (-u*(m : ℝ)) := by
  have h : x ≤ Real.exp (-u) := by
    have he := Real.add_one_le_exp (-u)
    linarith
  calc
    x^m ≤ (Real.exp (-u))^m := pow_le_pow_left₀ hx h m
    _ = Real.exp (-u*(m : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- The growing expected-degree scale makes every fixed positive-width box
long enough for the complete scalar frequency estimate. -/
theorem eventually_length_sixteen {θ T w : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hw : 0 < w) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      1 ≤ (N : ℝ) ∧ 0 < p ∧ p < 1 ∧
      ∀ L : ℕ, w*Real.sqrt (p*N) ≤ (L : ℝ) → 16 ≤ L := by
  obtain ⟨N₀, h⟩ := GraphProcess.EnumerationBounds.eventually_window
    hθlo hθhi hT (L := (16/w)^2) (U := 1/2) (M := 1)
    (by positivity) (by norm_num) zero_lt_one
  refine ⟨N₀, ?_⟩
  intro N hN p hlo hhi
  obtain ⟨hN0, hp, hN1, hscale, hpHalf⟩ := h N hN p hlo hhi
  refine ⟨hN1, hp, by linarith, ?_⟩
  intro L hL
  have hs : 0 ≤ p*N := mul_nonneg hp.le hN0.le
  have hsqrt : 16/w ≤ Real.sqrt (p*N) := by
    have hsq := Real.sq_sqrt hs
    have hnonneg := Real.sqrt_nonneg (p*N)
    have hdiv : 0 < 16/w := by positivity
    nlinarith [sq_nonneg (Real.sqrt (p*N) - 16/w)]
  have hmul := mul_le_mul_of_nonneg_left hsqrt hw.le
  have hcancel : w*(16/w) = 16 := by field_simp
  rw [hcancel] at hmul
  exact_mod_cast hmul.trans hL

end MajorityDynamics.Probability.ConditionedBinomialFourier
