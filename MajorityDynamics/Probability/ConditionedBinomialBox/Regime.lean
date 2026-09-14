import MajorityDynamics.GraphProcess.EnumerationBounds.Asymptotics
import MajorityDynamics.Binomial.Basic

noncomputable section

namespace MajorityDynamics.Probability.ConditionedBinomialBox

/-- Uniform scalar preparation from the original density, size and tilt windows.
The requested square-root scale and binomial means can be arbitrarily large,
and the density arbitrarily small, with one threshold preceding all varying data. -/
theorem uniform_regime {θ T K ε L : ℝ} (d : ℕ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hK : 1 ≤ K) (hε : 0 < ε) (hL : 1 ≤ L) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹ * (N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-θ) →
      ∀ (η : Fin d → ℕ) (q : Fin d → Binomial.Probability),
      (∀ i, (N : ℝ) / T ≤ (η i : ℝ)) →
      (∀ i, (η i : ℝ) ≤ T * N) →
      (∀ i, |(q i : ℝ) - p| ≤ T * p / Real.sqrt (p * N)) →
      0 < (N : ℝ) ∧ 0 < p ∧ p ≤ ε ∧ K ≤ Real.sqrt (p * N) ∧
      ∀ i, p / 2 ≤ (q i : ℝ) ∧ (q i : ℝ) ≤ 1 / 2 ∧
        p * N / (2 * T) ≤ (η i : ℝ) * (q i : ℝ) ∧
        L ≤ (η i : ℝ) * (q i : ℝ) ∧
        (η i : ℝ) * (q i : ℝ) ≤ 2 * T * p * N := by
  have hT0 : 0 < T := by linarith
  let X : ℝ := max (max (K^2) ((2*T)^2)) (2*T*L)
  have hX : 0 < X := by
    exact lt_of_lt_of_le (by positivity : 0 < 2*T*L) (le_max_right _ _)
  have hU : 0 < min ε (1/4 : ℝ) := lt_min hε (by norm_num)
  obtain ⟨N₀, hN₀⟩ := GraphProcess.EnumerationBounds.eventually_window
    hθlo hθhi hT hX hU (M := 1) zero_lt_one
  refine ⟨N₀, ?_⟩
  intro N hN p hpLo hpHi η q hηlo hηhi hq
  obtain ⟨hN0, hp0, _, hx, hp⟩ := hN₀ N hN p hpLo hpHi
  have hx0 : 0 < p * (N : ℝ) := mul_pos hp0 hN0
  have hs0 : 0 < Real.sqrt (p * N) := Real.sqrt_pos.mpr hx0
  have hs2 := Real.sq_sqrt hx0.le
  have hKsq : K^2 ≤ p*N := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hTsq : (2*T)^2 ≤ p*N := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hscale : 2*T*L ≤ p*N := (le_max_right _ _).trans hx
  have hsK : K ≤ Real.sqrt (p*N) := by
    nlinarith [sq_nonneg (Real.sqrt (p*N) - K)]
  have hsT : 2*T ≤ Real.sqrt (p*N) := by
    nlinarith [sq_nonneg (Real.sqrt (p*N) - 2*T)]
  refine ⟨hN0, hp0, hp.trans (min_le_left _ _), hsK, ?_⟩
  intro i
  have htilt : |(q i : ℝ)-p| ≤ p/2 := by
    apply (hq i).trans
    apply (div_le_iff₀ hs0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsT hp0.le]
  have hqlo : p/2 ≤ (q i : ℝ) := by linarith [(abs_le.mp htilt).1]
  have hqhi : (q i : ℝ) ≤ 2*p := by linarith [(abs_le.mp htilt).2]
  have hqhalf : (q i : ℝ) ≤ 1/2 := by
    have hpquarter := hp.trans (min_le_right _ _)
    linarith
  have hmeanlo : p*N/(2*T) ≤ (η i : ℝ)*(q i : ℝ) := by
    calc
      p*N/(2*T) = ((N : ℝ)/T)*(p/2) := by ring
      _ ≤ (η i : ℝ)*(q i : ℝ) :=
        mul_le_mul (hηlo i) hqlo (by positivity) (by positivity)
  have hmeanL : L ≤ (η i : ℝ)*(q i : ℝ) := by
    apply le_trans _ hmeanlo
    apply (le_div_iff₀ (by positivity : 0 < 2*T)).mpr
    nlinarith only [hscale]
  have hmeanhi : (η i : ℝ)*(q i : ℝ) ≤ 2*T*p*N := by
    calc
      (η i : ℝ)*(q i : ℝ) ≤ (T*N)*(2*p) :=
        mul_le_mul (hηhi i) hqhi (q i).property.1.le (by positivity)
      _ = 2*T*p*N := by ring
  exact ⟨hqlo, hqhalf, hmeanlo, hmeanL, hmeanhi⟩

end MajorityDynamics.Probability.ConditionedBinomialBox
