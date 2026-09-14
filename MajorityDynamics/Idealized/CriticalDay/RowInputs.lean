import MajorityDynamics.Idealized.CriticalDay.Balance

noncomputable section
open Filter Topology
open scoped BigOperators
namespace MajorityDynamics.Idealized.CriticalDay
open Universal LinearResponse PerturbedTilt
open Binomial.Approximation (Density scale)

/-- The original faithful arrays satisfy E.3, with a decaying history error
and a bounded, possibly nonzero, final decision imbalance. -/
theorem faithful_row_inputs (θ T δ : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hδ : 0 < δ) (n ell : ℕ)
    (hk : (n : ℝ) + 1 = 1 / (1 - θ)) :
    ∃ U C : ℝ, T ≤ U ∧ 0 < C ∧ ∀ᶠ N : ℕ in atTop,
    ∀ p : Binomial.Probability, Density θ T N p →
    ∀ a : Process.Data, Process.Specification N p (responseHorizon θ) ell a →
    ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
    ∀ η : History (n + 1) → ℤ, ∀ e : History (n + 1) → History (n + 1) → ℤ,
    FaithfulNumericalData N (p : ℝ) T δ τ a n η e →
    (0 < C * (N : ℝ) ^ (-δ) ∧ C * (N : ℝ) ^ (-δ) ≤ U) ∧
    ∀ s, RowLimits.AdmissibleSizes N p (ell + 1) U
      (C * (N : ℝ) ^ (-δ)) s (naturalSizes η) := by
  let B := Real.sqrt T ^ (n + 1)
  let C := (Fintype.card (History (n + 1)) : ℝ) * T * B
  let D := comparisonConstant n T * B
  let U := max T (C + T * B * lead n)
  have hT0 : 0 < T := by linarith
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (mul_pos (Nat.cast_pos.mpr Fintype.card_pos) hT0) hB
  have hD : 0 < D := mul_pos (hT0.trans_le (comparisonConstant_ge n hT0.le)) hB
  have hU : 0 < U := hT0.trans_le (le_max_left _ _)
  have hCU : C ≤ U := by
    have h := le_max_right T (C + T * B * lead n)
    have := lead_pos n
    dsimp [U]
    nlinarith [mul_pos (mul_pos hT0 hB) (lead_pos n)]
  have hlog : ∀ᶠ N : ℕ in atTop, D + 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  refine ⟨U, C, le_max_left _ _, hC, ?_⟩
  filter_upwards [faithful_geometry θ T δ hθlo hθhi hT hδ n ell hk,
    eventually_basic θ T hθlo hθhi hT,
    eventually_rpow_neg_le δ 1 hδ zero_lt_one, hlog]
    with N hgeo hbasic hpow hlog
  intro p hp a ha τ hτ hτT η e hf
  obtain ⟨_, hcast, _, _⟩ := hgeo p hp a ha τ hτ hτT η e hf
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hbasic.1
  have hp0 := p.property.1
  have hS : 0 < scale N p := Real.sqrt_pos.mpr (by positivity)
  have hβ : 0 ≤ betaScale N (p : ℝ) n := by unfold betaScale; positivity
  have hτ0 : 0 ≤ τ := ((inv_pos.mpr hT0).trans_le hτ).le
  have hsym := ha.symmetry n (Nat.lt_of_succ_lt (critical_level_lt_horizon hk))
  have hspec := ha.estimates n (Nat.lt_of_succ_lt (critical_level_lt_horizon hk))
  have hb : betaScale N (p : ℝ) n * scale N p ≤ B :=
    (critical_scale_bounds hbasic.1 hT0 hp hk hθhi).2
  have hsc := sizeScale_eq N hbasic.1 (p : ℝ) n
  have hsizeScale : sizeScale N (p : ℝ) n ≤ B * N / scale N p := by
    rw [hsc]
    apply (le_div_iff₀ hS).mpr
    nlinarith [mul_le_mul_of_nonneg_right hb hNr.le]
  have hhist : ∀ r : Fin n,
      |∑ t, character r.castSucc t * (naturalSizes η t : ℝ)| ≤
        C * (N : ℝ) ^ (-δ) * N / scale N p := by
    intro r
    simp only [hcast]
    have hh := PerturbedEvolution.faithful_earlier_imbalance hsym hf r
    have hb' := mul_le_mul_of_nonneg_left hsizeScale
      (show 0 ≤ (Fintype.card (History (n + 1)) : ℝ) * T * (N : ℝ) ^ (-δ) by positivity)
    dsimp [C] at *
    ring_nf at hh hb' ⊢
    linarith
  have hclose : ∀ t, |(naturalSizes η t : ℝ) - N * ν n t| ≤
      N / scale N p * Real.log (N : ℝ) ^ (ell + 1) := by
    intro t
    rw [hcast t]
    have hfclose := faithful_size_close hT0.le hτ0 hτT hpow hf t
    have href : |((a.state n).sizes t : ℝ) - N * ν n t| ≤
        N / scale N p * Real.log (N : ℝ) ^ ell := hspec.sizes t
    have hb' := mul_le_mul_of_nonneg_left hsizeScale
      (comparisonConstant_ge n hT0.le |>.trans' hT0.le)
    have hlog1 : 1 ≤ Real.log (N : ℝ) ^ ell := one_le_pow₀ (by linarith [hbasic.2.1])
    have hlogs : Real.log (N : ℝ) ^ ell + D ≤ Real.log (N : ℝ) ^ (ell + 1) := by
      rw [pow_succ]
      nlinarith
    have hh := (abs_sub_le (η t : ℝ) ((a.state n).sizes t : ℝ) (N * ν n t)).trans
      (add_le_add (hfclose.trans hb') href)
    have hlogN := mul_le_mul_of_nonneg_left hlogs (div_pos hNr hS).le
    dsimp [D] at *
    ring_nf at hh hlogN ⊢
    linarith
  have hlead := faithful_lead_error hsym hf
  have hdec : |RowLimits.nextImbalance (naturalSizes η)| ≤ U * N / scale N p := by
    have hlead' : |RowLimits.nextImbalance (naturalSizes η) - τ * sizeScale N (p : ℝ) n * lead n| ≤
        (Fintype.card (History (n + 1)) : ℝ) * (T * sizeScale N (p : ℝ) n * (N : ℝ) ^ (-δ)) := by
      simpa only [RowLimits.nextImbalance, RowLimits.sizeVector, imbalance, hcast] using hlead
    have hlead0 := lead_pos n
    have hmain : |τ * sizeScale N (p : ℝ) n * lead n| ≤ T * B * lead n * N / scale N p := by
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg hτ0 (sizeScale_nonneg _ _ _)) hlead0.le)]
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul hτT hsizeScale (sizeScale_nonneg _ _ _) hT0.le) hlead0.le
      convert hh using 1 <;> first | ring | rfl
    have herr : (Fintype.card (History (n + 1)) : ℝ) *
        (T * sizeScale N (p : ℝ) n * (N : ℝ) ^ (-δ)) ≤ C * N / scale N p := by
      have h1 := mul_le_mul hsizeScale hpow (Real.rpow_nonneg hNr.le _) (by positivity)
      have h2 := mul_le_mul_of_nonneg_left h1
        (show 0 ≤ (Fintype.card (History (n + 1)) : ℝ) * T by positivity)
      dsimp [C]
      convert h2 using 1 <;> first | ring | rfl
    have hh := abs_sub_le (RowLimits.nextImbalance (naturalSizes η))
      (τ * sizeScale N (p : ℝ) n * lead n) 0
    simp only [sub_zero] at hh
    have hUbound := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right T (C + T * B * lead n)) hNr.le) hS.le
    change (C + T * B * lead n) * N / scale N p ≤ U * N / scale N p at hUbound
    ring_nf at hh hlead' hmain herr hUbound ⊢
    linarith
  refine ⟨⟨mul_pos hC (Real.rpow_pos_of_pos hNr _),
    (mul_le_mul_of_nonneg_left hpow hC.le).trans (by simpa using hCU)⟩, ?_⟩
  intro s
  refine ⟨hclose, ?_, hdec⟩
  intro r
  have hid : (∑ t, historyMatrix s r t * (naturalSizes η t : ℝ)) =
      sign (bits (n + 1) s r.succ) * ∑ t, character r.castSucc t * (naturalSizes η t : ℝ) := by
    unfold historyMatrix
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [hid, abs_mul]
  cases bits (n + 1) s r.succ <;> simpa [sign, scale] using hhist r

end MajorityDynamics.Idealized.CriticalDay
