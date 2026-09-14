import MajorityDynamics.Probability.ConditionedBinomialBox.Main
import MajorityDynamics.GraphProcess.EnumerationBounds.BandAsymptotics

/-! Parallel original-law estimates on the uniform sparse density range. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace MajorityDynamics.Probability.ConditionedBinomialBox

theorem uniform_regime_sparse {θ T K ε L : ℝ} (d : ℕ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hK : 1 ≤ K) (hε : 0 < ε) (hL : 1 ≤ L) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹ * (N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-(1/2 : ℝ)) →
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
  obtain ⟨N₀, hN₀⟩ := GraphProcess.EnumerationBounds.eventually_band_window (η := 1/2) (by norm_num) hθhi hT hX hU (M := 1) zero_lt_one
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

theorem uniform_component_sparse (θ : ℝ) (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (d : ℕ) (_hd : 1 ≤ d) (r : ℕ) (M : Fin r → Fin d → ℤ)
    (hM : Binomial.Approximation.OrthogonalRows M) (strict : Fin r → Bool)
    (T : ℝ) (hT : 1 < T) :
    ∃ cWidth CWidth A cPoint cEvent β : ℝ,
      0 < cWidth ∧ 0 < CWidth ∧ 0 ≤ A ∧ 0 < cPoint ∧ 0 < cEvent ∧
      0 < β ∧ β < 1 ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹ * (N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-(1/2 : ℝ)) →
      ∀ (η : Fin d → ℕ) (q : Fin d → Binomial.Probability),
      (∀ i, (N : ℝ)/T ≤ (η i : ℝ)) →
      (∀ i, (η i : ℝ) ≤ T*N) →
      (∀ i, |(q i : ℝ)-p| ≤ T*p/Real.sqrt (p*N)) →
      (∀ j, |∑ i, (M j i : ℝ)*(η i : ℝ)| ≤ T*N/Real.sqrt (p*N)) →
      0 < p ∧ p < 1 ∧ ∃ a : Fin d → ℕ, ∃ L : ℕ,
        BoxConclusion M strict N p η q cWidth CWidth A cPoint cEvent β a L := by
  have hT0 : 0 < T := by linarith
  have hwidth := Geometry.width_pos M
  have hwindow := Geometry.window_pos M hT
  obtain ⟨cPoint, hcPoint, Lmean, hLmean, hpoint⟩ :=
    central_product_lower d (Geometry.window M T) (2*T) hwindow.le (by positivity)
  let cWidth := Geometry.width M / 2
  have hcWidth : 0 < cWidth := by dsimp [cWidth]; positivity
  let cEvent := cPoint*cWidth^d
  have hcEvent : 0 < cEvent := mul_pos hcPoint (pow_pos hcWidth d)
  let β := min (1/2 : ℝ) (cEvent/2)
  have hβ0 : 0 < β := lt_min (by norm_num) (div_pos hcEvent (by norm_num))
  have hβ1 : β < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hβ : β ≤ cPoint*cWidth^d :=
    (min_le_right _ _).trans (by dsimp [cEvent]; linarith)
  let K := max 1 (max (8*Geometry.matrixBound M) (2*T*(Geometry.driftBound M T+2)))
  have hK : 1 ≤ K := le_max_left _ _
  obtain ⟨N₀, hregime⟩ := uniform_regime_sparse (K := K) (ε := 1/(4*T^2))
    (L := Lmean) d hθlo hθhi hT hK (by positivity) hLmean
  refine ⟨cWidth, Geometry.width M, Geometry.window M T, cPoint, cEvent, β,
    hcWidth, hwidth, hwindow.le, hcPoint, hcEvent, hβ0, hβ1, N₀, ?_⟩
  intro N hN p hpLo hpHi η q hηlo hηhi hq hbal
  obtain ⟨hN0, hp0, hpsmall, hsK, hmeans⟩ :=
    hregime N hN p hpLo hpHi η q hηlo hηhi hq
  have hscale : 0 < p*N := mul_pos hp0 hN0
  have hs : 8*Geometry.matrixBound M ≤ Real.sqrt (p*N) :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hsK
  have hslarge : 2*T*(Geometry.driftBound M T+2) ≤ Real.sqrt (p*N) :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hsK
  obtain ⟨hL, hwidthLo, hwidthHi, hgeometry⟩ :=
    Geometry.construct M hM hT hp0 hs hslarge hpsmall (Real.sq_sqrt hscale.le)
      η q (fun i => ⟨hηlo i, hηhi i⟩) hq (fun i => (hmeans i).1) hbal
  have hp1 : p < 1 := by
    apply lt_of_le_of_lt hpsmall
    apply (div_lt_one (by positivity : 0 < 4*T^2)).mpr
    nlinarith
  refine ⟨hp0, hp1, Geometry.starts M T p (Real.sqrt (p*N)) η,
    Geometry.length M (Real.sqrt (p*N)), ?_⟩
  apply assemble M strict N p η q cWidth (Geometry.width M)
    (Geometry.window M T) cPoint β _ _ hscale hcWidth hcPoint hβ0 hβ1 hβ
    hL hwidthLo hwidthHi
    (fun x hx => (hgeometry x hx).1)
    (fun x hx => (hgeometry x hx).2.1)
    (fun x hx => (hgeometry x hx).2.2)
  intro x hx
  apply hpoint (p*N) hscale η q x
    (fun i => (hmeans i).2.1)
    (fun i => (hmeans i).2.2.2.1)
    (fun i => ?_)
    (fun i => (hgeometry x hx).2.2 i)
  simpa only [mul_assoc] using (hmeans i).2.2.2.2

/-- Expanded consumer interface for the subsequent Fourier step: the common
consecutive side length and the actual normalized-restriction mixture are visible. -/
theorem uniform_rectangular_mixture_sparse (θ : ℝ) (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (M : Fin r → Fin d → ℤ)
    (hM : Binomial.Approximation.OrthogonalRows M) (strict : Fin r → Bool)
    (T : ℝ) (hT : 1 < T) :
    ∃ cWidth CWidth β : ℝ, 0 < cWidth ∧ 0 < CWidth ∧ 0 < β ∧ β < 1 ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹ * (N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-(1/2 : ℝ)) →
      ∀ (η : Fin d → ℕ) (q : Fin d → Binomial.Probability),
      (∀ i, (N : ℝ)/T ≤ (η i : ℝ)) →
      (∀ i, (η i : ℝ) ≤ T*N) →
      (∀ i, |(q i : ℝ)-p| ≤ T*p/Real.sqrt (p*N)) →
      (∀ j, |∑ i, (M j i : ℝ)*(η i : ℝ)| ≤ T*N/Real.sqrt (p*N)) →
      ∃ (a : Fin d → ℕ) (L : ℕ) (ν : Measure (Fin d → ℕ)),
        1 ≤ L ∧ cWidth*Real.sqrt (p*N) ≤ (L : ℝ) ∧
        (L : ℝ) ≤ CWidth*Real.sqrt (p*N) ∧ IsProbabilityMeasure ν ∧
        cond (Binomial.law η q)
          (Binomial.inequalityEvent (fun j i => (M j i : ℝ)) strict) =
          ENNReal.ofReal β • uniformBox (Geometry.box a L) + ENNReal.ofReal (1-β) • ν := by
  obtain ⟨cw, Cw, A, cp, ce, β, hcw, hCw, _hA, _hcp, _hce, hβ0, hβ1, N₀, h⟩ :=
    uniform_component_sparse θ hθlo hθhi d hd r M hM strict T hT
  refine ⟨cw, Cw, β, hcw, hCw, hβ0, hβ1, N₀, ?_⟩
  intro N hN p hpLo hpHi η q hηlo hηhi hq hbal
  obtain ⟨_hp0, _hp1, a, L, hb⟩ := h N hN p hpLo hpHi η q hηlo hηhi hq hbal
  obtain ⟨ν, hν, hmix⟩ := hb.mixture
  exact ⟨a, L, ν, hb.length_pos, hb.width_lower, hb.width_upper, hν, hmix⟩

end MajorityDynamics.Probability.ConditionedBinomialBox

