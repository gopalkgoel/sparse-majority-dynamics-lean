import MajorityDynamics.Probability.ConditionedBinomialBox.Conclusions
import MajorityDynamics.Probability.ConditionedBinomialBox.Regime

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace MajorityDynamics.Probability.ConditionedBinomialBox

/-- The complete good-box and fixed-positive-weight rectangular-component step
of Appendix B.5, from the original matrix, density, sizes, tilts and balances.
All constants precede every varying input, and the same theorem includes `r=0`. -/
theorem uniform_component (θ : ℝ) (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (d : ℕ) (_hd : 1 ≤ d) (r : ℕ) (M : Fin r → Fin d → ℤ)
    (hM : Binomial.Approximation.OrthogonalRows M) (strict : Fin r → Bool)
    (T : ℝ) (hT : 1 < T) :
    ∃ cWidth CWidth A cPoint cEvent β : ℝ,
      0 < cWidth ∧ 0 < CWidth ∧ 0 ≤ A ∧ 0 < cPoint ∧ 0 < cEvent ∧
      0 < β ∧ β < 1 ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹ * (N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-θ) →
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
  obtain ⟨N₀, hregime⟩ := uniform_regime (K := K) (ε := 1/(4*T^2))
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
theorem uniform_rectangular_mixture (θ : ℝ) (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (M : Fin r → Fin d → ℤ)
    (hM : Binomial.Approximation.OrthogonalRows M) (strict : Fin r → Bool)
    (T : ℝ) (hT : 1 < T) :
    ∃ cWidth CWidth β : ℝ, 0 < cWidth ∧ 0 < CWidth ∧ 0 < β ∧ β < 1 ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹ * (N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-θ) →
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
    uniform_component θ hθlo hθhi d hd r M hM strict T hT
  refine ⟨cw, Cw, β, hcw, hCw, hβ0, hβ1, N₀, ?_⟩
  intro N hN p hpLo hpHi η q hηlo hηhi hq hbal
  obtain ⟨_hp0, _hp1, a, L, hb⟩ := h N hN p hpLo hpHi η q hηlo hηhi hq hbal
  obtain ⟨ν, hν, hmix⟩ := hb.mixture
  exact ⟨a, L, ν, hb.length_pos, hb.width_lower, hb.width_upper, hν, hmix⟩

/-- With no matrix rows the literal original event is the whole sample space. -/
theorem unconstrained_event (d : ℕ) (M : Fin 0 → Fin d → ℤ) (strict : Fin 0 → Bool) :
    Binomial.inequalityEvent (fun j i => (M j i : ℝ)) strict = Set.univ := by
  ext x
  simp [Binomial.inequalityEvent]

theorem unconstrained_conditioning (d : ℕ) (M : Fin 0 → Fin d → ℤ)
    (strict : Fin 0 → Bool) (η : Fin d → ℕ) (q : Fin d → Binomial.Probability) :
    cond (Binomial.law η q) (Binomial.inequalityEvent (fun j i => (M j i : ℝ)) strict) =
      Binomial.law η q := by
  rw [unconstrained_event, cond_univ]

end MajorityDynamics.Probability.ConditionedBinomialBox
