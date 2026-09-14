import MajorityDynamics.Probability.ConditionedBinomialFourier.Main
import MajorityDynamics.GraphProcess.EnumerationBounds.BandAsymptotics
import MajorityDynamics.Probability.ConditionedBinomialBox.Sparse

/-! Parallel original-law estimates on the uniform sparse density range. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace MajorityDynamics.Probability.ConditionedBinomialFourier

theorem eventually_length_sixteen_sparse {θ T w : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hw : 0 < w) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-(1/2 : ℝ)) →
      1 ≤ (N : ℝ) ∧ 0 < p ∧ p < 1 ∧
      ∀ L : ℕ, w*Real.sqrt (p*N) ≤ (L : ℝ) → 16 ≤ L := by
  obtain ⟨N₀, h⟩ := GraphProcess.EnumerationBounds.eventually_band_window (η := 1/2) (by norm_num) hθhi hT (L := (16/w)^2) (U := 1/2) (M := 1)
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

theorem uniform_global_gap_sparse (θ : ℝ) (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (M : Fin r → Fin d → ℤ)
    (hM : Binomial.Approximation.OrthogonalRows M) (strict : Fin r → Bool)
    (T : ℝ) (hT : 1 < T) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1/2 ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-(1/2 : ℝ)) →
      ∀ (η : Fin d → ℕ) (q : Fin d → Binomial.Probability),
      (∀ i, (N : ℝ)/T ≤ (η i : ℝ)) →
      (∀ i, (η i : ℝ) ≤ T*N) →
      (∀ i, |(q i : ℝ)-p| ≤ T*p/Real.sqrt (p*N)) →
      (∀ j, |∑ i, (M j i : ℝ)*(η i : ℝ)| ≤ T*N/Real.sqrt (p*N)) →
      let ρ := cond (Binomial.law η q)
        (Binomial.inequalityEvent (fun j i => (M j i : ℝ)) strict)
      0 < p ∧ p < 1 ∧ IsProbabilityMeasure ρ ∧
      (∀ t ∈ HighFrequency.cube d, ‖chi ρ t‖ ≤ 1-c*min (p*N*‖t‖^2) 1) ∧
      ∀ (m : ℕ) (t : Fin d → ℝ), t ∈ HighFrequency.cube d →
        ‖centeredChi ρ m t‖ ≤ Real.exp (-c*m*min (p*N*‖t‖^2) 1) := by
  obtain ⟨w, W, A, cp, ce, β, hw, _hW, _hA, _hcp, _hce, hβ0, hβ1, N₁, hbox⟩ :=
    ConditionedBinomialBox.uniform_component_sparse θ hθlo hθhi d hd r M hM strict T hT
  obtain ⟨N₂, hlength⟩ := eventually_length_sixteen_sparse hθlo hθhi hT hw
  refine ⟨gapConstant β w, gapConstant_pos hβ0 hw,
    gapConstant_le_half hβ0.le hβ1.le, max N₁ N₂, ?_⟩
  intro N hN p hlo hhi η q hηlo hηhi hq hbal
  obtain ⟨hp, hp1, a, L, hb⟩ := hbox N ((le_max_left _ _).trans hN)
    p hlo hhi η q hηlo hηhi hq hbal
  obtain ⟨_hN1, _hp, _hp1, hlength⟩ := hlength N ((le_max_right _ _).trans hN) p hlo hhi
  let ρ := cond (Binomial.law η q)
    (Binomial.inequalityEvent (fun j i => (M j i : ℝ)) strict)
  let : IsProbabilityMeasure ρ := hb.conditioned_probability
  obtain ⟨ν, hν, hmix⟩ := hb.mixture
  let := hν
  have hgap : ∀ t ∈ HighFrequency.cube d,
      ‖chi ρ t‖ ≤ 1-gapConstant β w*min (p*N*‖t‖^2) 1 := by
    intro t ht
    change ‖chi (cond (Binomial.law η q) _) t‖ ≤ _
    rw [hmix]
    exact rectangular_mixture_gap hd a ν hβ0 hβ1 hw
      (mul_nonneg hp.le (Nat.cast_nonneg N)) (hlength L hb.width_lower)
      hb.width_lower t ht
  refine ⟨hp, hp1, hb.conditioned_probability, hgap, ?_⟩
  intro m t ht
  have h := centeredChi_exp_of_gap ρ m t (hgap t ht)
  convert h using 1
  congr 1
  ring

theorem uniform_high_frequency_sparse (θ : ℝ) (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (M : Fin r → Fin d → ℤ)
    (hM : Binomial.Approximation.OrthogonalRows M) (strict : Fin r → Bool)
    (T : ℝ) (hT : 1 < T) (δ A : ℝ) (hδ0 : 0 < δ) (hδ : δ < 1/2) (_hA : 0 < A) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-(1/2 : ℝ)) →
      ∀ (η : Fin d → ℕ) (q : Fin d → Binomial.Probability) (m : ℕ),
      (∀ i, (N : ℝ)/T ≤ (η i : ℝ)) →
      (∀ i, (η i : ℝ) ≤ T*N) →
      (∀ i, |(q i : ℝ)-p| ≤ T*p/Real.sqrt (p*N)) →
      (∀ j, |∑ i, (M j i : ℝ)*(η i : ℝ)| ≤ T*N/Real.sqrt (p*N)) →
      (N : ℝ)/T ≤ (m : ℝ) → (m : ℝ) ≤ T*N →
      let ρ := cond (Binomial.law η q)
        (Binomial.inequalityEvent (fun j i => (M j i : ℝ)) strict)
      IsProbabilityMeasure ρ ∧ IsProbabilityMeasure (copyLaw ρ m) ∧
      IntegrableOn (centeredChi ρ m) (HighFrequency.region d N p δ) ∧
      (∀ t ∈ HighFrequency.region d N p δ, ‖centeredChi ρ m t‖ ≤ (N : ℝ)^(-A)) ∧
      ‖∫ t in HighFrequency.region d N p δ, centeredChi ρ m t‖ ≤
        (N : ℝ)^(-A)*((N : ℝ)^2*p)^(-(d : ℝ)/2) := by
  obtain ⟨c, hc, _hc1, N₁, hglobal⟩ :=
    uniform_global_gap_sparse θ hθlo hθhi d hd r M hM strict T hT
  obtain ⟨N₂, hdecay⟩ := HighFrequency.uniform_decay d c T δ A hc
    (by linarith) hδ0 hδ
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN p hlo hhi η q m hηlo hηhi hq hbal hm _hmhi
  obtain ⟨hp, hp1, hρ, _hgap, hamp⟩ := hglobal N ((le_max_left _ _).trans hN)
    p hlo hhi η q hηlo hηhi hq hbal
  let ρ := cond (Binomial.law η q)
    (Binomial.inequalityEvent (fun j i => (M j i : ℝ)) strict)
  let : IsProbabilityMeasure ρ := hρ
  obtain ⟨hpoint, hint⟩ := hdecay N ((le_max_right _ _).trans hN) p m
    (centeredChi ρ m) hp hp1.le hm (hamp m)
  exact ⟨hρ, inferInstance, HighFrequency.integrableOn_region _
    (centeredChi_continuous ρ m).measurable hpoint, hpoint, hint⟩

end MajorityDynamics.Probability.ConditionedBinomialFourier

