import MajorityDynamics.Probability.ConditionedBinomialFourier.Global

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace MajorityDynamics.Probability.ConditionedBinomialFourier

/-- Complete high-frequency part of Appendix B.5: the actual centered iid-sum
characteristic integral is uniformly negligible relative to the local atom scale.
All constants and thresholds precede the original varying binomial data.
No Fourier, mixture, independence, normalization or integrability certificate
is a hypothesis. The same statement includes a matrix with zero rows. -/
theorem uniform_high_frequency (θ : ℝ) (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (M : Fin r → Fin d → ℤ)
    (hM : Binomial.Approximation.OrthogonalRows M) (strict : Fin r → Bool)
    (T : ℝ) (hT : 1 < T) (δ A : ℝ) (hδ0 : 0 < δ) (hδ : δ < 1/2) (_hA : 0 < A) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
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
    uniform_global_gap θ hθlo hθhi d hd r M hM strict T hT
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
