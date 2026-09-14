import MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Generic
import MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Moments
import MajorityDynamics.Probability.ConditionedBinomialBox.Main
import MajorityDynamics.Probability.ConditionedBinomialFourier.Main

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace MajorityDynamics.Probability.ConditionedBinomialLocalCLT
open ConditionedBinomialFourier

/-- The full conditioned local central limit theorem of Appendix B.5.
The fixed constant and threshold precede every varying parameter. The probability
is that of the actual independent copies of the original conditioned binomial law,
and the target is the actual mean, required to be an integer vector. -/
theorem uniform_local_clt (θ : ℝ) (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (M : Fin r → Fin d → ℤ)
    (hM : Binomial.Approximation.OrthogonalRows M) (strict : Fin r → Bool)
    (T : ℝ) (hT : 1 < T) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
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
      ∀ z : Fin d → ℤ, (∀ i, (z i : ℝ) = (m : ℝ)*mean ρ i) →
        c*((N : ℝ)^2*p)^(-(d : ℝ)/2) ≤
          (copyLaw ρ m).real {x | ∀ i, (∑ j, (x j i : ℤ)) = z i} := by
  have hT0 : 0 < T := by linarith
  obtain ⟨cw, Cw, A, cp, ce, β, _hcw, _hCw, _hA, _hcp, hce, _hβ, _hβ1,
    Nbox, hbox⟩ := ConditionedBinomialBox.uniform_component θ hθlo hθhi d hd r M hM strict T hT
  obtain ⟨C, hC, hmom⟩ := uniform_directional_moments d (U := 2*T) hce (by linarith)
  obtain ⟨Nreg, hreg⟩ := ConditionedBinomialBox.uniform_regime
    (K := 1) (ε := 1) (L := 1) d hθlo hθhi hT (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Nlow, hlow⟩ := uniform_atom_lower d θ T C hθhi hT0 hC
  obtain ⟨Nhigh, hhigh⟩ := uniform_high_frequency θ hθlo hθhi d hd r M hM strict T hT
    (Scaling.delta d) 1 (Scaling.delta_pos d) (Scaling.delta_lt_half d) (by norm_num)
  refine ⟨localConstant d T C, localConstant_pos d T C,
    max (max Nbox Nreg) (max Nlow Nhigh), ?_⟩
  intro N hN p hpLo hpHi η q m hηlo hηhi hq hbal hmlo hmhi
  have hNb : Nbox ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNr : Nreg ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hNl : Nlow ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNh : Nhigh ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨hp0, _hp1, a, L, hb⟩ := hbox N hNb p hpLo hpHi η q hηlo hηhi hq hbal
  obtain ⟨hN0, _, _, hs, hmeans⟩ := hreg N hNr p hpLo hpHi η q hηlo hηhi hq
  let E := Binomial.inequalityEvent (fun j i => (M j i : ℝ)) strict
  let ρ := cond (Binomial.law η q) E
  have hmeans' (i : Fin d) : (η i : ℝ)*(q i : ℝ) ≤ (2*T)*(Real.sqrt (p*N))^2 := by
    rw [Real.sq_sqrt (mul_pos hp0 hN0).le]
    simpa only [mul_assoc] using (hmeans i).2.2.2.2
  obtain ⟨hall, hρ, hmoments⟩ := hmom η q E (Real.sqrt (p*N)) hb.event_mass hs hmeans'
  let : IsProbabilityMeasure ρ := hρ
  have hH := hhigh N hNh p hpLo hpHi η q m hηlo hηhi hq hbal hmlo hmhi
  refine ⟨hρ, inferInstance, ?_⟩
  intro z hz
  have hout := hlow N hNl p hpLo ρ m hmhi hall
    (fun t => (hmoments t).1) (fun t => (hmoments t).2) hH.2.2.2.2 z hz
  rw [integerSum_event_forall] at hout
  exact hout

/-- The same original-input local CLT, expressed as the literal event that the
sum of independent copies equals its actual mean. The integrality hypothesis is
explicit; no lattice atom is inferred from real centering alone. -/
theorem uniform_mean_local_clt (θ : ℝ) (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (M : Fin r → Fin d → ℤ)
    (hM : Binomial.Approximation.OrthogonalRows M) (strict : Fin r → Bool)
    (T : ℝ) (hT : 1 < T) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
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
      ((∃ z : Fin d → ℤ, ∀ i, (z i : ℝ) = (m : ℝ)*mean ρ i) →
        c*((N : ℝ)^2*p)^(-(d : ℝ)/2) ≤
          (copyLaw ρ m).real {x | copySum x = fun i => (m : ℝ)*mean ρ i}) := by
  obtain ⟨c, hc, N₀, h⟩ := uniform_local_clt θ hθlo hθhi d hd r M hM strict T hT
  refine ⟨c, hc, N₀, ?_⟩
  intro N hN p hpLo hpHi η q m hηlo hηhi hq hbal hmlo hmhi
  obtain ⟨hρ, hcopies, hout⟩ := h N hN p hpLo hpHi η q m hηlo hηhi hq hbal hmlo hmhi
  refine ⟨hρ, hcopies, ?_⟩
  rintro ⟨z, hz⟩
  have hbound := hout z hz
  rw [← integerSum_event_forall, integerSum_mean_event _ z hz] at hbound
  exact hbound

end MajorityDynamics.Probability.ConditionedBinomialLocalCLT
