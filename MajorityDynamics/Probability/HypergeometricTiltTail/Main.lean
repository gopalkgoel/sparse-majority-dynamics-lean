import MajorityDynamics.Probability.HypergeometricTiltTail.Results
import MajorityDynamics.Probability.HypergeometricTiltTail.Tail
import MajorityDynamics.Probability.HypergeometricTiltTail.Polynomial
import MajorityDynamics.Probability.HypergeometricTiltTail.NumericAbsorption
import MajorityDynamics.Probability.HypergeometricTiltTail.Adapters

noncomputable section
open scoped BigOperators
namespace MajorityDynamics.Probability.HypergeometricTiltTail
open FixedSizeExponential

/-- A fixed harmless coefficient absorbing the three central-atom prefactors. -/
def tailCost (T : ℝ) : ℝ := 28*T+3*((1+1/centralAtomConstant)+1)

theorem factor_regime {V : Type*} [DecidableEq V]
    {N : ℕ} {T p h L : ℝ} (hT : 1 < T) (r : Numerics.Regime N p T)
    {P S : Finset V} (hSP : S ⊆ P)
    (hMlo : (N:ℝ)-1 ≤ P.card) (hMhi : (P.card:ℝ) ≤ N)
    (hhlo : (N:ℝ)/T ≤ h) (hhhi : h ≤ N-(N:ℝ)/T)
    (hHh : |(S.card:ℝ)-h| ≤ 1) (hL : (N:ℝ)/T ≤ L)
    (β : V → ℝ) (hβ : ∀ v ∈ P, |β v| ≤ Real.log (N:ℝ))
    {d t : ℤ} (hd : |(d:ℝ)-p*N| ≤ Real.sqrt (p*N)*Real.log (N:ℝ))
    (ht : 0 ≤ t) (htd : t ≤ d)
    (hτ : (Real.log (N:ℝ))^100 ≤ |((t:ℝ)-p*h)/Real.sqrt (p*h)|) :
    weightedFactor P S d t p L β ≤
      Real.exp (tailCost T*(|((t:ℝ)-p*h)/Real.sqrt (p*h)| *Real.log (N:ℝ)+
        (Real.log (N:ℝ))^2+Real.log (N:ℝ)+1)) *
      Real.exp (-(((t:ℝ)-p*h)/Real.sqrt (p*h))^2/(32*T)) := by
  have hg := hypergeomMass_regime_tail hT r hMlo hMhi
    (Finset.card_le_card hSP) hhlo hhhi hHh hd ht htd hτ
  have he := tiltExpectation_regime hT r hSP hMlo hMhi hhlo hhhi hHh hL β hβ hd ht htd
  have hN : 0 < (N:ℝ) := by linarith [r.N_large]
  have hD : 1 ≤ 1+1/centralAtomConstant := by
    have := div_pos zero_lt_one centralAtomConstant_pos
    linarith
  have hpref := polynomial_prefactor_absorb hD (by linarith : 0 ≤ T) hN r.log_large
    (τ := ((t:ℝ)-p*h)/Real.sqrt (p*h))
  unfold weightedFactor
  have hprod := mul_le_mul hg he (tiltExpectation_nonneg _ _ _ _ _ _ _)
    (mul_nonneg (by positivity) (Real.exp_pos _).le)
  calc
    _ ≤ _ := hprod
    _ = (((1+1/centralAtomConstant)*(N:ℝ))^3 *
        Real.exp (28*T*(|((t:ℝ)-p*h)/Real.sqrt (p*h)| *Real.log (N:ℝ)+
          (Real.log (N:ℝ))^2))) *
        Real.exp (-(((t:ℝ)-p*h)/Real.sqrt (p*h))^2/(32*T)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le

/-- Complete analytic factor bound for the original sparse window. The constants
precede every varying population, subset, normalization, coefficient and integer
count. The population can be full or have one deleted vertex. -/
theorem uniform_factor {θ T B : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hB : 0 ≤ B) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-θ) →
      ∀ (V : Type*) [DecidableEq V] (P S : Finset V), S ⊆ P →
      (P.card = N ∨ P.card = N-1) → ∀ h : ℕ,
      (N:ℝ)/T ≤ h → (h:ℝ) ≤ N-(N:ℝ)/T → |(S.card:ℝ)-(h:ℝ)| ≤ 1 →
      ∀ L : ℝ, (N:ℝ)/T ≤ L → L ≤ T*N →
      ∀ β : V → ℝ, (∀ v ∈ P, |β v| ≤ Real.log (N:ℝ)) →
      ∀ d t : ℤ, |(d:ℝ)-p*N| ≤ Real.sqrt (p*N)*Real.log (N:ℝ) →
      0 ≤ t → t ≤ d →
      (Real.log (N:ℝ))^100 ≤ |((t:ℝ)-p*h)/Real.sqrt (p*h)| →
      Real.exp (B*(Real.log (N:ℝ))^4) * weightedFactor P S d t p L β ≤
        Real.exp (-c*(((t:ℝ)-p*h)/Real.sqrt (p*h))^2) := by
  have hC : 0 ≤ tailCost T := by unfold tailCost; have := centralAtomConstant_pos; positivity
  have hK : 0 < 32*T := by linarith
  obtain ⟨N₁,h₁⟩ := Numerics.uniform_regime hθlo hθhi hT
  obtain ⟨N₂,h₂⟩ := Numerics.eventually_exp_absorb hB hC hK
  refine ⟨1/(2*(32*T)), by positivity, max N₁ N₂, ?_⟩
  intro N hN p hlo hhi V _ P S hSP hM h hhlo hhhi hHh L hL _hLhi β hβ d t hd ht htd hτ
  have r := h₁ N ((le_max_left _ _).trans hN) p hlo hhi
  have hNr : 1 ≤ (N:ℝ) := by linarith [r.N_large]
  have hNnat : 1 ≤ N := by exact_mod_cast hNr
  have hMlo : (N:ℝ)-1 ≤ P.card := by
    rcases hM with he | he <;> rw [he]
    · linarith
    · rw [Nat.cast_sub hNnat]; norm_num
  have hMhi : (P.card:ℝ) ≤ N := by
    rcases hM with he | he
    · rw [he]
    · rw [he]
      exact_mod_cast Nat.sub_le N 1
  have hf := factor_regime hT r hSP hMlo hMhi hhlo hhhi hHh hL β hβ hd ht htd hτ
  calc
    _ ≤ Real.exp (B*(Real.log (N:ℝ))^4) *
        (Real.exp (tailCost T*(|((t:ℝ)-p*h)/Real.sqrt (p*h)| *Real.log (N:ℝ)+
          (Real.log (N:ℝ))^2+Real.log (N:ℝ)+1)) *
          Real.exp (-(((t:ℝ)-p*h)/Real.sqrt (p*h))^2/(32*T))) :=
      mul_le_mul_of_nonneg_left hf (Real.exp_pos _).le
    _ ≤ _ := by
      rw [← mul_assoc]
      exact h₂ N ((le_max_right _ _).trans hN) _ hτ

end MajorityDynamics.Probability.HypergeometricTiltTail
