import MajorityDynamics.Probability.HypergeometricTiltTail.Main
import MajorityDynamics.Probability.HypergeometricTiltTail.MeanSparse
import MajorityDynamics.Probability.HypergeometricTiltTail.SparseNumerics

/-! Closed tilted hypergeometric tail on the whole sparse range. -/
noncomputable section
open scoped BigOperators
namespace MajorityDynamics.Probability.HypergeometricTiltTail
open FixedSizeExponential

theorem hypergeomMass_regime_tail_sparse {N M H : ℕ} {p T h : ℝ} {d t : ℤ}
    (hT : 1 < T) (r : Numerics.SparseRegime N p T)
    (hMlo : (N : ℝ)-1 ≤ M) (hMhi : (M : ℝ) ≤ N) (hHM : H ≤ M)
    (hhlo : (N : ℝ)/T ≤ h) (hhhi : h ≤ N-(N : ℝ)/T)
    (hH : |(H : ℝ)-h| ≤ 1)
    (hd : |(d : ℝ)-p*N| ≤ Real.sqrt (p*N)*Real.log (N : ℝ))
    (ht0 : 0 ≤ t) (htd : t ≤ d)
    (htau : (Real.log (N : ℝ))^100 ≤ |((t : ℝ)-p*h)/Real.sqrt (p*h)|) :
    hypergeomMass M H d.toNat t.toNat ≤
      (1+1/centralAtomConstant)*(N : ℝ) *
        Real.exp (-(((t : ℝ)-p*h)/Real.sqrt (p*h))^2/(32*T)) := by
  obtain ⟨hN0,_,_,hH0,_,_,hd0,hdM,hdhi⟩ :=
    Numerics.basic_bounds_sparse (L := h) hT r hMlo hMhi hhlo hhhi hH hhlo hd
  have hM0 : 0 < (M : ℝ) := hd0.trans hdM
  have hHnat : 0 < H := by exact_mod_cast hH0
  have hdInt0 : 0 < d := by exact_mod_cast hd0
  have hdcast : (d.toNat : ℝ) = d := by exact_mod_cast Int.toNat_of_nonneg hdInt0.le
  have htcast : (t.toNat : ℝ) = t := by exact_mod_cast Int.toNat_of_nonneg ht0
  have hdNat0 : 0 < d.toNat := by exact_mod_cast (show 0 < (d.toNat : ℝ) by simpa [hdcast] using hd0)
  have hdNatM : d.toNat < M := by exact_mod_cast (show (d.toNat : ℝ) < M by simpa [hdcast] using hdM)
  have htNatd : t.toNat ≤ d.toNat := Int.toNat_le_toNat htd
  have hHMreal : (H : ℝ) ≤ M := by exact_mod_cast hHM
  have hμ := Numerics.hypergeometric_bounds (x := p*N)
    (mul_pos r.p_pos hN0) hM0 hH0 hHMreal hd0 (by simpa [mul_assoc] using hdhi)
    (show 0 ≤ (t : ℝ) by exact_mod_cast ht0)
    (show (t : ℝ) ≤ d by exact_mod_cast htd)
  have hdev := Numerics.deviation_conversion_sparse hT r hN0 hM0 hMlo hMhi hH0.le
    hHMreal hhlo hH hd htau
  have hexp := Numerics.tail_exponent (x := p*N)
    (τ := ((t : ℝ)-p*h)/Real.sqrt (p*h)) hT (mul_pos r.p_pos hN0)
    rfl r.p_pos hN0 hhlo (abs_nonneg _) hμ.1 hμ.2.1 hμ.2.2 hdev
  have hbound := hypergeomMass_chernoff hHM hdNat0 hdNatM htNatd hHnat
  rw [hdcast,htcast] at hbound
  have hcent : (H : ℝ)*((d : ℝ)/M) = ((d : ℝ)/M)*H := mul_comm _ _
  rw [hcent] at hbound
  have he : Real.exp (-|(t : ℝ)-((d : ℝ)/M)*H|^2 /
      (2*(((d : ℝ)/M)*H)+2*|(t : ℝ)-((d : ℝ)/M)*H|/3)) ≤
      Real.exp (-(((t : ℝ)-p*h)/Real.sqrt (p*h))^2/(32*T)) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_div] using neg_le_neg hexp
  have hN1 : 1 ≤ (N : ℝ) := by linarith [r.N_large]
  have hdsqrt : Real.sqrt (d : ℝ) ≤ N := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · exact hN0.le
    · have hdn : (d : ℝ) ≤ N := hdM.le.trans hMhi
      nlinarith
  have hpref : Real.sqrt (d : ℝ)/centralAtomConstant ≤
      (1+1/centralAtomConstant)*(N : ℝ) := by
    have hc := centralAtomConstant_pos
    have hs := div_le_div_of_nonneg_right hdsqrt hc.le
    have heq : (N : ℝ)/centralAtomConstant = (1/centralAtomConstant)*(N : ℝ) := by ring
    rw [heq] at hs
    nlinarith
  have hc := centralAtomConstant_pos
  exact hbound.trans (mul_le_mul hpref he (Real.exp_pos _).le (by positivity))

theorem tiltExpectation_regime_sparse {V : Type*} [DecidableEq V]
    {N : ℕ} {T p h L : ℝ} (hT : 1 < T) (r : Numerics.SparseRegime N p T)
    {P S : Finset V} (hSP : S ⊆ P)
    (hMlo : (N:ℝ)-1 ≤ P.card) (hMhi : (P.card:ℝ) ≤ N)
    (hhlo : (N:ℝ)/T ≤ h) (hhhi : h ≤ N-(N:ℝ)/T)
    (hHh : |(S.card:ℝ)-h| ≤ 1) (hL : (N:ℝ)/T ≤ L)
    (β : V → ℝ) (hβ : ∀ v ∈ P, |β v| ≤ Real.log (N:ℝ))
    {d t : ℤ} (hd : |(d:ℝ)-p*N| ≤ Real.sqrt (p*N)*Real.log (N:ℝ))
    (ht : 0 ≤ t) (htd : t ≤ d) :
    tiltExpectation P S t.toNat (d-t).toNat p L β ≤
      ((1+1/centralAtomConstant)*(N:ℝ))^2 *
        Real.exp (28*T*(|((t:ℝ)-p*h)/Real.sqrt (p*h)| *Real.log (N:ℝ)+
          (Real.log (N:ℝ))^2)) := by
  obtain ⟨hN,hHs,hCs,hH,hHM,hL0,hd0,hdM,hdhi⟩ :=
    Numerics.basic_bounds_sparse hT r hMlo hMhi hhlo hhhi hHh hL hd
  have hT0 : 0 < T := by linarith
  have hN1 : 1 ≤ (N:ℝ) := by linarith [r.N_large]
  have hlog : 0 ≤ Real.log (N:ℝ) := by linarith [r.log_large]
  have hp1 : p ≤ 1 := by linarith [r.p_small]
  have hc := centralAtomConstant_pos
  have hl : 0 ≤ d-t := sub_nonneg.mpr htd
  have htcast : (t.toNat:ℝ) = (t:ℝ) := by exact_mod_cast Int.toNat_of_nonneg ht
  have hlcast : ((d-t).toNat:ℝ) = (d:ℝ)-(t:ℝ) := by
    have hh : ((d-t).toNat:ℤ) = d-t := Int.toNat_of_nonneg hl
    exact_mod_cast hh
  have hccard : ((P \ S).card:ℝ) = (P.card:ℝ)-(S.card:ℝ) := by
    rw [Finset.card_sdiff_of_subset hSP, Nat.cast_sub (Finset.card_le_card hSP)]
  have hdrawS := Numerics.draw_below_child_sparse hT r hHs hdhi
  have hdrawC := Numerics.draw_below_child_sparse hT r hCs hdhi
  have hk : t.toNat < S.card := by
    have : (t.toNat:ℝ) < S.card := by
      rw [htcast]
      have hh : (t:ℝ) ≤ d := by exact_mod_cast htd
      exact hh.trans_lt hdrawS
    exact_mod_cast this
  have hk' : (d-t).toNat < (P \ S).card := by
    have : ((d-t).toNat:ℝ) < ((P \ S).card:ℝ) := by
      rw [hlcast,hccard]
      have ht' : (0:ℝ) ≤ t := by exact_mod_cast ht
      linarith
    exact_mod_cast this
  have hkl : (t.toNat:ℝ)+(d-t).toNat ≤ 2*p*N := by rw [htcast,hlcast]; linarith
  have ha : ∀ v ∈ P, |tiltCoefficient p L β v| ≤ 1 := by
    intro v hv
    unfold tiltCoefficient
    rw [abs_div,abs_mul,abs_of_pos (by linarith [r.p_pos] : 0 < 1+p),
      abs_of_pos (Real.sqrt_pos.mpr (mul_pos r.p_pos hL0))]
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hβ v hv) (by linarith [r.p_pos]))
      (Real.sqrt_nonneg _)).trans (Numerics.coefficient_bound_sparse hT r hL)
  have hmgf := tiltExpectation_beta_mgf hSP hk hk' r.p_pos hp1 hL0 hT0 hL hlog hkl β hβ ha
  have hMN : |(P.card:ℝ)-(N:ℝ)| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hh0 : 0 < h := (div_pos hN hT0).trans_le hhlo
  have hhN : h ≤ (N:ℝ) := by have := div_pos hN hT0; linarith
  have hb1 := sum_beta_bound S β (fun v hv => hβ v (hSP hv))
  have hb2 := sum_beta_bound (P \ S) β (fun v hv => hβ v (Finset.sdiff_subset hv))
  rw [hccard] at hb2
  have hmean := pair_tilt_mean_bound_normalized (t := (t:ℝ)) hT.le hN r.p_pos hp1 r.normalized_density
    (by linarith [r.degree_large]) r.log_large hMN hHh hh0 hhN hH (by linarith)
    hL (by exact_mod_cast ht) (by exact_mod_cast htd) hdhi hd hb1 hb2
  have hmean' :
      (t.toNat:ℝ)/S.card*(∑ v ∈ S, tiltCoefficient p L β v)+
        ((d-t).toNat:ℝ)/(P \ S).card*(∑ v ∈ P \ S, tiltCoefficient p L β v)-
        tiltConstant P p L β ≤
      20*T*(|((t:ℝ)-p*h)/Real.sqrt (p*h)| *Real.log (N:ℝ)+(Real.log (N:ℝ))^2) := by
    rw [pair_mean_eq hSP r.p_pos hL0 β,htcast,hlcast,hccard]
    exact hmean
  have hexp : Real.exp
      ((t.toNat:ℝ)/S.card*(∑ v ∈ S, tiltCoefficient p L β v)+
        ((d-t).toNat:ℝ)/(P \ S).card*(∑ v ∈ P \ S, tiltCoefficient p L β v)-
        tiltConstant P p L β +8*T*(Real.log (N:ℝ))^2) ≤
      Real.exp (28*T*(|((t:ℝ)-p*h)/Real.sqrt (p*h)| *Real.log (N:ℝ)+(Real.log (N:ℝ))^2)) := by
    apply Real.exp_le_exp.mpr
    have hz : 0 ≤ |((t:ℝ)-p*h)/Real.sqrt (p*h)| *Real.log (N:ℝ) := by positivity
    nlinarith
  have htN : (t.toNat:ℝ) ≤ (N:ℝ) := by
    rw [htcast]
    have hh : (t:ℝ) ≤ d := by exact_mod_cast htd
    linarith
  have hlN : ((d-t).toNat:ℝ) ≤ (N:ℝ) := by
    rw [hlcast]
    have hh : (0:ℝ) ≤ t := by exact_mod_cast ht
    linarith
  have hpref := mul_le_mul (mgfPrefactor_le hN1 htN) (mgfPrefactor_le hN1 hlN)
    (mgfPrefactor_pos _).le (by positivity : 0 ≤ (1+1/centralAtomConstant)*(N:ℝ))
  calc
    _ ≤ _ := hmgf
    _ ≤ _ := mul_le_mul hpref hexp (Real.exp_pos _).le
      (mul_nonneg (by positivity) (by positivity))
    _ = _ := by ring

theorem factor_regime_sparse {V : Type*} [DecidableEq V]
    {N : ℕ} {T p h L : ℝ} (hT : 1 < T) (r : Numerics.SparseRegime N p T)
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
  have hg := hypergeomMass_regime_tail_sparse hT r hMlo hMhi
    (Finset.card_le_card hSP) hhlo hhhi hHh hd ht htd hτ
  have he := tiltExpectation_regime_sparse hT r hSP hMlo hMhi hhlo hhhi hHh hL β hβ hd ht htd
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
theorem uniform_factor_sparse {θ T B : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hB : 0 ≤ B) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-(1/2 : ℝ)) →
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
  obtain ⟨N₁,h₁⟩ := Numerics.uniform_regime_sparse hθlo hθhi hT
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
  have hf := factor_regime_sparse hT r hSP hMlo hMhi hhlo hhhi hHh hL β hβ hd ht htd hτ
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

