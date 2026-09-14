import MajorityDynamics.Probability.HypergeometricTiltTail.TiltMGF
import MajorityDynamics.Probability.HypergeometricTiltTail.MeanBounds
import MajorityDynamics.Probability.HypergeometricTiltTail.NumericData

noncomputable section
open scoped BigOperators
namespace MajorityDynamics.Probability.HypergeometricTiltTail
open FixedSizeExponential

theorem sum_beta_bound {V : Type*} (A : Finset V) {g : ℝ} (β : V → ℝ)
    (hβ : ∀ v ∈ A, |β v| ≤ g) : |∑ v ∈ A, β v| ≤ (A.card : ℝ)*g := by
  calc
    _ ≤ ∑ v ∈ A, |β v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v ∈ A, g := Finset.sum_le_sum hβ
    _ = _ := by simp

/-- The actual two-subset exponential moment from original finite data and a
uniform numerical regime. Neither draw size needs a positive lower bound. -/
theorem tiltExpectation_regime {V : Type*} [DecidableEq V]
    {N : ℕ} {T p h L : ℝ} (hT : 1 < T) (r : Numerics.Regime N p T)
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
    Numerics.basic_bounds hT r hMlo hMhi hhlo hhhi hHh hL hd
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
  have hdrawS := Numerics.draw_below_child hT r hHs hdhi
  have hdrawC := Numerics.draw_below_child hT r hCs hdhi
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
      (Real.sqrt_nonneg _)).trans (Numerics.coefficient_bound hT r hL)
  have hmgf := tiltExpectation_beta_mgf hSP hk hk' r.p_pos hp1 hL0 hT0 hL hlog hkl β hβ ha
  have hMN : |(P.card:ℝ)-(N:ℝ)| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hh0 : 0 < h := (div_pos hN hT0).trans_le hhlo
  have hhN : h ≤ (N:ℝ) := by have := div_pos hN hT0; linarith
  have hb1 := sum_beta_bound S β (fun v hv => hβ v (hSP hv))
  have hb2 := sum_beta_bound (P \ S) β (fun v hv => hβ v (Finset.sdiff_subset hv))
  rw [hccard] at hb2
  have hmean := pair_tilt_mean_bound (t := (t:ℝ)) hT.le hN r.p_pos hp1 r.square_density
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

end MajorityDynamics.Probability.HypergeometricTiltTail
