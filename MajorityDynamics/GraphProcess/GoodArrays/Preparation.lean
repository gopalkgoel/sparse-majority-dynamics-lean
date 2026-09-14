import MajorityDynamics.GraphProcess.GoodArrays.Basic
import MajorityDynamics.GraphProcess.EnumerationBounds.Numerics
import MajorityDynamics.GraphProcess.EnumerationBounds.Asymptotics

noncomputable section
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.GoodArrays
open Universal
variable {V : Type*} [Fintype V] {n : ℕ}

theorem window_le_sqrt (n : ℕ) {T p : ℝ} (hT : 1 < T) (N : ℕ) :
    window n T p N ≤ Real.sqrt (p*N) := by
  have hh : (1 : ℝ) ≤ labelCount n := by exact_mod_cast labelCount_pos n
  have hden : 1 ≤ 100*T*(labelCount n : ℝ) := by nlinarith
  unfold window
  exact div_le_self (Real.sqrt_nonneg _) hden

theorem finite_regime (y : Local.CoarseData V n) {T p : ℝ} (hT : 1 < T)
    (hN : 2*T ≤ (Fintype.card V : ℝ)) (hp : 0 < p)
    (hsmall : p ≤ 1/(8*T^2))
    (hcountScale : 4*T^6 ≤ p*Fintype.card V)
    (hradius : (200*T*(labelCount n : ℝ))^2 ≤ p*Fintype.card V)
    (hroot : (2*T^2)^2 ≤ p*Fintype.card V)
    (hreg : (T^2+1)*Real.sqrt (p*Fintype.card V) ≤
      (p*Fintype.card V)^(4/7:ℝ))
    (hsizes : ∀ s, (Fintype.card V : ℝ)/T ≤ (y.sizes s : ℝ))
    (hcounts : ∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
      T*(Fintype.card V : ℝ)^2*p/Real.sqrt (p*Fintype.card V)) :
    Regime y T p := by
  have hT0 : 0 < T := by linarith
  have hT2 : 1 ≤ T^2 := by nlinarith
  have hN0 : 0 < (Fintype.card V : ℝ) := by linarith
  have hx0 : 0 < p*Fintype.card V := mul_pos hp hN0
  have hs0 := Real.sqrt_nonneg (p*Fintype.card V)
  have hs2 := Real.sq_sqrt hx0.le
  have hroot' : 2*T^2 ≤ Real.sqrt (p*Fintype.card V) := by
    nlinarith [sq_nonneg (Real.sqrt (p*Fintype.card V)-2*T^2)]
  have hrootMean : Real.sqrt (p*Fintype.card V) ≤ p*Fintype.card V/(2*T^2) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*T^2)).mpr
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hroot')]
  have hsizePos (s) : 0 < (y.sizes s : ℝ) := (div_pos hN0 hT0).trans_le (hsizes s)
  have hsizeUpper (s) : (y.sizes s : ℝ) ≤ Fintype.card V := by
    exact_mod_cast y.sizes_le_card s
  have he (s t) := EnumerationBounds.pair_estimates hN0 hT hp hcountScale
    (hsizes s) (hsizes t) (hsizeUpper s) (hsizeUpper t) (hcounts s t)
  have hpx : p*(8*T^2) ≤ 1 := (le_div_iff₀ (by positivity : 0 < 8*T^2)).mp hsmall
  have hp1 : p ≤ 1 := by nlinarith
  have hmeanUpper : p*Fintype.card V ≤ (Fintype.card V : ℝ)/(8*T^2) :=
    by simpa only [one_div_mul_eq_div] using mul_le_mul_of_nonneg_right hsmall hN0.le
  have hrootN : Real.sqrt (p*Fintype.card V) ≤ (Fintype.card V : ℝ)/(4*T) := by
    have hrootMean' : Real.sqrt (p*Fintype.card V) ≤ p*Fintype.card V := by
      exact hrootMean.trans (div_le_self hx0.le (by nlinarith))
    apply hrootMean'.trans
    apply hmeanUpper.trans
    apply div_le_div_of_nonneg_left hN0.le (by positivity : 0 < 4*T)
    nlinarith
  refine ⟨hN0, hp, hsizePos, ?_, ?_, ?_, ?_, ?_, hreg⟩
  · intro s t
    exact (he s t).2.2.1
  · intro s t
    exact (window_le_sqrt n hT _).trans (hrootMean.trans (he s t).1)
  · intro s t
    have havg : EnumerationBounds.avg y s t ≤ (Fintype.card V : ℝ)/(4*T) := by
      apply (he s t).2.1.trans
      apply (le_div_iff₀ (by positivity : 0 < 4*T)).mpr
      have hh := mul_le_mul_of_nonneg_right hpx hN0.le
      nlinarith [hh]
    have hw := (window_le_sqrt n hT (Fintype.card V)).trans hrootN
    have ht := EnumerationBounds.size_estimates hT hN (hsizes t)
    calc
      _ ≤ (Fintype.card V : ℝ)/(4*T) + (Fintype.card V : ℝ)/(4*T) := add_le_add havg hw
      _ = (Fintype.card V : ℝ)/(2*T) := by ring
      _ ≤ _ := ht.2
  · have hh : (0 : ℝ) < labelCount n := by exact_mod_cast labelCount_pos n
    have hden : 0 < 200*T*(labelCount n : ℝ) := by positivity
    have hsden : 200*T*(labelCount n : ℝ) ≤ Real.sqrt (p*Fintype.card V) := by
      nlinarith [sq_nonneg (Real.sqrt (p*Fintype.card V)-200*T*(labelCount n : ℝ))]
    have hc : 1 ≤ radiusCoefficient n T * Real.sqrt (p*Fintype.card V) := by
      unfold radiusCoefficient
      rw [one_div_mul_eq_div]
      exact (le_div_iff₀ hden).mpr (by simpa using hsden)
    have hw : window n T p (Fintype.card V) =
        2*(radiusCoefficient n T * Real.sqrt (p*Fintype.card V)) := by
      unfold window radiusCoefficient
      ring
    rw [hw]
    linarith
  · intro s
    have hs := (div_le_iff₀ hT0).mp (hsizes s)
    have hrootN' : Real.sqrt (p*Fintype.card V) ≤ (Fintype.card V : ℝ) :=
      hrootN.trans (div_le_self hN0.le (by linarith))
    nlinarith

universe u

/-- All finite construction and membership margins follow from the three
original numerical hypotheses; no degree array or regularity is assumed. -/
theorem uniform_regime {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ y : Local.CoarseData V n,
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) → Regime y T p := by
  obtain ⟨X, hX, hpow⟩ := EnumerationBounds.eventually_mul_rpow_le
    (a := (1:ℝ)/2) (b := (4:ℝ)/7) (A := T^2+1) (B := 1)
    (by norm_num) zero_lt_one
  let L := max X (max (4*T^6) (max ((200*T*(labelCount n : ℝ))^2) ((2*T^2)^2)))
  have hL : 0 < L := hX.trans_le (le_max_left _ _)
  obtain ⟨N₀, hN₀⟩ := EnumerationBounds.eventually_window hθlo hθhi hT hL
    (U := 1/(8*T^2)) (by positivity) (M := 2*T) (by linarith)
  refine ⟨N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi y hsizes hcounts
  have hw := hN₀ N hN p hlo hhi
  have hLX : X ≤ L := le_max_left _ _
  have hLC : 4*T^6 ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hLR : (200*T*(labelCount n : ℝ))^2 ≤ L :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hLS : (2*T^2)^2 ≤ L :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  subst N
  apply finite_regime y hT hw.2.2.1 hw.2.1 hw.2.2.2.2
    (hLC.trans hw.2.2.2.1) (hLR.trans hw.2.2.2.1) (hLS.trans hw.2.2.2.1)
    _ hsizes hcounts
  simpa [Real.sqrt_eq_rpow] using hpow (p*Fintype.card V) (hLX.trans hw.2.2.2.1)

end MajorityDynamics.GraphProcess.GoodArrays
