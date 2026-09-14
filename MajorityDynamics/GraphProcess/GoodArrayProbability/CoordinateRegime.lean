import MajorityDynamics.GraphProcess.GoodArrays.Preparation

noncomputable section
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.GoodArrayProbability
open Universal

def coordinateConstant (T : ℝ) : ℝ := 4*T*(T^2+T+2)

theorem coordinateConstant_pos {T : ℝ} (hT : 1 < T) :
    0 < coordinateConstant T := by
  unfold coordinateConstant
  positivity

variable {V : Type*} [Fintype V] {n : ℕ}

set_option maxHeartbeats 800000 in
theorem finite_coordinate_regime (y : Local.CoarseData V n) (q : Local.Tilt n)
    {T p L : ℝ} (hT : 1 < T) (_hL : 1 ≤ L)
    (hreg : GoodArrays.Regime y T p)
    (hN : 2*T ≤ (Fintype.card V : ℝ)) (hp : p ≤ 1/4)
    (hscale : 4*T*L ≤ p*Fintype.card V)
    (hroot : (2*T)^2 ≤ p*Fintype.card V)
    (hsizes : ∀ s, (Fintype.card V : ℝ)/T ≤ (y.sizes s : ℝ))
    (htilt : ∀ s t, |(q s t : ℝ)-p| ≤ T*p/Real.sqrt (p*Fintype.card V))
    (d : RowArray.Ambient y.part) (hd : d ∈ GoodArrays.E0 y T p)
    (v : V) (t : History (n+1)) :
    (q (y.part v) t : ℝ) ≤ 1/2 ∧
    L ≤ (Local.trials y.sizes (y.part v) t : ℝ)*(q (y.part v) t : ℝ) ∧
    (Local.trials y.sizes (y.part v) t : ℝ)*(q (y.part v) t : ℝ) ≤
      2*p*Fintype.card V ∧
    |(RowArray.naturalRows d v t : ℝ) -
      (Local.trials y.sizes (y.part v) t : ℝ)*(q (y.part v) t : ℝ)| ≤
      coordinateConstant T * Real.sqrt
        ((Local.trials y.sizes (y.part v) t : ℝ)*(q (y.part v) t : ℝ)) := by
  let N : ℝ := Fintype.card V
  let x : ℝ := p*N
  let m : ℝ := Local.trials y.sizes (y.part v) t
  let r : ℝ := q (y.part v) t
  have hT0 : 0 < T := by linarith
  have hp0 := hreg.density_pos
  have hN0 : 0 < N := hreg.card_pos
  have hx0 : 0 < x := mul_pos hp0 hN0
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hs2 := Real.sq_sqrt hx0.le
  have hsr : 2*T ≤ Real.sqrt x := by
    dsimp [x, N] at *
    nlinarith [sq_nonneg (Real.sqrt (p*Fintype.card V)-2*T)]
  have htilt' : |r-p| ≤ p/2 := by
    apply (htilt (y.part v) t).trans
    apply (div_le_iff₀ hs0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsr hp0.le]
  have hrlo : p/2 ≤ r := by linarith [(abs_le.mp htilt').1]
  have hrup : r ≤ 2*p := by linarith [(abs_le.mp htilt').2]
  have hr0 : 0 < r := (half_pos hp0).trans_le hrlo
  have hsize : 2 ≤ (y.sizes t : ℝ) ∧ N/(2*T) ≤ (y.sizes t : ℝ)-1 :=
    EnumerationBounds.size_estimates hT hN (hsizes t)
  have hmcast : m = (y.sizes t : ℝ) - if y.part v = t then 1 else 0 := by
    have hnat : 1 ≤ y.sizes t := by exact_mod_cast (show (1:ℝ) ≤ y.sizes t by linarith [hsize.1])
    dsimp [m, Local.trials]
    split_ifs <;> simp [Nat.cast_sub hnat]
  have hmlo : N/(2*T) ≤ m := by
    rw [hmcast]
    split_ifs <;> linarith [hsize.2]
  have hmup : m ≤ N := by
    have hh : (y.sizes t : ℝ) ≤ N := by
      dsimp [N]
      exact_mod_cast y.sizes_le_card t
    rw [hmcast]
    split_ifs <;> linarith
  have hm0 : 0 ≤ m := by dsimp [m]; positivity
  have hmeanlo : x/(4*T) ≤ m*r := by
    have hh := mul_le_mul hmlo hrlo (by positivity : 0 ≤ p/2) hm0
    calc
      x/(4*T) = N/(2*T)*(p/2) := by dsimp [x]; ring
      _ ≤ m*r := hh
  have hmeanup : m*r ≤ 2*p*N := by
    have hh := mul_le_mul hmup hrup hr0.le hN0.le
    nlinarith
  have hmeanL : L ≤ m*r := by
    apply le_trans _ hmeanlo
    apply (le_div_iff₀ (by positivity : 0 < 4*T)).mpr
    dsimp [x, N]
    nlinarith [hscale]
  have havg := hreg.center (y.part v) t
  have hgood : |(RowArray.naturalRows d v t : ℝ) -
      EnumerationBounds.avg y (y.part v) t| ≤ Real.sqrt x := by
    have hh := (GoodArrays.mem_E0 y T p d).mp hd |>.2 (y.part v) t v (by simp)
    exact hh.trans (GoodArrays.window_le_sqrt n hT _)
  have htiltSize : |p*(y.sizes t : ℝ)-m*r| ≤ (T+1)*Real.sqrt x := by
    have htrial : |p*(y.sizes t : ℝ)-m*p| ≤ p := by
      rw [hmcast]
      split_ifs
      · rw [show p*(y.sizes t : ℝ)-((y.sizes t : ℝ)-1)*p = p by ring, abs_of_pos hp0]
      · rw [show p*(y.sizes t : ℝ)-((y.sizes t : ℝ)-0)*p = 0 by ring, abs_zero]
        exact hp0.le
    have hshift : |m*p-m*r| ≤ T*Real.sqrt x := by
      rw [← mul_sub, abs_mul, abs_of_nonneg hm0, abs_sub_comm]
      calc
        m*|r-p| ≤ m*(T*p/Real.sqrt x) :=
          mul_le_mul_of_nonneg_left (htilt (y.part v) t) hm0
        _ ≤ N*(T*p/Real.sqrt x) := mul_le_mul_of_nonneg_right hmup (by positivity)
        _ = T*Real.sqrt x := by
          rw [← mul_div_assoc]
          apply (div_eq_iff hs0.ne').mpr
          calc
            N*(T*p) = T*x := by dsimp [x]; ring
            _ = T*(Real.sqrt x)^2 := congrArg (fun z => T*z) hs2.symm
            _ = T*Real.sqrt x*Real.sqrt x := by ring
    have hpS : p ≤ Real.sqrt x := by linarith
    calc
      |p*(y.sizes t : ℝ)-m*r| ≤ |p*(y.sizes t : ℝ)-m*p|+|m*p-m*r| :=
        abs_sub_le _ _ _
      _ ≤ p+T*Real.sqrt x := add_le_add htrial hshift
      _ ≤ (T+1)*Real.sqrt x := by nlinarith
  have hdev : |(RowArray.naturalRows d v t : ℝ)-m*r| ≤
      (T^2+T+2)*Real.sqrt x := by
    have htri := abs_sub_le (RowArray.naturalRows d v t : ℝ)
      (EnumerationBounds.avg y (y.part v) t) (m*r)
    have htri' := abs_sub_le (EnumerationBounds.avg y (y.part v) t)
      (p*(y.sizes t : ℝ)) (m*r)
    nlinarith [hgood, havg, htiltSize]
  have hmu0 : 0 ≤ m*r := mul_nonneg hm0 hr0.le
  have hmusq := Real.sq_sqrt hmu0
  have hxmu : x ≤ 4*T*(m*r) := by
    have hh := (div_le_iff₀ (by positivity : 0 < 4*T)).mp hmeanlo
    nlinarith only [hh]
  have hsqrt : Real.sqrt x ≤ 4*T*Real.sqrt (m*r) := by
    have hprod := mul_nonneg hmu0 (show 0 ≤ (4*T)^2-4*T by nlinarith)
    have hsp := Real.sqrt_nonneg (m*r)
    have hb : 0 ≤ 4*T*Real.sqrt (m*r) := by positivity
    nlinarith only [hxmu, hprod, hs2, hmusq, hs0.le, hb,
      sq_nonneg (Real.sqrt x-4*T*Real.sqrt (m*r))]
  refine ⟨by change r ≤ 1/2; linarith, hmeanL, hmeanup, ?_⟩
  apply hdev.trans
  have hh := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ T^2+T+2 by positivity)
  convert hh using 1
  unfold coordinateConstant
  ring

universe u

theorem uniform_coordinate_regime {θ T L : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hL : 1 ≤ L) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
      (∀ s t, |(q s t : ℝ)-p| ≤ T*p/Real.sqrt (p*N)) →
      ∀ d : RowArray.Ambient y.part, d ∈ GoodArrays.E0 y T p →
      ∀ v t,
      (q (y.part v) t : ℝ) ≤ 1/2 ∧
      L ≤ (Local.trials y.sizes (y.part v) t : ℝ)*(q (y.part v) t : ℝ) ∧
      (Local.trials y.sizes (y.part v) t : ℝ)*(q (y.part v) t : ℝ) ≤ 2*p*N ∧
      |(RowArray.naturalRows d v t : ℝ)-
        (Local.trials y.sizes (y.part v) t : ℝ)*(q (y.part v) t : ℝ)| ≤
        coordinateConstant T * Real.sqrt
          ((Local.trials y.sizes (y.part v) t : ℝ)*(q (y.part v) t : ℝ)) := by
  obtain ⟨N₁, h₁⟩ := GoodArrays.uniform_regime n hθlo hθhi hT
  let X := max (4*T*L) ((2*T)^2)
  have hX : 0 < X := lt_of_lt_of_le (by positivity : 0 < (2*T)^2) (le_max_right _ _)
  obtain ⟨N₂, h₂⟩ := EnumerationBounds.eventually_window hθlo hθhi hT hX
    (U := 1/4) (by norm_num) (M := 2*T) (by linarith)
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN V inst hcard p hlo hhi y q hsizes hcounts htilt d hd v t
  have hg := h₁ N ((le_max_left _ _).trans hN) V hcard p hlo hhi y hsizes hcounts
  have hw := h₂ N ((le_max_right _ _).trans hN) p hlo hhi
  subst N
  exact finite_coordinate_regime y q hT hL hg hw.2.2.1 hw.2.2.2.2
    ((le_max_left _ _).trans hw.2.2.2.1) ((le_max_right _ _).trans hw.2.2.2.1)
    hsizes htilt d hd v t

end MajorityDynamics.GraphProcess.GoodArrayProbability
