import MajorityDynamics.GraphProcess.RowConcentration.Asymptotics
import MajorityDynamics.GraphProcess.EnumerationBounds.Numerics
import MajorityDynamics.GraphProcess.RowArray.Main

noncomputable section
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.RowConcentration
open Universal

variable {V : Type*} [Fintype V] {n : ℕ}

/-- Coordinate mean bounds use only sizes and tilts, never the coarse edge counts. -/
theorem finite_mean_bounds (y : Local.CoarseData V n) (q : Local.Tilt n)
    {T p : ℝ} (hT : 1 < T) (hp : 0 < p) (hp1 : p ≤ 1)
    (hN : 2*T ≤ (Fintype.card V : ℝ))
    (hroot : (2*T)^2 ≤ p*Fintype.card V)
    (hsizes : ∀ s, (Fintype.card V : ℝ)/T ≤ (y.sizes s : ℝ))
    (htilt : ∀ s t, |(q s t : ℝ)-p| ≤ T*p/Real.sqrt (p*Fintype.card V))
    (s t : History (n+1)) :
    (Local.trials y.sizes s t : ℝ)*(q s t : ℝ) ≤ 2*p*Fintype.card V ∧
    |p*(y.sizes t : ℝ)-(Local.trials y.sizes s t : ℝ)*(q s t : ℝ)| ≤
      (T+1)*Real.sqrt (p*Fintype.card V) := by
  let N : ℝ := Fintype.card V
  let x : ℝ := p*N
  let m : ℝ := Local.trials y.sizes s t
  let r : ℝ := q s t
  have hT0 : 0 < T := by linarith
  have hN0 : 0 < N := by dsimp [N]; linarith
  have hx0 : 0 < x := mul_pos hp hN0
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hs2 := Real.sq_sqrt hx0.le
  have hsr : 2*T ≤ Real.sqrt x := by
    dsimp [x,N] at *
    nlinarith [sq_nonneg (Real.sqrt (p*Fintype.card V)-2*T)]
  have htilt' : |r-p| ≤ p/2 := by
    apply (htilt s t).trans
    apply (div_le_iff₀ hs0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsr hp.le]
  have hrup : r ≤ 2*p := by linarith [(abs_le.mp htilt').2]
  have hr0 : 0 ≤ r := (q s t).2.1.le
  have hsize := EnumerationBounds.size_estimates hT hN (hsizes t)
  have hmcast : m = (y.sizes t : ℝ) - if s = t then 1 else 0 := by
    have hnat : 1 ≤ y.sizes t := by exact_mod_cast (show (1:ℝ) ≤ y.sizes t by linarith [hsize.1])
    dsimp [m, Local.trials]
    split_ifs <;> simp [Nat.cast_sub hnat]
  have hmup : m ≤ N := by
    have hh : (y.sizes t : ℝ) ≤ N := by
      dsimp [N]
      exact_mod_cast y.sizes_le_card t
    rw [hmcast]
    split_ifs <;> linarith
  have hm0 : 0 ≤ m := by dsimp [m]; positivity
  have hmeanup : m*r ≤ 2*p*N := by
    have hh := mul_le_mul hmup hrup hr0 hN0.le
    nlinarith
  have htrial : |p*(y.sizes t : ℝ)-m*p| ≤ p := by
    rw [hmcast]
    split_ifs
    · rw [show p*(y.sizes t : ℝ)-((y.sizes t : ℝ)-1)*p = p by ring, abs_of_pos hp]
    · rw [show p*(y.sizes t : ℝ)-((y.sizes t : ℝ)-0)*p = 0 by ring, abs_zero]
      exact hp.le
  have hshift : |m*p-m*r| ≤ T*Real.sqrt x := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hm0, abs_sub_comm]
    calc
      m*|r-p| ≤ m*(T*p/Real.sqrt x) := mul_le_mul_of_nonneg_left (htilt s t) hm0
      _ ≤ N*(T*p/Real.sqrt x) := mul_le_mul_of_nonneg_right hmup (by positivity)
      _ = T*Real.sqrt x := by
        rw [← mul_div_assoc]
        apply (div_eq_iff hs0.ne').mpr
        calc
          N*(T*p) = T*x := by dsimp [x]; ring
          _ = T*(Real.sqrt x)^2 := congrArg (fun z => T*z) hs2.symm
          _ = T*Real.sqrt x*Real.sqrt x := by ring
  have hpS : p ≤ Real.sqrt x := by linarith
  refine ⟨hmeanup, ?_⟩
  calc
    |p*(y.sizes t : ℝ)-m*r| ≤ |p*(y.sizes t : ℝ)-m*p|+|m*p-m*r| := abs_sub_le _ _ _
    _ ≤ p+T*Real.sqrt x := add_le_add htrial hshift
    _ ≤ (T+1)*Real.sqrt x := by nlinarith

universe u
/-- A uniform scalar regime for the original row model, independent of edge counts. -/
theorem uniform_degree_regime {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(q s t : ℝ)-p| ≤ T*p/Real.sqrt (p*N)) →
      0 < (N : ℝ) ∧ 0 < p ∧ 1 ≤ Real.log (N : ℝ) ∧
      Real.sqrt (p*N)*(Real.log (N : ℝ))^((2:ℝ)/3) ≤ p*N ∧
      (∀ s t, (Local.trials y.sizes s t : ℝ)*(q s t : ℝ) ≤ 2*p*N ∧
        |p*(y.sizes t : ℝ)-(Local.trials y.sizes s t : ℝ)*(q s t : ℝ)| ≤
          Real.sqrt (p*N)*(Real.log (N : ℝ))^((2:ℝ)/3)/2) := by
  obtain ⟨N₁,h₁⟩ := eventually_tolerance_le hθlo hθhi hT
  obtain ⟨N₂,h₂⟩ := EnumerationBounds.eventually_window hθlo hθhi hT
    (L := (2*T)^2) (by positivity) (U := 1) zero_lt_one (M := 2*T) (by linarith)
  have ht := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<2/3)).comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop :
      Filter.Tendsto (fun N : ℕ => (N : ℝ)) Filter.atTop Filter.atTop))
  obtain ⟨N₃,h₃⟩ := Filter.eventually_atTop.mp (ht.eventually_ge_atTop (2*(T+1)))
  refine ⟨max N₁ (max N₂ N₃), ?_⟩
  intro N hN V inst hcard p hlo hhi y q hsizes htilt
  have ha := h₁ N ((le_max_left _ _).trans hN) p hlo hhi
  have hb := h₂ N ((le_max_left _ _).trans ((le_max_right _ _).trans hN)) p hlo hhi
  have hc := h₃ N ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  refine ⟨ha.2.1, ha.1, ha.2.2.1, ha.2.2.2, ?_⟩
  intro s t
  subst N
  have hf := finite_mean_bounds y q hT ha.1 hb.2.2.2.2 hb.2.2.1 hb.2.2.2.1 hsizes htilt s t
  refine ⟨hf.1, hf.2.trans ?_⟩
  have hh := mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg (p*Fintype.card V))
  dsimp only [Function.comp_apply] at hh
  nlinarith

end MajorityDynamics.GraphProcess.RowConcentration

/-- info: 'MajorityDynamics.GraphProcess.RowConcentration.finite_mean_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowConcentration.finite_mean_bounds

/-- info: 'MajorityDynamics.GraphProcess.RowConcentration.uniform_degree_regime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowConcentration.uniform_degree_regime
