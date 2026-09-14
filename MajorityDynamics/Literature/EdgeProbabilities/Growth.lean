import MajorityDynamics.Literature.EdgeProbabilities.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Genuine source little-o hypotheses from polynomial comparability of sizes and totals. -/
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace MajorityDynamics.Literature.EdgeProbabilities

/-- Convert explicit two-sided bounds into asymptotic comparability. -/
theorem isTheta_of_eventual_bounds {f g : ℕ → ℝ} {c C : ℝ}
    (hc : 0 < c) (hf : ∀ᶠ k in atTop, 0 ≤ f k)
    (hg : ∀ᶠ k in atTop, 0 ≤ g k)
    (h : ∀ᶠ k in atTop, c * g k ≤ f k ∧ f k ≤ C * g k) :
    f =Θ[atTop] g := by
  constructor
  · apply IsBigO.of_bound C
    filter_upwards [hf, hg, h] with k hfk hgk hk
    simpa [Real.norm_eq_abs, abs_of_nonneg hfk, abs_of_nonneg hgk] using hk.2
  · apply IsBigO.of_bound c⁻¹
    filter_upwards [hf, hg, h] with k hfk hgk hk
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hfk, abs_of_nonneg hgk]
    exact (le_inv_mul_iff₀ hc).mpr hk.1

/-- Comparable nonnegative natural size sequences diverge together. -/
theorem nat_tendsto_of_isTheta {N n : ℕ → ℕ}
    (hN : Tendsto N atTop atTop)
    (hn : (fun k => (n k : ℝ)) =Θ[atTop] (fun k => (N k : ℝ))) :
    Tendsto n atTop atTop := by
  have hNr : Tendsto (fun k => (N k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hnr : Tendsto (fun k => (n k : ℝ)) atTop atTop := by
    simpa only [Function.comp_def, Real.norm_eq_abs, Nat.abs_cast] using
      hn.tendsto_norm_atTop_iff.mpr (by simpa only [Function.comp_def, Real.norm_eq_abs, Nat.abs_cast] using hNr)
  exact tendsto_natCast_atTop_iff.mp hnr

/-- Subtracting one vertex leaves a size sequence comparable. -/
theorem sub_one_isTheta {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) :
    (fun k => (n k : ℝ) - 1) =Θ[atTop] (fun k => (n k : ℝ)) := by
  have htwo : ∀ᶠ k in atTop, 2 ≤ (n k : ℝ) :=
    (tendsto_natCast_atTop_atTop.comp hn).eventually_ge_atTop 2
  apply isTheta_of_eventual_bounds (c := 1/2) (C := 1) (by norm_num)
  · filter_upwards [htwo] with k hk
    linarith
  · exact .of_forall fun _ => Nat.cast_nonneg _
  · filter_upwards [htwo] with k hk
    constructor <;> linarith

/-- Strictly smaller powers are little-o along a diverging positive reference size. -/
theorem rpow_isLittleO_of_lt {N : ℕ → ℕ} {a b : ℝ}
    (hN : Tendsto N atTop atTop) (hab : a < b) :
    (fun k => (N k : ℝ)^a) =o[atTop] (fun k => (N k : ℝ)^b) := by
  have hpos : ∀ᶠ k in atTop, 0 < (N k : ℝ) :=
    (tendsto_natCast_atTop_atTop.comp hN).eventually_gt_atTop 0
  apply isLittleO_of_tendsto'
    (hpos.mono fun k hk hzero => False.elim ((Real.rpow_pos_of_pos hk b).ne' hzero))
  have ht := (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).comp
    (tendsto_natCast_atTop_atTop.comp hN)
  apply ht.congr'
  filter_upwards [hpos] with k hk
  change (N k : ℝ)^(-(b-a)) = _
  rw [show -(b-a) = a-b by ring, Real.rpow_sub hk]

theorem rpow_div_self {x : ℝ} (hx : 0 < x) (a : ℝ) : x^a/x = x^(a-1) := by
  simpa only [Real.rpow_one] using (Real.rpow_sub hx a 1).symm

/-- The graph source density is comparable to the original sparse density scale. -/
theorem graph_density_isTheta {N n m : ℕ → ℕ} {θ : ℝ}
    (hN : Tendsto N atTop atTop)
    (hn : (fun k => (n k : ℝ)) =Θ[atTop] (fun k => (N k : ℝ)))
    (hm : (fun k => (m k : ℝ)) =Θ[atTop] (fun k => (N k : ℝ)^(2-θ))) :
    (fun k => graphDensity (n k) (m k)) =Θ[atTop] (fun k => (N k : ℝ)^(-θ)) := by
  have hn' := (sub_one_isTheta (nat_tendsto_of_isTheta hN hn)).trans hn
  have hh := ((hm.div hn).div hn').const_mul_left (by norm_num : (2 : ℝ) ≠ 0)
  have heq : (fun k => (N k : ℝ)^(2-θ)/(N k : ℝ)/(N k : ℝ)) =ᶠ[atTop]
      (fun k => (N k : ℝ)^(-θ)) := by
    filter_upwards [(tendsto_natCast_atTop_atTop.comp hN).eventually_gt_atTop (0 : ℝ)]
      with k hk
    change 0 < (N k : ℝ) at hk
    rw [rpow_div_self hk, rpow_div_self hk]
    congr 1
    ring
  have hout := hh.trans_eventuallyEq heq
  have hleft : (fun k => graphDensity (n k) (m k)) =ᶠ[atTop]
      (fun k => 2*((m k : ℝ)/(n k : ℝ)/((n k : ℝ)-1))) := by
    apply Eventually.of_forall
    intro k
    unfold graphDensity graphAverage
    ring
  exact hleft.trans_isTheta hout

/-- Both graph source growth hypotheses follow from size and total comparability. -/
theorem graph_sequence_growth {N n m : ℕ → ℕ} {θ : ℝ}
    (hθlo : 0 < θ) (hθhi : θ < 1) (hN : Tendsto N atTop atTop)
    (hn : (fun k => (n k : ℝ)) =Θ[atTop] (fun k => (N k : ℝ)))
    (hm : (fun k => (m k : ℝ)) =Θ[atTop] (fun k => (N k : ℝ)^(2-θ))) :
    Tendsto (fun k => graphDensity (n k) (m k)) atTop (𝓝 0) ∧
    ∀ K : ℝ, 0 < K → Asymptotics.IsLittleO atTop
      (fun k => (Real.log (n k)) ^ K / (n k : ℝ))
      (fun k => graphDensity (n k) (m k)) := by
  have hd := graph_density_isTheta hN hn hm
  constructor
  · exact hd.tendsto_zero_iff.mpr ((tendsto_rpow_neg_atTop hθlo).comp
      (tendsto_natCast_atTop_atTop.comp hN))
  · intro K _
    have hnTop : Tendsto (fun k => (n k : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (nat_tendsto_of_isTheta hN hn)
    have hlog := (isLittleO_log_rpow_rpow_atTop K (sub_pos.mpr hθhi)).comp_tendsto hnTop
    have hratio := hlog.mul_isBigO (isBigO_refl (fun k => (n k : ℝ)⁻¹) atTop)
    have hnPow := hn.rpow (r := 1-θ) (.of_forall fun _ => Nat.cast_nonneg _)
      (.of_forall fun _ => Nat.cast_nonneg _)
    have hratioTheta := hnPow.div hn
    have heq : (fun k => (N k : ℝ)^(1-θ)/(N k : ℝ)) =ᶠ[atTop]
        (fun k => (N k : ℝ)^(-θ)) := by
      filter_upwards [(tendsto_natCast_atTop_atTop.comp hN).eventually_gt_atTop (0 : ℝ)]
        with k hk
      change 0 < (N k : ℝ) at hk
      rw [rpow_div_self hk]
      congr 1
      ring
    have htarget := (hratioTheta.trans_eventuallyEq heq).trans hd.symm
    have hratio' : (fun k => (Real.log (n k))^K / (n k : ℝ)) =o[atTop]
        (fun k => (n k : ℝ)^(1-θ)/(n k : ℝ)) := by
      simpa only [Function.comp_def, ← div_eq_mul_inv] using hratio
    exact hratio'.trans_isTheta htarget

/-- Source bipartite density from comparable dimensions and polynomial total. -/
theorem bipartite_density_isTheta {N ell n m : ℕ → ℕ} {θ : ℝ}
    (hN : Tendsto N atTop atTop)
    (hell : (fun k => (ell k : ℝ)) =Θ[atTop] (fun k => (N k : ℝ)))
    (hn : (fun k => (n k : ℝ)) =Θ[atTop] (fun k => (N k : ℝ)))
    (hm : (fun k => (m k : ℝ)) =Θ[atTop] (fun k => (N k : ℝ)^(2-θ))) :
    (fun k => bipartiteDensity (ell k) (n k) (m k)) =Θ[atTop]
      (fun k => (N k : ℝ)^(-θ)) := by
  apply (hm.div (hell.mul hn)).trans_eventuallyEq
  filter_upwards [(tendsto_natCast_atTop_atTop.comp hN).eventually_gt_atTop (0 : ℝ)]
    with k hk
  change 0 < (N k : ℝ) at hk
  rw [← div_div, rpow_div_self hk, rpow_div_self hk]
  congr 1
  ring

/-- Multiply a power by the base without changing its value at positive inputs. -/
theorem rpow_mul_self {x : ℝ} (hx : 0 < x) (a : ℝ) : x^a*x = x^(a+1) := by
  simpa only [Real.rpow_one] using (Real.rpow_add hx a 1).symm

/-- The additional LW20 growth condition for the fixed source exponent `7/12`. -/
theorem bipartite_power_growth {N ell n m : ℕ → ℕ} {θ : ℝ}
    (hθhi : θ < 1) (hN : Tendsto N atTop atTop)
    (hell : (fun k => (ell k : ℝ)) =Θ[atTop] (fun k => (N k : ℝ)))
    (hn : (fun k => (n k : ℝ)) =Θ[atTop] (fun k => (N k : ℝ)))
    (hm : (fun k => (m k : ℝ)) =Θ[atTop] (fun k => (N k : ℝ)^(2-θ))) :
    Asymptotics.IsLittleO atTop
      (fun k => ((ell k : ℝ) + n k) ^ (5-5*((7:ℝ)/12)))
      (fun k => (ell k : ℝ)*n k*(m k : ℝ)^(3-5*((7:ℝ)/12))) := by
  have hsum : (fun k => (ell k : ℝ)+n k) =O[atTop] (fun k => (N k : ℝ)) :=
    hell.1.add hn.1
  have hnum := hsum.rpow (r := (25:ℝ)/12) (by norm_num)
    (.of_forall fun _ => Nat.cast_nonneg _)
  have hmpow := hm.rpow (r := (1:ℝ)/12) (.of_forall fun _ => Nat.cast_nonneg _)
    (.of_forall fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hden := (hell.mul hn).mul hmpow
  have hdenEq : (fun k => (N k : ℝ)*(N k : ℝ)*((N k : ℝ)^(2-θ))^((1:ℝ)/12))
      =ᶠ[atTop] (fun k => (N k : ℝ)^(2+(2-θ)/12)) := by
    filter_upwards [(tendsto_natCast_atTop_atTop.comp hN).eventually_gt_atTop (0 : ℝ)]
      with k hk
    change 0 < (N k : ℝ) at hk
    rw [← Real.rpow_mul hk.le]
    calc
      _ = (N k : ℝ)^(2:ℝ) * (N k : ℝ)^((2-θ)*((1:ℝ)/12)) := by
        rw [Real.rpow_two]
        ring
      _ = _ := by
        rw [← Real.rpow_add hk]
        congr 1
        ring
  have hgap := rpow_isLittleO_of_lt hN
    (show (25:ℝ)/12 < 2+(2-θ)/12 by linarith)
  have hout := (hnum.trans_isLittleO hgap).trans_isTheta (hden.trans_eventuallyEq hdenEq).symm
  norm_num only at hout ⊢
  exact hout

/-- Either logarithmic summand is little-o of the total; side sizes may vary. -/
theorem bipartite_log_growth {N ell n m : ℕ → ℕ} {θ : ℝ}
    (hθhi : θ < 1) (hN : Tendsto N atTop atTop)
    (hell : (fun k => (ell k : ℝ)) =Θ[atTop] (fun k => (N k : ℝ)))
    (hn : (fun k => (n k : ℝ)) =Θ[atTop] (fun k => (N k : ℝ)))
    (hm : (fun k => (m k : ℝ)) =Θ[atTop] (fun k => (N k : ℝ)^(2-θ)))
    (K : ℝ) :
    Asymptotics.IsLittleO atTop
      (fun k => (ell k : ℝ)*(Real.log (n k))^K +
        (n k : ℝ)*(Real.log (ell k))^K) (fun k => (m k : ℝ)) := by
  have hone (s t : ℕ → ℕ)
      (hs : (fun k => (s k : ℝ)) =Θ[atTop] (fun k => (N k : ℝ)))
      (ht : (fun k => (t k : ℝ)) =Θ[atTop] (fun k => (N k : ℝ))) :
      (fun k => (s k : ℝ)*(Real.log (t k))^K) =o[atTop] (fun k => (m k : ℝ)) := by
    have htTop : Tendsto (fun k => (t k : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (nat_tendsto_of_isTheta hN ht)
    have hlog := (isLittleO_log_rpow_rpow_atTop K (sub_pos.mpr hθhi)).comp_tendsto htTop
    have hprod := hlog.mul_isBigO (isBigO_refl (fun k => (s k : ℝ)) atTop)
    have htpow := ht.rpow (r := 1-θ) (.of_forall fun _ => Nat.cast_nonneg _)
      (.of_forall fun _ => Nat.cast_nonneg _)
    have hprodTheta := htpow.mul hs
    have heq : (fun k => (N k : ℝ)^(1-θ)*(N k : ℝ)) =ᶠ[atTop]
        (fun k => (N k : ℝ)^(2-θ)) := by
      filter_upwards [(tendsto_natCast_atTop_atTop.comp hN).eventually_gt_atTop (0 : ℝ)]
        with k hk
      change 0 < (N k : ℝ) at hk
      rw [rpow_mul_self hk]
      congr 1
      ring
    have hout := hprod.trans_isTheta ((hprodTheta.trans_eventuallyEq heq).trans hm.symm)
    simpa only [Function.comp_def, mul_comm] using hout
  exact (hone ell n hell hn).add (hone n ell hn hell)

/-- All source growth hypotheses for LW20 at `alpha=7/12`. -/
theorem bipartite_sequence_growth {N ell n m : ℕ → ℕ} {θ : ℝ}
    (hθlo : 0 < θ) (hθhi : θ < 1) (hN : Tendsto N atTop atTop)
    (hell : (fun k => (ell k : ℝ)) =Θ[atTop] (fun k => (N k : ℝ)))
    (hn : (fun k => (n k : ℝ)) =Θ[atTop] (fun k => (N k : ℝ)))
    (hm : (fun k => (m k : ℝ)) =Θ[atTop] (fun k => (N k : ℝ)^(2-θ))) :
    Tendsto ell atTop atTop ∧
    Tendsto (fun k => bipartiteDensity (ell k) (n k) (m k)) atTop (𝓝 0) ∧
    Asymptotics.IsLittleO atTop
      (fun k => ((ell k : ℝ)+n k)^(5-5*((7:ℝ)/12)))
      (fun k => (ell k : ℝ)*n k*(m k : ℝ)^(3-5*((7:ℝ)/12))) ∧
    ∀ K : ℝ, 0 < K → Asymptotics.IsLittleO atTop
      (fun k => (ell k : ℝ)*(Real.log (n k))^K +
        (n k : ℝ)*(Real.log (ell k))^K) (fun k => (m k : ℝ)) := by
  refine ⟨nat_tendsto_of_isTheta hN hell, ?_, bipartite_power_growth hθhi hN hell hn hm,
    fun K _ => bipartite_log_growth hθhi hN hell hn hm K⟩
  exact (bipartite_density_isTheta hN hell hn hm).tendsto_zero_iff.mpr
    ((tendsto_rpow_neg_atTop hθlo).comp (tendsto_natCast_atTop_atTop.comp hN))

end MajorityDynamics.Literature.EdgeProbabilities
