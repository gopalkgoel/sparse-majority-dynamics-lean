import MajorityDynamics.Literature.EdgeProbabilities.Growth
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace MajorityDynamics.Literature.EdgeProbabilities

theorem bigO_div_theta {f F g G : ℕ → ℝ}
    (hf : f =O[atTop] F) (hg : g =Θ[atTop] G) :
    (fun k => f k / g k) =O[atTop] (fun k => F k / G k) := by
  simpa only [div_eq_mul_inv] using hf.mul hg.inv.1

theorem power_div_twice {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) (a : ℝ) :
    (fun k => (N k : ℝ)^a / N k / N k) =ᶠ[atTop]
      (fun k => (N k : ℝ)^(a-2)) := by
  filter_upwards [(tendsto_natCast_atTop_atTop.comp hN).eventually_gt_atTop (0 : ℝ)] with k hk
  change 0 < (N k : ℝ) at hk
  rw [rpow_div_self hk, rpow_div_self hk]
  congr 1
  ring

/-- The true density tracks the varying total, without a single polynomial exponent. -/
theorem graph_density_scaled {N n m : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (hn : (fun k => (n k : ℝ)) =Θ[atTop] (fun k => (N k : ℝ))) :
    (fun k => graphDensity (n k) (m k)) =Θ[atTop]
      (fun k => (m k : ℝ) / N k / N k) := by
  have hn' := (sub_one_isTheta (nat_tendsto_of_isTheta hN hn)).trans hn
  have h := (((isTheta_refl (fun k => (m k : ℝ)) atTop).div hn).div hn').const_mul_left
    (by norm_num : (2:ℝ) ≠ 0)
  simpa only [graphDensity, graphAverage, mul_div_assoc] using h

theorem bipartite_density_scaled {N ell n m : ℕ → ℕ}
    (hell : (fun k => (ell k : ℝ)) =Θ[atTop] (fun k => (N k : ℝ)))
    (hn : (fun k => (n k : ℝ)) =Θ[atTop] (fun k => (N k : ℝ))) :
    (fun k => bipartiteDensity (ell k) (n k) (m k)) =Θ[atTop]
      (fun k => (m k : ℝ) / N k / N k) := by
  simpa only [bipartiteDensity, div_div] using
    ((isTheta_refl (fun k => (m k : ℝ)) atTop).div hell).div hn

/-- Polynomial lower and upper total bounds induce independent density bounds. -/
theorem density_band_of_scaled {N m : ℕ → ℕ} {d : ℕ → ℝ} {θ η : ℝ}
    (hN : Tendsto N atTop atTop)
    (hs : d =Θ[atTop] (fun k => (m k : ℝ) / N k / N k))
    (hlo : (fun k => (N k : ℝ)^(2-θ)) =O[atTop] (fun k => (m k : ℝ)))
    (hhi : (fun k => (m k : ℝ)) =O[atTop] (fun k => (N k : ℝ)^(2-η))) :
    (fun k => (N k : ℝ)^(-θ)) =O[atTop] d ∧
    d =O[atTop] (fun k => (N k : ℝ)^(-η)) := by
  have hn := isTheta_refl (fun k => (N k : ℝ)) atTop
  have hl := bigO_div_theta (bigO_div_theta hlo hn) hn
  have hu := bigO_div_theta (bigO_div_theta hhi hn) hn
  have el := power_div_twice hN (2-θ)
  have eu := power_div_twice hN (2-η)
  simp only [sub_sub_cancel_left] at el eu
  exact ⟨el.symm.isBigO.trans (hl.trans hs.symm.1),
    hs.1.trans (hu.trans eu.isBigO)⟩

theorem graph_sequence_growth_band {N n m : ℕ → ℕ} {θ η : ℝ}
    (hη : 0 < η) (hθhi : θ < 1) (hN : Tendsto N atTop atTop)
    (hn : (fun k => (n k : ℝ)) =Θ[atTop] (fun k => (N k : ℝ)))
    (hlo : (fun k => (N k : ℝ)^(2-θ)) =O[atTop] (fun k => (m k : ℝ)))
    (hhi : (fun k => (m k : ℝ)) =O[atTop] (fun k => (N k : ℝ)^(2-η))) :
    Tendsto (fun k => graphDensity (n k) (m k)) atTop (𝓝 0) ∧
    ∀ K : ℝ, 0 < K → Asymptotics.IsLittleO atTop
      (fun k => (Real.log (n k)) ^ K / (n k : ℝ))
      (fun k => graphDensity (n k) (m k)) := by
  have hd := density_band_of_scaled hN (graph_density_scaled hN hn) hlo hhi
  constructor
  · exact hd.2.trans_tendsto ((tendsto_rpow_neg_atTop hη).comp
      (tendsto_natCast_atTop_atTop.comp hN))
  · intro K _
    have hnTop : Tendsto (fun k => (n k : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (nat_tendsto_of_isTheta hN hn)
    have hlog := (isLittleO_log_rpow_rpow_atTop K (sub_pos.mpr hθhi)).comp_tendsto hnTop
    have hratio := hlog.mul_isBigO (isBigO_refl (fun k => (n k : ℝ)⁻¹) atTop)
    have hnPow := hn.rpow (r := 1-θ) (.of_forall fun _ => Nat.cast_nonneg _)
      (.of_forall fun _ => Nat.cast_nonneg _)
    have heq : (fun k => (N k : ℝ)^(1-θ)/(N k : ℝ)) =ᶠ[atTop]
        (fun k => (N k : ℝ)^(-θ)) := by
      filter_upwards [(tendsto_natCast_atTop_atTop.comp hN).eventually_gt_atTop (0 : ℝ)] with k hk
      change 0 < (N k : ℝ) at hk
      rw [rpow_div_self hk]
      congr 1
      ring
    have htarget := ((hnPow.div hn).trans_eventuallyEq heq).1.trans hd.1
    have hratio' : (fun k => (Real.log (n k))^K / (n k : ℝ)) =o[atTop]
        (fun k => (n k : ℝ)^(1-θ)/(n k : ℝ)) := by
      simpa only [Function.comp_def, ← div_eq_mul_inv] using hratio
    exact hratio'.trans_isBigO htarget

theorem bipartite_power_growth_lower {N ell n m : ℕ → ℕ} {θ : ℝ}
    (hθhi : θ < 1) (hN : Tendsto N atTop atTop)
    (hell : (fun k => (ell k : ℝ)) =Θ[atTop] (fun k => (N k : ℝ)))
    (hn : (fun k => (n k : ℝ)) =Θ[atTop] (fun k => (N k : ℝ)))
    (hm : (fun k => (N k : ℝ)^(2-θ)) =O[atTop] (fun k => (m k : ℝ))) :
    Asymptotics.IsLittleO atTop
      (fun k => ((ell k : ℝ) + n k) ^ (5-5*((7:ℝ)/12)))
      (fun k => (ell k : ℝ)*n k*(m k : ℝ)^(3-5*((7:ℝ)/12))) := by
  have hsum : (fun k => (ell k : ℝ)+n k) =O[atTop] (fun k => (N k : ℝ)) :=
    hell.1.add hn.1
  have hnum := hsum.rpow (r := (25:ℝ)/12) (by norm_num)
    (.of_forall fun _ => Nat.cast_nonneg _)
  have hmpow := hm.rpow (r := (1:ℝ)/12) (by norm_num) (.of_forall fun _ => Nat.cast_nonneg _)
  have hden := (hell.symm.1.mul hn.symm.1).mul hmpow
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
  have hout := (hnum.trans_isLittleO hgap).trans_isBigO (hdenEq.symm.isBigO.trans hden)
  norm_num only at hout ⊢
  exact hout

theorem bipartite_log_growth_lower {N ell n m : ℕ → ℕ} {θ : ℝ}
    (hθhi : θ < 1) (hN : Tendsto N atTop atTop)
    (hell : (fun k => (ell k : ℝ)) =Θ[atTop] (fun k => (N k : ℝ)))
    (hn : (fun k => (n k : ℝ)) =Θ[atTop] (fun k => (N k : ℝ)))
    (hm : (fun k => (N k : ℝ)^(2-θ)) =O[atTop] (fun k => (m k : ℝ)))
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
    have hout := hprod.trans_isBigO ((hprodTheta.trans_eventuallyEq heq).1.trans hm)
    simpa only [Function.comp_def, mul_comm] using hout
  exact (hone ell n hell hn).add (hone n ell hn hell)

theorem bipartite_sequence_growth_band {N ell n m : ℕ → ℕ} {θ η : ℝ}
    (hη : 0 < η) (hθhi : θ < 1) (hN : Tendsto N atTop atTop)
    (hell : (fun k => (ell k : ℝ)) =Θ[atTop] (fun k => (N k : ℝ)))
    (hn : (fun k => (n k : ℝ)) =Θ[atTop] (fun k => (N k : ℝ)))
    (hlo : (fun k => (N k : ℝ)^(2-θ)) =O[atTop] (fun k => (m k : ℝ)))
    (hhi : (fun k => (m k : ℝ)) =O[atTop] (fun k => (N k : ℝ)^(2-η))) :
    Tendsto ell atTop atTop ∧
    Tendsto (fun k => bipartiteDensity (ell k) (n k) (m k)) atTop (𝓝 0) ∧
    Asymptotics.IsLittleO atTop
      (fun k => ((ell k : ℝ)+n k)^(5-5*((7:ℝ)/12)))
      (fun k => (ell k : ℝ)*n k*(m k : ℝ)^(3-5*((7:ℝ)/12))) ∧
    ∀ K : ℝ, 0 < K → Asymptotics.IsLittleO atTop
      (fun k => (ell k : ℝ)*(Real.log (n k))^K +
        (n k : ℝ)*(Real.log (ell k))^K) (fun k => (m k : ℝ)) := by
  refine ⟨nat_tendsto_of_isTheta hN hell, ?_,
    bipartite_power_growth_lower hθhi hN hell hn hlo,
    fun K _ => bipartite_log_growth_lower hθhi hN hell hn hlo K⟩
  have hd := density_band_of_scaled hN (bipartite_density_scaled hell hn) hlo hhi
  exact hd.2.trans_tendsto ((tendsto_rpow_neg_atTop hη).comp
    (tendsto_natCast_atTop_atTop.comp hN))

end MajorityDynamics.Literature.EdgeProbabilities
