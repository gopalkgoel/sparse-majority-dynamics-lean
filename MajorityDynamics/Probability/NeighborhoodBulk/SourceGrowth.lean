import MajorityDynamics.Probability.NeighborhoodBulk.Regularity
import MajorityDynamics.Literature.DegreeEnumeration.UniformApplications

/-! Polynomial sparse scales discharge the growth clauses of the original
enumeration sources. These statements are uniform in the edge totals. -/
noncomputable section
open Filter Topology
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodBulk
open MajorityDynamics.Literature.DegreeEnumeration

def GraphScaleWindow (θ K : ℝ) (n m : ℕ) : Prop :=
  K⁻¹ * (n : ℝ) ^ (2 - θ) ≤ m ∧ (m : ℝ) ≤ K * (n : ℝ) ^ (2 - θ)

theorem graph_scale_bounds {θ K : ℝ} {n m : ℕ} (hK : 0 < K) (hn : 2 ≤ n)
    (h : GraphScaleWindow θ K n m) :
    0 < graphAverage n m ∧
      2 * K⁻¹ * (n : ℝ) ^ (1 - θ) ≤ graphAverage n m ∧
      graphAverage n m ≤ 2 * K * (n : ℝ) ^ (1 - θ) ∧
      2 * K⁻¹ * (n : ℝ) ^ (-θ) ≤ graphDensity n m ∧
      graphDensity n m ≤ 4 * K * (n : ℝ) ^ (-θ) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hN : 0 < (n : ℝ) - 1 := by linarith
  have he : (n : ℝ) ^ (1 - θ) * n = (n : ℝ) ^ (2 - θ) := by
    rw [← Real.rpow_add_one hn0.ne']
    congr 1
    ring
  have he' : (n : ℝ) ^ (-θ) * n = (n : ℝ) ^ (1 - θ) := by
    rw [← Real.rpow_add_one hn0.ne']
    congr 1
    ring
  have hlo : 2 * K⁻¹ * (n : ℝ) ^ (1 - θ) ≤ graphAverage n m := by
    apply (le_div_iff₀ hn0).mpr
    rw [mul_assoc, he]
    linarith [h.1]
  have hhi : graphAverage n m ≤ 2 * K * (n : ℝ) ^ (1 - θ) := by
    apply (div_le_iff₀ hn0).mpr
    rw [mul_assoc, he]
    linarith [h.2]
  refine ⟨(by positivity : 0 < 2 * K⁻¹ * (n : ℝ) ^ (1 - θ)).trans_le hlo,
    hlo, hhi, ?_, ?_⟩
  · apply (le_div_iff₀ hN).mpr
    calc
      _ ≤ 2 * K⁻¹ * (n : ℝ) ^ (-θ) * n := by gcongr; linarith
      _ = 2 * K⁻¹ * (n : ℝ) ^ (1 - θ) := by rw [mul_assoc, he']
      _ ≤ _ := hlo
  · apply (div_le_iff₀ hN).mpr
    calc
      _ ≤ 2 * K * (n : ℝ) ^ (1 - θ) := hhi
      _ = 2 * K * (n : ℝ) ^ (-θ) * n := by simp only [mul_assoc, he']
      _ ≤ 2 * K * (n : ℝ) ^ (-θ) * (2 * ((n : ℝ) - 1)) := by gcongr; linarith
      _ = _ := by ring

theorem graph_scale_log_growth (θ K : ℝ) (hθ : θ < 1) (hK : 0 < K)
    (m : ℕ → ℕ) (hm : ∀ᶠ n in atTop, GraphScaleWindow θ K n (m n))
    (r : ℝ) :
    Asymptotics.IsLittleO atTop (fun n : ℕ => Real.log n ^ r / (n : ℝ))
      (fun n => graphDensity n (m n)) := by
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have hb := ((isLittleO_log_rpow_rpow_atTop r (sub_pos.mpr hθ)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).bound (show 0 < ε * (2 * K⁻¹) by positivity)
  filter_upwards [hm, hb, eventually_ge_atTop (2 : ℕ)] with n hn hlog hn2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hL : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hμ := graph_scale_bounds hK hn2 hn
  have hμ0 : 0 < graphDensity n (m n) := div_pos hμ.1 (by exact_mod_cast (by omega : (0 : ℤ) < (n : ℤ) - 1))
  have he : (n : ℝ) ^ (-θ) * n = (n : ℝ) ^ (1 - θ) := by
    rw [← Real.rpow_add_one hn0.ne']
    congr 1
    ring
  have hlog' : Real.log n ^ r ≤ ε * (2 * K⁻¹) * (n : ℝ) ^ (1 - θ) := by
    simpa only [Function.comp_apply, Real.norm_of_nonneg (Real.rpow_nonneg hL _),
      Real.norm_of_nonneg (Real.rpow_nonneg hn0.le _)] using hlog
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ Real.log (n : ℝ) ^ r / n),
    Real.norm_of_nonneg hμ0.le]
  apply (div_le_iff₀ hn0).mpr
  calc
    _ ≤ ε * (2 * K⁻¹) * (n : ℝ) ^ (1 - θ) := hlog'
    _ = ε * (2 * K⁻¹ * (n : ℝ) ^ (-θ)) * n := by simp only [mul_assoc, he]
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hμ.2.2.2.1 hε.le) hn0.le

theorem eventually_graph_scale_domain (θ K μ₀ : ℝ) (hθ : 0 < θ) (hK : 0 < K) (hμ₀ : 0 < μ₀) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, GraphScaleWindow θ K n m →
      m ≤ n.choose 2 ∧ graphDensity n m ≤ μ₀ ∧ 0 < graphErrorScale (7 / 12) n m := by
  have hu : Tendsto (fun n : ℕ => 4 * K * (n : ℝ) ^ (-θ)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hθ).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (4 * K)
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    hu.eventually (eventually_lt_nhds (lt_min hμ₀ zero_lt_one))] with n hn hsmall
  intro m hm
  have hb := graph_scale_bounds hK hn hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hN : 0 < (n : ℝ) - 1 := by exact_mod_cast (by omega : (0 : ℤ) < (n : ℤ) - 1)
  refine ⟨?_, hb.2.2.2.2.trans (hsmall.trans_le (min_le_left _ _)).le, ?_⟩
  · have hρ : graphDensity n m ≤ 1 := hb.2.2.2.2.trans (hsmall.trans_le (min_le_right _ _)).le
    have ha : graphAverage n m ≤ (n : ℝ) - 1 := (div_le_iff₀ hN).mp hρ |>.trans_eq (one_mul _)
    have hh := (div_le_iff₀ hn0).mp ha
    have : (m : ℝ) ≤ (n.choose 2 : ℝ) := by rw [Nat.cast_choose_two]; nlinarith
    exact_mod_cast this
  · unfold graphErrorScale
    exact add_pos_of_nonneg_of_pos (by positivity) (Real.rpow_pos_of_pos hb.1 _)

theorem eventually_graph_error_small (θ K ε : ℝ) (hθ : θ < 1) (hK : 0 < K) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, GraphScaleWindow θ K n m →
      graphErrorScale (7 / 12) n m ≤ ε := by
  have hn := tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog : Tendsto (fun n : ℕ => Real.log n ^ 2 / Real.sqrt n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_two, Real.sqrt_eq_rpow] using
      ((isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp hn)
  have hav : Tendsto (fun n : ℕ => 2 * K⁻¹ * (n : ℝ) ^ (1 - θ)) atTop atTop := by
    exact ((tendsto_rpow_atTop (sub_pos.mpr hθ)).comp hn).const_mul_atTop (by positivity)
  have herr : Tendsto (fun n : ℕ => (2 * K⁻¹ * (n : ℝ) ^ (1 - θ)) ^ (-1 / 12 : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_div] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 12)).comp hav
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    hlog.eventually (eventually_lt_nhds (show (0 : ℝ) < ε / 2 by positivity)),
    herr.eventually (eventually_lt_nhds (show (0 : ℝ) < ε / 2 by positivity))] with n hn2 hl he
  intro m hm
  have hb := graph_scale_bounds hK hn2 hm
  have hp : 0 < 2 * K⁻¹ * (n : ℝ) ^ (1 - θ) := by
    have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    positivity
  have hpow := Real.rpow_le_rpow_of_nonpos hp hb.2.1 (by norm_num : (-1 / 12 : ℝ) ≤ 0)
  unfold graphErrorScale
  norm_num only [show (5 * (7 / 12) - 3 : ℝ) = -1 / 12 by norm_num]
  linarith

end MajorityDynamics.Probability.NeighborhoodBulk
