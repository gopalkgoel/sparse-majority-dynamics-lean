import MajorityDynamics.Probability.NeighborhoodBulk.SourceGrowth

noncomputable section
open Filter Topology
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodBulk
open MajorityDynamics.Literature.DegreeEnumeration

def BipartiteScaleWindow (θ K : ℝ) (n ell m : ℕ) : Prop :=
  (n : ℝ) / K ≤ ell ∧ (ell : ℝ) ≤ K * n ∧ GraphScaleWindow θ K n m

theorem bipartite_scale_bounds {θ K : ℝ} {n ell m : ℕ} (hK : 1 ≤ K) (hn : 2 ≤ n)
    (h : BipartiteScaleWindow θ K n ell m) :
    0 < (ell : ℝ) ∧
      (K ^ 2)⁻¹ * (n : ℝ) ^ (1 - θ) ≤ leftAverage ell m ∧
      leftAverage ell m ≤ K ^ 2 * (n : ℝ) ^ (1 - θ) ∧
      (K ^ 2)⁻¹ * (n : ℝ) ^ (1 - θ) ≤ rightAverage n m ∧
      bipartiteDensity ell n m ≤ K ^ 2 * (n : ℝ) ^ (-θ) := by
  have hK0 : 0 < K := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hell : (0 : ℝ) < ell := (div_pos hn0 hK0).trans_le h.1
  have he : (n : ℝ) ^ (1 - θ) * n = (n : ℝ) ^ (2 - θ) := by
    rw [← Real.rpow_add_one hn0.ne']
    congr 1
    ring
  have he' : (n : ℝ) ^ (-θ) * n = (n : ℝ) ^ (1 - θ) := by
    rw [← Real.rpow_add_one hn0.ne']
    congr 1
    ring
  have hlo : (K ^ 2)⁻¹ * (n : ℝ) ^ (1 - θ) ≤ leftAverage ell m := by
    apply (le_div_iff₀ hell).mpr
    calc
      _ ≤ (K ^ 2)⁻¹ * (n : ℝ) ^ (1 - θ) * (K * n) := by gcongr; exact h.2.1
      _ = K⁻¹ * (n : ℝ) ^ (2 - θ) := by rw [← he]; field_simp
      _ ≤ _ := h.2.2.1
  have hhi : leftAverage ell m ≤ K ^ 2 * (n : ℝ) ^ (1 - θ) := by
    apply (div_le_iff₀ hell).mpr
    calc
      _ ≤ K * (n : ℝ) ^ (2 - θ) := h.2.2.2
      _ = K ^ 2 * (n : ℝ) ^ (1 - θ) * ((n : ℝ) / K) := by rw [← he]; field_simp
      _ ≤ _ := by gcongr; exact h.1
  have hright : (K ^ 2)⁻¹ * (n : ℝ) ^ (1 - θ) ≤ rightAverage n m := by
    have hg := graph_scale_bounds hK0 hn h.2.2
    have ha : graphAverage n m = 2 * rightAverage n m := by
      unfold graphAverage rightAverage
      ring
    rw [ha] at hg
    have hInv : (K ^ 2)⁻¹ ≤ K⁻¹ := by
      apply inv_anti₀ hK0
      nlinarith
    have hh := mul_le_mul_of_nonneg_right hInv (Real.rpow_nonneg hn0.le (1 - θ))
    linarith [hg.2.1]
  refine ⟨hell, hlo, hhi, hright, ?_⟩
  have hρ : bipartiteDensity ell n m = leftAverage ell m / n := by
    unfold bipartiteDensity leftAverage
    rw [div_div]
  rw [hρ]
  apply (div_le_iff₀ hn0).mpr
  simpa only [mul_assoc, he'] using hhi

theorem littleO_of_polynomial_bounds (f g : ℕ → ℝ) (A B a b : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hab : a < b)
    (hf : ∀ᶠ n : ℕ in atTop, ‖f n‖ ≤ A * (n : ℝ) ^ a)
    (hg : ∀ᶠ n : ℕ in atTop, B * (n : ℝ) ^ b ≤ ‖g n‖) :
    Asymptotics.IsLittleO atTop f g := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (a - b)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_sub] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [hf, hg, eventually_ge_atTop (1 : ℕ),
    ht.eventually (eventually_lt_nhds (show (0 : ℝ) < ε * B / A by positivity))]
      with n hnF hnG hn hnsmall
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hh := (lt_div_iff₀ hA).mp hnsmall
  have he : (n : ℝ) ^ (a - b) * (n : ℝ) ^ b = (n : ℝ) ^ a := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  calc
    _ ≤ A * (n : ℝ) ^ a := hnF
    _ ≤ ε * (B * (n : ℝ) ^ b) := by
      have hm := mul_le_mul_of_nonneg_right hh.le (Real.rpow_nonneg hn0.le b)
      simpa only [mul_assoc, mul_comm _ A, he] using hm
    _ ≤ _ := mul_le_mul_of_nonneg_left hnG hε.le

theorem bipartite_scale_power_growth (θ K : ℝ) (hθ : θ < 1) (hK : 1 ≤ K)
    (ell m : ℕ → ℕ) (hm : ∀ᶠ n in atTop, BipartiteScaleWindow θ K n (ell n) (m n)) :
    Asymptotics.IsLittleO atTop
      (fun n => ((ell n : ℝ) + n) ^ (5 - 5 * (7 / 12 : ℝ)))
      (fun n => (ell n : ℝ) * n * (m n : ℝ) ^ (3 - 5 * (7 / 12 : ℝ))) := by
  have hK0 : 0 < K := by linarith
  norm_num only [show (5 - 5 * (7 / 12) : ℝ) = 25 / 12 by norm_num,
    show (3 - 5 * (7 / 12) : ℝ) = 1 / 12 by norm_num]
  apply littleO_of_polynomial_bounds _ _ ((K + 1) ^ (25 / 12 : ℝ))
    (K⁻¹ * (K⁻¹ : ℝ) ^ (1 / 12 : ℝ)) (25 / 12) (2 + (2 - θ) / 12)
    (by positivity) (by positivity) (by linarith)
  · filter_upwards [hm] with n hn
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ ((ell n : ℝ) + n) ^ (25 / 12 : ℝ))]
    calc
      _ ≤ ((K + 1) * n) ^ (25 / 12 : ℝ) := by
        apply Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
        nlinarith [hn.2.1]
      _ = _ := Real.mul_rpow (by positivity) (by positivity)
  · filter_upwards [hm, eventually_ge_atTop (1 : ℕ)] with n hn hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ (ell n : ℝ) * n * (m n : ℝ) ^ (1 / 12 : ℝ))]
    calc
      _ = ((n : ℝ) / K) * n * (K⁻¹ * (n : ℝ) ^ (2 - θ)) ^ (1 / 12 : ℝ) := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hn0.le]
        rw [show (2 + (2 - θ) / 12 : ℝ) = 2 + (2 - θ) * (1 / 12) by ring,
          Real.rpow_add hn0, Real.rpow_two]
        ring
      _ ≤ _ := by
        gcongr
        · exact hn.1
        · exact hn.2.2.1

theorem side_log_bound {K : ℝ} {n ell : ℕ} (hK : 1 ≤ K)
    (hn : 0 < n) (hlog : 1 ≤ Real.log (n : ℝ)) (hell : 0 < ell) (hupper : (ell : ℝ) ≤ K * n) :
    Real.log (ell : ℝ) ≤ (Real.log K + 1) * Real.log (n : ℝ) := by
  have hK0 : 0 < K := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have he0 : (0 : ℝ) < ell := by exact_mod_cast hell
  have hh := Real.log_le_log he0 hupper
  rw [Real.log_mul hK0.ne' hn0.ne'] at hh
  have hp := mul_nonneg (Real.log_nonneg hK) (sub_nonneg.mpr hlog)
  nlinarith

theorem bipartite_scale_log_growth (θ K : ℝ) (hθ : θ < 1) (hK : 1 ≤ K)
    (ell m : ℕ → ℕ) (hm : ∀ᶠ n in atTop, BipartiteScaleWindow θ K n (ell n) (m n))
    (r : ℝ) (hr : 0 < r) :
    Asymptotics.IsLittleO atTop
      (fun n => (ell n : ℝ) * Real.log n ^ r + (n : ℝ) * Real.log (ell n) ^ r)
      (fun n => (m n : ℝ)) := by
  have hK0 : 0 < K := by linarith
  let D : ℝ := (Real.log K + 1) ^ r
  have hD : 0 ≤ D := Real.rpow_nonneg (by linarith [Real.log_nonneg hK]) _
  have hKD : 0 < K + D := by linarith
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have hb := ((isLittleO_log_rpow_rpow_atTop r (sub_pos.mpr hθ)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).bound
      (show 0 < ε * K⁻¹ / (K + D) by positivity)
  filter_upwards [hm, hb, eventually_ge_atTop (2 : ℕ),
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_ge_atTop 1)] with n hn hbound hn2 hlog
  simp only [Function.comp_apply] at hlog
  have hn0 : 0 < n := by omega
  have hn0r : (0 : ℝ) < n := by exact_mod_cast hn0
  have hL : 0 ≤ Real.log (n : ℝ) := by linarith
  have hellr := (bipartite_scale_bounds hK hn2 hn).1
  have hell : 0 < ell n := by exact_mod_cast hellr
  have hlogell : 0 ≤ Real.log (ell n : ℝ) := Real.log_nonneg (by exact_mod_cast hell)
  have hlog' : Real.log (ell n : ℝ) ^ r ≤ D * Real.log (n : ℝ) ^ r := by
    calc
      _ ≤ ((Real.log K + 1) * Real.log (n : ℝ)) ^ r :=
        Real.rpow_le_rpow hlogell (side_log_bound hK hn0 hlog hell hn.2.1) hr.le
      _ = _ := Real.mul_rpow (by linarith [Real.log_nonneg hK]) hL
  have hnum : (ell n : ℝ) * Real.log n ^ r + (n : ℝ) * Real.log (ell n) ^ r ≤
      (K + D) * n * Real.log n ^ r := by
    have h1 := mul_le_mul_of_nonneg_right hn.2.1 (Real.rpow_nonneg hL r)
    have h2 := mul_le_mul_of_nonneg_left hlog' hn0r.le
    nlinarith
  have hbound' : Real.log (n : ℝ) ^ r ≤ ε * K⁻¹ / (K + D) * (n : ℝ) ^ (1 - θ) := by
    simpa only [Function.comp_apply, Real.norm_of_nonneg (Real.rpow_nonneg hL _),
      Real.norm_of_nonneg (Real.rpow_nonneg hn0r.le _)] using hbound
  have he : (n : ℝ) ^ (1 - θ) * n = (n : ℝ) ^ (2 - θ) := by
    rw [← Real.rpow_add_one hn0r.ne']
    congr 1
    ring
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ (ell n : ℝ) * Real.log n ^ r +
    (n : ℝ) * Real.log (ell n) ^ r), Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ m n)]
  calc
    _ ≤ (K + D) * n * Real.log n ^ r := hnum
    _ ≤ (K + D) * n * (ε * K⁻¹ / (K + D) * (n : ℝ) ^ (1 - θ)) := by gcongr
    _ = ε * (K⁻¹ * (n : ℝ) ^ (2 - θ)) := by
      rw [← he]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hn.2.2.1 hε.le

theorem bipartite_error_third_bound {θ K : ℝ} {n ell m : ℕ} (hK : 1 ≤ K) (hn : 2 ≤ n)
    (h : BipartiteScaleWindow θ K n ell m) :
    min (leftAverage ell m) (rightAverage n m) ^ (5 * (7 / 12 : ℝ) - 5) *
        (m : ℝ) ^ 2 / ((ell : ℝ) * n) ≤
      ((K ^ 2)⁻¹ : ℝ) ^ (-25 / 12 : ℝ) * K ^ 3 * (n : ℝ) ^ (-(1 - θ) / 12) := by
  have hK0 : 0 < K := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hb := bipartite_scale_bounds hK hn h
  have hlo : 0 < (K ^ 2)⁻¹ * (n : ℝ) ^ (1 - θ) := by positivity
  have hmin := le_min hb.2.1 hb.2.2.2.1
  have hp := Real.rpow_le_rpow_of_nonpos hlo hmin (by norm_num : (-25 / 12 : ℝ) ≤ 0)
  have hm0 : 0 ≤ (m : ℝ) := by positivity
  have hρ0 : 0 ≤ bipartiteDensity ell n m := by unfold bipartiteDensity; positivity
  have hρm := mul_le_mul hb.2.2.2.2 h.2.2.2 hm0 (by positivity : 0 ≤ K ^ 2 * (n : ℝ) ^ (-θ))
  have he : min (leftAverage ell m) (rightAverage n m) ^ (-25 / 12 : ℝ) *
      (m : ℝ) ^ 2 / ((ell : ℝ) * n) =
      min (leftAverage ell m) (rightAverage n m) ^ (-25 / 12 : ℝ) *
        (bipartiteDensity ell n m * m) := by unfold bipartiteDensity; ring
  rw [show (5 * (7 / 12) - 5 : ℝ) = -25 / 12 by norm_num]
  rw [he]
  calc
    _ ≤ ((K ^ 2)⁻¹ * (n : ℝ) ^ (1 - θ)) ^ (-25 / 12 : ℝ) *
        ((K ^ 2 * (n : ℝ) ^ (-θ)) * (K * (n : ℝ) ^ (2 - θ))) :=
      mul_le_mul hp hρm (mul_nonneg hρ0 hm0) (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hn0.le]
      calc
        _ = ((K ^ 2)⁻¹ : ℝ) ^ (-25 / 12 : ℝ) * K ^ 3 *
            ((n : ℝ) ^ ((1 - θ) * (-25 / 12)) * (n : ℝ) ^ (-θ) * (n : ℝ) ^ (2 - θ)) := by ring
        _ = _ := by
          rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
          congr 2
          ring

theorem eventually_bipartite_scale_domain (θ K μ₀ : ℝ)
    (hθ : 0 < θ) (hK : 1 ≤ K) (hμ₀ : 0 < μ₀) :
    ∀ᶠ n : ℕ in atTop, ∀ ell m : ℕ, BipartiteScaleWindow θ K n ell m →
      0 < ell ∧ m ≤ ell * n ∧ bipartiteDensity ell n m < μ₀ ∧
        0 < bipartiteErrorScale (7 / 12) ell n m := by
  have hK0 : 0 < K := by linarith
  have hu : Tendsto (fun n : ℕ => K ^ 2 * (n : ℝ) ^ (-θ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using ((tendsto_rpow_neg_atTop hθ).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (K ^ 2)
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    hu.eventually (eventually_lt_nhds (lt_min hμ₀ zero_lt_one))] with n hn hsmall
  intro ell m hm
  have hb := bipartite_scale_bounds hK hn hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hav : 0 < (K ^ 2)⁻¹ * (n : ℝ) ^ (1 - θ) := by positivity
  have ha : 0 < leftAverage ell m := hav.trans_le hb.2.1
  have hb' : 0 < rightAverage n m := hav.trans_le hb.2.2.2.1
  have hm0 : (0 : ℝ) < m := (by positivity : 0 < K⁻¹ * (n : ℝ) ^ (2 - θ)).trans_le hm.2.2.1
  refine ⟨by exact_mod_cast hb.1, ?_, hb.2.2.2.2.trans_lt (hsmall.trans_le (min_le_left _ _)), ?_⟩
  · have hρ : bipartiteDensity ell n m ≤ 1 :=
      hb.2.2.2.2.trans (hsmall.trans_le (min_le_right _ _)).le
    have h := (div_le_iff₀ (mul_pos hb.1 hn0)).mp hρ
    simp only [one_mul] at h
    exact_mod_cast h
  · unfold bipartiteErrorScale
    exact add_pos_of_nonneg_of_pos (by positivity) (div_pos
      (mul_pos (Real.rpow_pos_of_pos (lt_min ha hb') _) (sq_pos_of_pos hm0))
        (mul_pos hb.1 hn0))

theorem eventually_bipartite_error_small (θ K ε : ℝ)
    (hθ : θ < 1) (hK : 1 ≤ K) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ ell m : ℕ, BipartiteScaleWindow θ K n ell m →
      bipartiteErrorScale (7 / 12) ell n m ≤ ε := by
  have hK0 : 0 < K := by linarith
  have hn := tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog : Tendsto (fun n : ℕ => Real.log n ^ 2 / Real.sqrt n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_two, Real.sqrt_eq_rpow] using
      ((isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp hn)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlog.eventually
    (eventually_lt_nhds (show (0 : ℝ) < ε / 3 by positivity)))
  have ht : Tendsto (fun n : ℕ => ((K ^ 2)⁻¹ : ℝ) ^ (-25 / 12 : ℝ) * K ^ 3 *
      (n : ℝ) ^ (-(1 - θ) / 12)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_div, mul_zero] using
      ((tendsto_rpow_neg_atTop (show 0 < (1 - θ) / 12 by linarith)).comp hn).const_mul
        (((K ^ 2)⁻¹ : ℝ) ^ (-25 / 12 : ℝ) * K ^ 3)
  filter_upwards [eventually_ge_atTop (2 : ℕ), eventually_ge_atTop N,
    hn.eventually (eventually_ge_atTop (K * N)),
    ht.eventually (eventually_lt_nhds (show (0 : ℝ) < ε / 3 by positivity))]
      with n hn2 hnN hnsize hthird
  intro ell m hm
  have hellN : N ≤ ell := by
    have hh : (N : ℝ) ≤ (n : ℝ) / K := (le_div_iff₀ hK0).mpr (by nlinarith)
    exact_mod_cast hh.trans hm.1
  have htbound := bipartite_error_third_bound hK hn2 hm
  unfold bipartiteErrorScale
  linarith [hN ell hellN, hN n hnN]

end MajorityDynamics.Probability.NeighborhoodBulk
