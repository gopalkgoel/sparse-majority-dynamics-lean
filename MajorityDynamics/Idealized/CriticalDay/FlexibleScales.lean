import MajorityDynamics.Idealized.CriticalDay.FlexibleStopping
noncomputable section
open Filter Topology
namespace MajorityDynamics.Idealized.CriticalDay
open Binomial.Approximation LinearResponse

theorem first_response_weight_flexible {N : ℕ} {p : ℝ}
    (hp : 0 < p) (hN : 0 < N) (r : ℝ) :
    (betaScale N p 0 * Real.sqrt (p*N)) * Real.sqrt (p*N)^(1-r) =
      (p*N)^(1-r/2)/Real.sqrt N := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hx : 0 < p*N := mul_pos hp hn
  rw [response_scale_rpow hp.le, Real.sqrt_eq_rpow (p*N), ← Real.rpow_mul hx.le,
    div_mul_eq_mul_div, ← Real.rpow_add hx]
  congr 2
  norm_num
  ring

theorem stopping_response_weight_flexible {N : ℕ} {p : ℝ}
    (hp : 0 < p) (hN : 0 < N) (j : ℕ) (r : ℝ) :
    (betaScale N p j * Real.sqrt (p*N)) * Real.sqrt (p*N)^(1-r) =
      (p*N)^(((j : ℝ) + 2-r)/2)/Real.sqrt N := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hx : 0 < p*N := mul_pos hp hn
  rw [response_scale_rpow hp.le, Real.sqrt_eq_rpow (p*N), ← Real.rpow_mul hx.le,
    div_mul_eq_mul_div, ← Real.rpow_add hx]
  congr 2
  ring

theorem eventually_flexible_stopping_scales (θ T r : ℝ) (H : ℕ)
    (hr : 0 < r) (hr1 : r ≤ 1) (hθ : θ < 1) (hT : 1 < T) (hH : 1 < (H : ℝ) * (1 - θ)) :
    ∀ᶠ N : ℕ in atTop, 0 < N ∧ ∀ p : Binomial.Probability,
      SparseRange θ T N p →
      1 ≤ scale N p ∧
      (betaScale N p 0 * scale N p) * (scale N p) ^ (1-r) < 1 ∧
      1 ≤ betaScale N p H * scale N p := by
  have hT0 : 0 < T := by linarith
  have hn := tendsto_natCast_atTop_atTop (R := ℝ)
  have hu : Tendsto (fun N : ℕ => T ^ (1-r/2) *
      (N : ℝ) ^ (-r/4)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_div, mul_zero] using
      ((tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < r/4)).comp hn).const_mul
        (T ^ (1-r/2))
  have hex : 0 < (1 - θ) * (((H : ℝ) + 1) / 2) - 1 / 2 := by nlinarith
  have hl : Tendsto (fun N : ℕ => (T⁻¹) ^ (((H : ℝ) + 1) / 2) *
      (N : ℝ) ^ ((1 - θ) * (((H : ℝ) + 1) / 2) - 1 / 2)) atTop atTop :=
    ((tendsto_rpow_atTop hex).comp hn).const_mul_atTop (by positivity)
  have hx : Tendsto (fun N : ℕ => T⁻¹ * (N : ℝ) ^ (1 - θ)) atTop atTop :=
    ((tendsto_rpow_atTop (by linarith : 0 < 1 - θ)).comp hn).const_mul_atTop (by positivity)
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    hu.eventually (eventually_lt_nhds zero_lt_one), hl.eventually_ge_atTop 1,
    hx.eventually_ge_atTop 1] with N hN hu hl hx
  refine ⟨by omega, ?_⟩
  intro p hp
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp0 : 0 < (p : ℝ) := p.property.1
  have hbase : 1 ≤ (p : ℝ) * N := by
    have hh := mul_le_mul_of_nonneg_right hp.1.le hn0.le
    have he : (N : ℝ) ^ (-θ) * N = (N : ℝ) ^ (1 - θ) := by
      rw [← Real.rpow_add_one hn0.ne']; congr 1; ring
    rw [mul_assoc, he] at hh
    exact hx.trans hh
  refine ⟨?_, ?_, ?_⟩
  · exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by simpa using hbase)
  · rw [show scale N p = Real.sqrt ((p : ℝ) * N) from rfl,
      first_response_weight_flexible hp0 (by omega) r]
    have hh := (degree_power_band_bounds (by omega) hT0
      (by linarith : (0 : ℝ) ≤ 1-r/2) hp.1 hp.2).2
    have he : (1-(1/2:ℝ))*(1-r/2)-1/2 = -r/4 := by ring
    rw [he] at hh
    exact hh.trans_lt (by simpa only [neg_div] using hu)
  · rw [show scale N p = Real.sqrt ((p : ℝ) * N) from rfl, response_scale_rpow hp0.le]
    exact hl.trans (degree_power_band_bounds (by omega) hT0 (by positivity) hp.1 hp.2).1

/-- The endpoint only needs to reach the stopping threshold, rather than one.
This sharper form permits a smaller deterministic stopping horizon. -/
theorem eventually_flexible_stopping_scales_at (θ T r : ℝ) (H : ℕ)
    (hr : 0 < r) (hr1 : r ≤ 1) (hθ : θ < 1) (hT : 1 < T)
    (hH : 1 < (1-θ)*((H:ℝ)+2-r)) :
    ∀ᶠ N : ℕ in atTop, 0 < N ∧ ∀ p : Binomial.Probability,
      SparseRange θ T N p →
      1 ≤ scale N p ∧
      (betaScale N p 0 * scale N p) * (scale N p) ^ (1-r) < 1 ∧
      scale N p^(r-1) ≤ betaScale N p H * scale N p := by
  have hT0 : 0 < T := by linarith
  have hn := tendsto_natCast_atTop_atTop (R := ℝ)
  have hu : Tendsto (fun N : ℕ => T ^ (1-r/2) *
      (N : ℝ) ^ (-r/4)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_div, mul_zero] using
      ((tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < r/4)).comp hn).const_mul
        (T ^ (1-r/2))
  have hex : 0 < (1 - θ) * (((H : ℝ) + 2-r) / 2) - 1 / 2 := by nlinarith
  have hepos : 0 < ((H : ℝ) + 2-r) / 2 := by
    by_contra hh
    have hnonpos : ((H : ℝ) + 2-r) / 2 ≤ 0 := le_of_not_gt hh
    have hprod := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 1-θ) hnonpos
    linarith
  have hl : Tendsto (fun N : ℕ => (T⁻¹) ^ (((H : ℝ) + 2-r) / 2) *
      (N : ℝ) ^ ((1 - θ) * (((H : ℝ) + 2-r) / 2) - 1 / 2)) atTop atTop :=
    ((tendsto_rpow_atTop hex).comp hn).const_mul_atTop (by positivity)
  have hx : Tendsto (fun N : ℕ => T⁻¹ * (N : ℝ) ^ (1 - θ)) atTop atTop :=
    ((tendsto_rpow_atTop (by linarith : 0 < 1 - θ)).comp hn).const_mul_atTop (by positivity)
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    hu.eventually (eventually_lt_nhds zero_lt_one), hl.eventually_ge_atTop 1,
    hx.eventually_ge_atTop 1] with N hN hu hl hx
  refine ⟨by omega, ?_⟩
  intro p hp
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp0 : 0 < (p : ℝ) := p.property.1
  have hbase : 1 ≤ (p : ℝ) * N := by
    have hh := mul_le_mul_of_nonneg_right hp.1.le hn0.le
    have he : (N : ℝ) ^ (-θ) * N = (N : ℝ) ^ (1 - θ) := by
      rw [← Real.rpow_add_one hn0.ne']; congr 1; ring
    rw [mul_assoc, he] at hh
    exact hx.trans hh
  refine ⟨?_, ?_, ?_⟩
  · exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by simpa using hbase)
  · rw [show scale N p = Real.sqrt ((p : ℝ) * N) from rfl,
      first_response_weight_flexible hp0 (by omega) r]
    have hh := (degree_power_band_bounds (by omega) hT0
      (by linarith : (0 : ℝ) ≤ 1-r/2) hp.1 hp.2).2
    have he : (1-(1/2:ℝ))*(1-r/2)-1/2 = -r/4 := by ring
    rw [he] at hh
    exact hh.trans_lt (by simpa only [neg_div] using hu)
  · have hweight : 1 ≤ (betaScale N p H*scale N p)*scale N p^(1-r) := by
      rw [show scale N p = Real.sqrt ((p : ℝ) * N) from rfl,
        stopping_response_weight_flexible hp0 (by omega) H r]
      exact hl.trans (degree_power_band_bounds (by omega) hT0 hepos.le hp.1 hp.2).1
    have hs0 : 0 < scale N p := Real.sqrt_pos.mpr (mul_pos hp0 hn0)
    have hb : 0 ≤ scale N p^(r-1) := (Real.rpow_pos_of_pos hs0 _).le
    have he : scale N p^(r-1)*scale N p^(1-r) = 1 := by
      rw [← Real.rpow_add hs0]
      simp
    calc
      scale N p^(r-1) = 1*scale N p^(r-1) := by ring
      _ ≤ ((betaScale N p H*scale N p)*scale N p^(1-r))*scale N p^(r-1) :=
        mul_le_mul_of_nonneg_right hweight hb
      _ = (betaScale N p H*scale N p)*(scale N p^(r-1)*scale N p^(1-r)) := by ring
      _ = betaScale N p H*scale N p := by rw [he,mul_one]

/-- Stop later in the subcritical regime when a small inherited rate requires
a smaller permitted overshoot. The index remains bounded uniformly in density. -/
theorem uniform_flexible_stopping_index (θ T r : ℝ) (H : ℕ)
    (hr : 0 < r) (hr1 : r ≤ 1) (hθ : θ < 1) (hT : 1 < T)
    (hH : 1 < (H:ℝ)*(1-θ)) :
    ∀ᶠ N : ℕ in atTop, 0 < N ∧ ∀ p : Binomial.Probability,
      SparseRange θ T N p →
      let s := scale N p
      let t := s^r
      1 ≤ s ∧ 1 ≤ t ∧ ∃ j : ℕ, 0 < j ∧ j ≤ H ∧
        t ≤ (betaScale N p j*s)*s ∧ betaScale N p j*s < t ∧
        ∀ i < j, betaScale N p i*s < s^(r-1) := by
  filter_upwards [eventually_flexible_stopping_scales θ T r H hr hr1 hθ hT hH] with N hN
  refine ⟨hN.1,?_⟩
  intro p hp
  obtain ⟨hs,h0,hH⟩ := hN.2 p hp
  dsimp only
  have hs0 : 0 < scale N p := zero_lt_one.trans_le hs
  have hb : 0 < scale N p^(r-1) := Real.rpow_pos_of_pos hs0 _
  have he : scale N p^(r-1)*scale N p^(1-r) = 1 := by
    rw [← Real.rpow_add hs0]
    simp
  have hf0 : betaScale N p 0*scale N p < scale N p^(r-1) := by
    have hh := mul_lt_mul_of_pos_right h0 hb
    have hid : ((betaScale N p 0*scale N p)*scale N p^(1-r))*scale N p^(r-1) =
        betaScale N p 0*scale N p := by
      calc
        _ = (betaScale N p 0*scale N p)*(scale N p^(r-1)*scale N p^(1-r)) := by ring
        _ = _ := by rw [he,mul_one]
    simpa only [hid,one_mul] using hh
  have hb1 : scale N p^(r-1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hs (by linarith)
  have hstep : ∀ j, betaScale N p (j+1)*scale N p =
      scale N p*(betaScale N p j*scale N p) := by
    intro j
    unfold betaScale scale
    rw [pow_succ]
    ring
  obtain ⟨j,hj0,hjH,hlo,hhi,hprev⟩ := first_geometric_crossing
    (fun j => betaScale N p j*scale N p) H hs0 hf0 (hb1.trans hH) hstep
  have hid : scale N p*scale N p^(r-1) = scale N p^r := by
    rw [mul_comm, ← Real.rpow_add_one hs0.ne']
    congr 1
    ring
  refine ⟨hs,Real.one_le_rpow hs hr.le,j,hj0,hjH,?_,?_,hprev⟩
  · have hh := mul_le_mul_of_nonneg_right hlo hs0.le
    simpa only [mul_comm (scale N p^(r-1)) (scale N p),hid] using hh
  · simpa only [hid] using hhi

/-- Flexible first crossing with the sharp endpoint hypothesis. -/
theorem uniform_flexible_stopping_index_at (θ T r : ℝ) (H : ℕ)
    (hr : 0 < r) (hr1 : r ≤ 1) (hθ : θ < 1) (hT : 1 < T)
    (hH : 1 < (1-θ)*((H:ℝ)+2-r)) :
    ∀ᶠ N : ℕ in atTop, 0 < N ∧ ∀ p : Binomial.Probability,
      SparseRange θ T N p →
      let s := scale N p
      let t := s^r
      1 ≤ s ∧ 1 ≤ t ∧ ∃ j : ℕ, 0 < j ∧ j ≤ H ∧
        t ≤ (betaScale N p j*s)*s ∧ betaScale N p j*s < t ∧
        ∀ i < j, betaScale N p i*s < s^(r-1) := by
  filter_upwards [eventually_flexible_stopping_scales_at θ T r H hr hr1 hθ hT hH] with N hN
  refine ⟨hN.1,?_⟩
  intro p hp
  obtain ⟨hs,h0,hH⟩ := hN.2 p hp
  dsimp only
  have hs0 : 0 < scale N p := zero_lt_one.trans_le hs
  have hb : 0 < scale N p^(r-1) := Real.rpow_pos_of_pos hs0 _
  have he : scale N p^(r-1)*scale N p^(1-r) = 1 := by
    rw [← Real.rpow_add hs0]
    simp
  have hf0 : betaScale N p 0*scale N p < scale N p^(r-1) := by
    have hh := mul_lt_mul_of_pos_right h0 hb
    have hid : ((betaScale N p 0*scale N p)*scale N p^(1-r))*scale N p^(r-1) =
        betaScale N p 0*scale N p := by
      calc
        _ = (betaScale N p 0*scale N p)*(scale N p^(r-1)*scale N p^(1-r)) := by ring
        _ = _ := by rw [he,mul_one]
    simpa only [hid,one_mul] using hh
  have hstep : ∀ j, betaScale N p (j+1)*scale N p =
      scale N p*(betaScale N p j*scale N p) := by
    intro j
    unfold betaScale scale
    rw [pow_succ]
    ring
  obtain ⟨j,hj0,hjH,hlo,hhi,hprev⟩ := first_geometric_crossing
    (fun j => betaScale N p j*scale N p) H hs0 hf0 hH hstep
  have hid : scale N p*scale N p^(r-1) = scale N p^r := by
    rw [mul_comm, ← Real.rpow_add_one hs0.ne']
    congr 1
    ring
  refine ⟨hs,Real.one_le_rpow hs hr.le,j,hj0,hjH,?_,?_,hprev⟩
  · have hh := mul_le_mul_of_nonneg_right hlo hs0.le
    simpa only [mul_comm (scale N p^(r-1)) (scale N p),hid] using hh
  · simpa only [hid] using hhi

/-- The stopping rule can be chosen after *any* positive inherited polynomial
rate. This eliminates a requirement to preserve a particular sharp error rate. -/
theorem choose_flexible_stopping_exponent {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1/4 ∧ r/4 < δ := by
  refine ⟨min (1/4) δ,lt_min (by norm_num) hδ,min_le_left _ _,?_⟩
  have hh := min_le_right (1/4:ℝ) δ
  linarith

/-- Choose the stopping exponent after the inherited rate while also staying
inside a fixed positive timing margin. -/
theorem choose_flexible_stopping_exponent_before {θ δ : ℝ} (H : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hδ : 0 < δ)
    (hH : 1 < (H:ℝ)*(1-θ)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1/4 ∧ r/4 < δ ∧ 1 < (1-θ)*((H:ℝ)-r) := by
  let m := (H:ℝ)*(1-θ)-1
  have hm : 0 < m := by dsimp [m]; linarith
  let r := min (1/4) (min δ (m/2))
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (by norm_num) (lt_min hδ (half_pos hm))
  have hr4 : r ≤ 1/4 := by dsimp [r]; exact min_le_left _ _
  have hrδ : r ≤ δ := by
    dsimp [r]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hrm : r ≤ m/2 := by
    dsimp [r]
    exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r,hr,hr4,by linarith,?_⟩
  have hα : 0 < 1-θ := by linarith
  have hα1 : 1-θ < 1 := by linarith
  have hαr : (1-θ)*r < m := by nlinarith
  dsimp [m] at hαr
  nlinarith

/-- Complete terminal error absorption with any positive polynomial inherited
rate, provided the freely chosen amplification exponent is small enough. -/
theorem uniform_flexible_terminal_budget (θ T r δ C ε : ℝ) (k : ℕ)
    (hθ : θ < 1) (hT : 0 < T) (hr : 0 < r) (hr3 : r ≤ 1/3)
    (hgap : r/4 < δ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Binomial.Probability, SparseRange θ T N p →
      let s := scale N p
      let t := s^r
      ∀ a e : ℝ, 0 < a → t ≤ a*s → a ≤ t → 0 ≤ e →
        e ≤ C*(N:ℝ)^(-δ) →
        ((1+a+a^2)/s*Real.log N ^ k+a*e)/min a 1 ≤ ε := by
  filter_upwards [eventually_ge_atTop (1:ℕ),
    RowLimits.density_scale_lower_power_sparse θ T 1 0 hθ hT zero_lt_one,
    sparse_scale_rpow_log_small θ T r (ε/6) k hθ hT hr (by positivity),
    sparse_polynomial_amplification θ T r δ C (ε/2) hT hr hgap hC (by positivity)]
    with N hN hs hlog herr
  intro p hp
  dsimp only
  intro a e ha halo hahi he heB
  have hs1 : 1 ≤ scale N p := by simpa using hs p hp
  have ht1 : 1 ≤ scale N p^r := Real.one_le_rpow hs1 hr.le
  have hcube : (scale N p^r)^3 ≤ scale N p := by
    rw [← Real.rpow_mul_natCast (zero_le_one.trans hs1)]
    have hh := Real.rpow_le_rpow_of_exponent_le hs1 (show r*(3:ℕ) ≤ 1 by
      norm_num
      linarith)
    simpa only [Real.rpow_one] using hh
  have hl : 0 ≤ Real.log N ^ k := pow_nonneg
    (Real.log_nonneg (by exact_mod_cast hN)) _
  have hh := flexible_stopping_error ht1 hcube ha halo hahi he hl
  have h1 := mul_le_mul_of_nonneg_left (hlog p hp) (by norm_num : (0:ℝ) ≤ 3)
  rw [← mul_div_assoc] at h1
  have h2 := herr p hp e heB
  linarith

end MajorityDynamics.Idealized.CriticalDay
