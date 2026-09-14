import MajorityDynamics.Paper.CleanupAsymptotics

/-! Cleanup from a lead at any stopping day. Only the density lower bound
is used; the proportional upper bound plays no role. -/
noncomputable section
open Filter Topology
namespace MajorityDynamics.Paper

/-- A finite sufficient condition for cleanup on the actual graph and coloring. -/
theorem cleanup_after_lead_finite {N : ℕ} (G : Graph N) (c : Coloring N)
    (K : ℕ) (p : unitInterval) (CJ : ℝ) (hCJ : 0 < CJ)
    (hpN : 0 < (p : ℝ) * N)
    (hlog : 10 * CJ ≤ Real.log N)
    (hq : 16 * CJ ^ 2 / ((p : ℝ) * N) ≤ 1)
    (hfinal : (16 * CJ ^ 2 / ((p : ℝ) * N)) ^ K * ((N : ℝ) / 5) < 1)
    (hps : G ∈ pseudorandomEvent p CJ)
    (hexp : (N : ℝ) / Real.sqrt ((p : ℝ) * N) * Real.log N ≤ lead c) :
    ∀ v, (nextColoring G)^[K + 1] c v = false := by
  let β := CJ * Real.sqrt ((p : ℝ) * N)
  have hspos := Real.sqrt_pos.mpr hpN
  have hsquare := Real.sq_sqrt hpN.le
  have hβ : 0 < β := mul_pos hCJ hspos
  have hthreshold : 10 * β ≤ (p : ℝ) * lead c := by
    have hp : 0 ≤ (p : ℝ) := p.property.1
    have h1 := mul_le_mul_of_nonneg_left hexp hp
    have h2 := mul_le_mul_of_nonneg_left hlog (le_of_lt hspos)
    have heq : (p : ℝ) * ((N : ℝ) / Real.sqrt ((p : ℝ) * N) * Real.log N) =
        Real.sqrt ((p : ℝ) * N) * Real.log N := by
      field_simp
      nlinarith
    change (p : ℝ) * ((N : ℝ) / Real.sqrt ((p : ℝ) * N) * Real.log N) ≤
      (p : ℝ) * lead c at h1
    rw [heq] at h1
    dsimp [β]
    nlinarith
  have hratio : 16 * β ^ 2 / ((p : ℝ) * N) ^ 2 = 16 * CJ ^ 2 / ((p : ℝ) * N) := by
    dsimp [β]
    rw [mul_pow, hsquare]
    field_simp
  have hj : Jumbled G p β := hps.2
  have hjump := jumbled_majority_jump G c p β hβ hj hthreshold
  have hiter := majority_iterate_bound G (nextColoring G c) p β hpN hj hps.1 hjump
    (by simpa only [hratio] using hq) (K)
  rw [hratio] at hiter
  have hzero := (minus_card_lt_one_iff _).mp (hiter.trans_lt hfinal)
  simpa only [← Function.iterate_succ_apply] using hzero

/-- A density-uniform upper bound for the cleanup contraction factor. -/
theorem cleanup_ratio_lower_bound {N : ℕ} (θ T CJ : ℝ) (p : unitInterval)
    (hN : 0 < (N : ℝ)) (hT : 0 < T) (hCJ : 0 < CJ)
    (hdensity : T⁻¹ * (N : ℝ) ^ (-θ) < (p : ℝ)) :
    0 < (p : ℝ) * N ∧
      16 * CJ ^ 2 / ((p : ℝ) * N) ≤
        (16 * CJ ^ 2 * T) * (N : ℝ) ^ (-(1 - θ)) := by
  have hpow : 0 < (N : ℝ) ^ (1 - θ) := Real.rpow_pos_of_pos hN _
  have hbase : T⁻¹ * (N : ℝ) ^ (1 - θ) < (p : ℝ) * N := by
    have h := mul_lt_mul_of_pos_right hdensity hN
    have heq : (N : ℝ) ^ (1 - θ) = (N : ℝ) ^ (-θ) * N := by
      calc
        _ = (N : ℝ) ^ (-θ + 1) := by congr 1; ring
        _ = _ := Real.rpow_add_one hN.ne' (-θ)
    rwa [mul_assoc, ← heq] at h
  have hpN : 0 < (p : ℝ) * N := lt_trans (mul_pos (inv_pos.mpr hT) hpow) hbase
  refine ⟨hpN, (div_le_iff₀ hpN).mpr ?_⟩
  have hnonneg : 0 ≤ (16 * CJ ^ 2 * T) * (N : ℝ) ^ (-(1 - θ)) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hbase.le hnonneg
  have heq : (16 * CJ ^ 2 * T * (N : ℝ) ^ (-(1 - θ))) *
      (T⁻¹ * (N : ℝ) ^ (1 - θ)) = 16 * CJ ^ 2 := by
    rw [Real.rpow_neg hN.le]
    field_simp
  rwa [heq] at hmul

/-- Section 6 cleanup, with no provisional mathematical axioms. -/
theorem uniform_cleanup_after_lead (θ T CJ : ℝ) (hθ : θ < 1)
    (hT : 1 < T) (hCJ : 0 < CJ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (p : unitInterval) (G : Graph N) (c : Coloring N),
      T⁻¹ * (N : ℝ) ^ (-θ) < (p : ℝ) → G ∈ pseudorandomEvent p CJ →
      (N : ℝ) / Real.sqrt ((p : ℝ) * N) * Real.log N ≤ lead c →
      ∀ v, (nextColoring G)^[expansionDay θ + 1] c v = false := by
  have hT0 : 0 < T := by linarith
  let a := 1 - θ
  let K := expansionDay θ
  let A := 16 * CJ ^ 2 * T
  have ha : 0 < a := by dsimp [a]; linarith
  have hAK : 0 < a * (K : ℝ) - 1 := by
    have h := expansionDay_exponent hθ
    dsimp [a, K]
    nlinarith
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun N : ℕ => A * (N : ℝ) ^ (-a)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop ha).comp hnat).const_mul A
  have hfinal : Tendsto (fun N : ℕ => (A ^ K / 5) * (N : ℝ) ^ (-(a * K - 1)))
      atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hAK).comp hnat).const_mul (A ^ K / 5)
  have hlog := (Real.tendsto_log_atTop.comp hnat).eventually_ge_atTop (10 * CJ)
  have hratio1 := hratio.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hfinal1 := hfinal.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hevent : ∀ᶠ N : ℕ in atTop,
      ∀ (p : unitInterval) (G : Graph N) (c : Coloring N),
        T⁻¹ * (N : ℝ) ^ (-θ) < (p : ℝ) → G ∈ pseudorandomEvent p CJ →
          (N : ℝ) / Real.sqrt ((p : ℝ) * N) * Real.log N ≤ lead c →
          ∀ v, (nextColoring G)^[expansionDay θ + 1] c v = false := by
    filter_upwards [eventually_ge_atTop (1 : ℕ), hlog, hratio1, hfinal1]
      with N hN hlogN hratioN hfinalN
    intro p G c hdensity hps hexp
    have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
    obtain ⟨hpN, hbound⟩ := cleanup_ratio_lower_bound θ T CJ p hN0 hT0 hCJ hdensity
    have hq : 16 * CJ ^ 2 / ((p : ℝ) * N) ≤ 1 := hbound.trans hratioN.le
    have hq0 : 0 ≤ 16 * CJ ^ 2 / ((p : ℝ) * N) := by positivity
    have hpower := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq0 hbound K)
      (by positivity : 0 ≤ (N : ℝ) / 5)
    rw [cleanup_power_identity A a K hN0] at hpower
    exact cleanup_after_lead_finite G c K p CJ hCJ hpN hlogN hq
      (hpower.trans_lt hfinalN) hps hexp
  exact eventually_atTop.mp hevent

theorem nextColoring_allplus {N : ℕ} (G : Graph N) (c : Coloring N)
    (hc : ∀ v, c v = false) : ∀ v, nextColoring G c v = false := by
  intro v
  have hs : 0 ≤ neighborSum G c v := by
    unfold neighborSum
    apply Finset.sum_nonneg
    intro w _
    simp only [hc w, opinion, Bool.false_eq_true, if_false]
    positivity
  simp only [nextColoring, not_lt.mpr hs, if_false, hc v, ite_self]

theorem iterate_allplus {N : ℕ} (G : Graph N) (c : Coloring N)
    (hc : ∀ v, c v = false) (k : ℕ) : ∀ v, (nextColoring G)^[k] c v = false := by
  induction k with
  | zero => exact hc
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact nextColoring_allplus G _ ih

theorem allplus_later_day {N : ℕ} (G : Graph N) (c : Coloring N) {d D : ℕ}
    (hd : 1 ≤ d) (hD : d ≤ D) (h : ∀ v, coloringOnDay G c d v = false) :
    ∀ v, coloringOnDay G c D v = false := by
  have he : coloringOnDay G c D = (nextColoring G)^[D - d] (coloringOnDay G c d) := by
    unfold coloringOnDay
    rw [← Function.iterate_add_apply]
    congr 1
    omega
  rw [he]
  exact iterate_allplus G _ h (D - d)

/-- A lead on any day at most H gives unanimity on day 2H+1, uniformly
over all allowed densities. -/
theorem uniform_cleanup_at_stopping_day (θ T CJ : ℝ) (hθ : θ < 1)
    (hT : 1 < T) (hCJ : 0 < CJ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (p : unitInterval) (G : Graph N) (c : Coloring N),
      T⁻¹ * (N : ℝ) ^ (-θ) < (p : ℝ) → G ∈ pseudorandomEvent p CJ →
      ∀ d : ℕ, 1 ≤ d → d ≤ expansionDay θ →
      (N : ℝ) / Real.sqrt ((p : ℝ) * N) * Real.log N ≤ lead (coloringOnDay G c d) →
      ∀ v, coloringOnDay G c (2 * expansionDay θ + 1) v = false := by
  obtain ⟨N₀, hN₀⟩ := uniform_cleanup_after_lead θ T CJ hθ hT hCJ
  refine ⟨N₀, ?_⟩
  intro N hN p G c hp hps d hd hdH hlead
  have h := hN₀ N hN p G (coloringOnDay G c d) hp hps hlead
  have he : coloringOnDay G c (d + expansionDay θ + 1) =
      (nextColoring G)^[expansionDay θ + 1] (coloringOnDay G c d) := by
    unfold coloringOnDay
    rw [← Function.iterate_add_apply]
    congr 1
    omega
  have hday : ∀ v, coloringOnDay G c (d + expansionDay θ + 1) v = false := by
    rwa [he]
  exact allplus_later_day G c (by omega) (by omega) hday

end MajorityDynamics.Paper
