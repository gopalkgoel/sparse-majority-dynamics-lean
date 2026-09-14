import MajorityDynamics.Paper.Cleanup
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Discharging the deterministic cleanup input

The density lower bound makes the contraction factor tend to zero. For
`K = expansionDay θ`, the strict inequality `1 < K * (1 - θ)` makes `K`
contractions eliminate the remaining vertices, uniformly over the density range.
This proves the exact `DeterministicCleanup` proposition from the scaffold.
-/

noncomputable section
open Filter Topology

namespace MajorityDynamics.Paper

theorem expansionDay_exponent {θ : ℝ} (hθ : θ < 1) :
    1 < (expansionDay θ : ℝ) * (1 - θ) := by
  have ha : 0 < 1 - θ := by linarith
  have hfloor : 1 / (1 - θ) < (expansionDay θ : ℝ) := by
    simpa [expansionDay] using Nat.lt_floor_add_one (1 / (1 - θ))
  exact (div_lt_iff₀ ha).mp hfloor

/-- A density-uniform upper bound for the cleanup contraction factor. -/
theorem cleanup_ratio_bound {N : ℕ} (θ T CJ : ℝ) (p : unitInterval)
    (hN : 0 < (N : ℝ)) (hT : 0 < T) (hCJ : 0 < CJ)
    (hdensity : densityRange θ T N p) :
    0 < (p : ℝ) * N ∧
      16 * CJ ^ 2 / ((p : ℝ) * N) ≤
        (16 * CJ ^ 2 * T) * (N : ℝ) ^ (-(1 - θ)) := by
  have hpow : 0 < (N : ℝ) ^ (1 - θ) := Real.rpow_pos_of_pos hN _
  have hbase : T⁻¹ * (N : ℝ) ^ (1 - θ) < (p : ℝ) * N := by
    have h := mul_lt_mul_of_pos_right hdensity.1 hN
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

/-- The scalar estimate controlling the number of vertices after `K` contractions. -/
theorem cleanup_power_identity {N : ℕ} (A a : ℝ) (K : ℕ) (hN : 0 < (N : ℝ)) :
    (A * (N : ℝ) ^ (-a)) ^ K * ((N : ℝ) / 5) =
      (A ^ K / 5) * (N : ℝ) ^ (-(a * K - 1)) := by
  rw [mul_pow, ← Real.rpow_mul_natCast hN.le]
  have hexp : -(a * (K : ℝ) - 1) = (-a) * (K : ℝ) + 1 := by ring
  rw [hexp, Real.rpow_add_one hN.ne']
  ring

/-- Section 6 cleanup, with no provisional mathematical axioms. -/
theorem deterministic_cleanup : DeterministicCleanup := by
  intro θ T CJ _hθlower hθ hT hCJ
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
        densityRange θ T N p → G ∈ pseudorandomEvent p CJ →
          G ∈ expansionEvent θ p c → G ∈ successEvent θ c := by
    filter_upwards [eventually_ge_atTop (1 : ℕ), hlog, hratio1, hfinal1]
      with N hN hlogN hratioN hfinalN
    intro p G c hdensity hps hexp
    have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
    obtain ⟨hpN, hbound⟩ := cleanup_ratio_bound θ T CJ p hN0 hT0 hCJ hdensity
    have hq : 16 * CJ ^ 2 / ((p : ℝ) * N) ≤ 1 := hbound.trans hratioN.le
    have hq0 : 0 ≤ 16 * CJ ^ 2 / ((p : ℝ) * N) := by positivity
    have hpower := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq0 hbound K)
      (by positivity : 0 ≤ (N : ℝ) / 5)
    rw [cleanup_power_identity A a K hN0] at hpower
    exact cleanup_of_numerical_bounds G c θ p CJ hCJ hpN hlogN hq
      (hpower.trans_lt hfinalN) hps hexp
  exact eventually_atTop.mp hevent

end MajorityDynamics.Paper
