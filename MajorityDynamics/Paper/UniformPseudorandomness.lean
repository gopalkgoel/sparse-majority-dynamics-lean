import MajorityDynamics.Paper.Pseudorandomness

/-! The pseudorandomness phase only needs the polynomial density lower bound
and the fixed upper cap from the jumbledness source. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace MajorityDynamics.Paper

theorem expectedDegree_lower_only {N : ℕ} (θ T : ℝ) (p : unitInterval)
    (hN : 0 < (N : ℝ)) (hp : T⁻¹ * (N : ℝ) ^ (-θ) < (p : ℝ)) :
    T⁻¹ * (N : ℝ) ^ (1 - θ) < (p : ℝ) * N := by
  have hh := mul_lt_mul_of_pos_right hp hN
  have heq : (N : ℝ) ^ (1 - θ) = (N : ℝ) ^ (-θ) * N := by
    rw [show 1 - θ = -θ + 1 by ring, Real.rpow_add_one hN.ne']
  rwa [mul_assoc, ← heq] at hh

theorem lower_density_eventually_log_degree (θ T : ℝ) (hθ : θ < 1) (hT : 0 < T) :
    ∀ᶠ N : ℕ in atTop, ∀ p : unitInterval,
      T⁻¹ * (N : ℝ) ^ (-θ) < (p : ℝ) →
      0 < (p : ℝ) ∧ (Real.log (N : ℝ)) ^ 2 ≤ (p : ℝ) * N := by
  have hn := tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog := ((isLittleO_log_rpow_rpow_atTop 2 (by linarith : 0 < 1 - θ)).comp_tendsto
    hn).bound (inv_pos.mpr hT)
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlog] with N hN hlog
  intro p hp
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨(by positivity : 0 < T⁻¹ * (N : ℝ) ^ (-θ)).trans hp, ?_⟩
  have hl : Real.log (N : ℝ) ^ 2 ≤ T⁻¹ * (N : ℝ) ^ (1 - θ) := by
    simpa only [Function.comp_apply, Real.rpow_two, Real.norm_of_nonneg (sq_nonneg _),
      Real.norm_of_nonneg (Real.rpow_nonneg hn0.le _)] using hlog
  exact hl.trans (expectedDegree_lower_only θ T p hn0 hp).le

theorem minimumDegree_highProbability_lower (θ T : ℝ) (hθ : θ < 1) (hT : 0 < T)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : unitInterval,
      T⁻¹ * (N : ℝ) ^ (-θ) < (p : ℝ) →
      graphLaw N p {G | minimumDegree G p}ᶜ ≤ ENNReal.ofReal ε := by
  have hsmall := (degreeFailureEnvelope_tendsto θ T hθ hT).eventually
    (eventually_lt_nhds hε)
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop (20 : ℕ), hsmall,
    lower_density_eventually_log_degree θ T hθ hT] with N hN hsmall hreg
  intro p hp
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have henv : (N : ℝ) * Real.exp (-((p : ℝ) * N) / 1000) ≤ degreeFailureEnvelope θ T N := by
    apply mul_le_mul_of_nonneg_left _ hn0.le
    apply Real.exp_le_exp.mpr
    have hh := expectedDegree_lower_only θ T p hn0 hp
    linarith
  exact (minimumDegree_failure_bound_of_chernoff Literature.bernoulli_lower_tail
    N hN p (hreg p hp).1).trans (ENNReal.ofReal_le_ofReal (henv.trans hsmall.le))

theorem pseudorandomness_lower_only :
    ∃ CJ : ℝ, 0 < CJ ∧ ∀ θ T : ℝ, θ < 1 → 0 < T →
      ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : unitInterval,
        T⁻¹ * (N : ℝ) ^ (-θ) < (p : ℝ) → (p : ℝ) ≤ 99 / 100 →
        graphLaw N p (pseudorandomEvent p CJ)ᶜ ≤ ENNReal.ofReal ε := by
  obtain ⟨CJ, hCJ, hJ⟩ := Literature.random_graph_jumbledness
  refine ⟨CJ, hCJ, ?_⟩
  intro θ T hθ hT ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨ND, hD⟩ := minimumDegree_highProbability_lower θ T hθ hT (ε / 2) hhalf
  obtain ⟨NJ, hJ⟩ := hJ (ε / 2) hhalf
  obtain ⟨NR, hR⟩ := eventually_atTop.mp (lower_density_eventually_log_degree θ T hθ hT)
  refine ⟨max ND (max NJ NR), ?_⟩
  intro N hN p hp hcap
  have hreg := hR N (by omega) p hp
  have hdegree := hD N (by omega) p hp
  have hjumbled := hJ N (by omega) p hcap hreg.2
  have he : (pseudorandomEvent p CJ)ᶜ = {G : Graph N | minimumDegree G p}ᶜ ∪
      {G | Jumbled G p (CJ * Real.sqrt ((p : ℝ) * N))}ᶜ := by
    ext G
    simp only [pseudorandomEvent, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_union]
    tauto
  rw [he]
  refine (measure_union_le _ _).trans ((add_le_add hdegree hjumbled).trans ?_)
  rw [← ENNReal.ofReal_add hhalf.le hhalf.le, add_halves]

end MajorityDynamics.Paper
