import MajorityDynamics.Literature.RandomGraph.JumblednessAnalysis
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter Topology
namespace MajorityDynamics.Literature.RandomGraph

/-- The degree-error envelope tends to zero uniformly over all densities
with `log N ^ 2 ≤ p * N`. The polynomial prefactor may be arbitrary. -/
lemma tendsto_pow_mul_exp_neg_log_sq (k : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ k * Real.exp (-c * Real.log (N : ℝ) ^ 2))
      atTop (𝓝 0) := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hl := Real.tendsto_log_atTop.comp hn
  have he : Tendsto (fun N : ℕ => Real.exp (-Real.log (N : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hl)
  apply squeeze_zero' (Filter.Eventually.of_forall fun N => by positivity) ?_ he
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    hl.eventually_ge_atTop (((k : ℝ) + 1) / c)] with N hN hlog
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hl0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hcL : (k : ℝ) + 1 ≤ c * Real.log (N : ℝ) := by
    have hh := (div_le_iff₀ hc).mp hlog
    change (k : ℝ) + 1 ≤ Real.log (N : ℝ) * c at hh
    nlinarith
  have hpow : (N : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log (N : ℝ)) := by
    rw [Real.exp_nat_mul, Real.exp_log hN0]
  rw [hpow, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hcL hl0]

lemma tendsto_pow_mul_exp_neg_linear (k : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ k * Real.exp (-c * N)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) c hc).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  change Tendsto (fun N : ℕ => (N : ℝ) ^ (k : ℝ) * Real.exp (-c * N)) atTop (𝓝 0) at h
  simpa only [Real.rpow_natCast] using h

lemma tendsto_pow_mul_exp_neg_log (k : ℕ) {c : ℝ} (hc : (k : ℝ) < c) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ k * Real.exp (-c * Real.log (N : ℝ)))
      atTop (𝓝 0) := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hl := Real.tendsto_log_atTop.comp hn
  have ht : Tendsto (fun N : ℕ => ((k : ℝ) - c) * Real.log (N : ℝ)) atTop atBot :=
    hl.const_mul_atTop_of_neg (by linarith)
  apply (Real.tendsto_exp_atBot.comp ht).congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  change Real.exp (((k : ℝ) - c) * Real.log (N : ℝ)) = _
  rw [show ((k : ℝ) - c) * Real.log (N : ℝ) =
    (k : ℝ) * Real.log (N : ℝ) + -c * Real.log (N : ℝ) by ring,
    Real.exp_add, Real.exp_nat_mul, Real.exp_log hN0]

end MajorityDynamics.Literature.RandomGraph
