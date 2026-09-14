import MajorityDynamics.Literature.Goals.RandomGraphJumbledness.Statement
import MajorityDynamics.Literature.RandomGraph.JumblednessAsymptotics

open Filter Topology MajorityDynamics.Paper
namespace MajorityDynamics.Literature.RandomGraph

/-- A density-uniform finite failure bound closes the frozen literature
contract. The finite bound is supplied by the checked discrepancy argument. -/
lemma jumbledness_of_uniform_failure_bound (C A B c : ℝ) (hC : 0 < C)
    (hA : 0 ≤ A) (hc : 0 < c) (N₁ : ℕ)
    (hfinite : ∀ N : ℕ, N₁ ≤ N → ∀ p : unitInterval,
      (p : ℝ) ≤ 99 / 100 → Real.log (N : ℝ) ^ 2 ≤ (p : ℝ) * N →
      graphLaw N p {G | Jumbled G p (C * Real.sqrt ((p : ℝ) * N))}ᶜ ≤
        ENNReal.ofReal (A * N * Real.exp (-c * ((p : ℝ) * N)) +
          B * (N : ℝ) ^ 2 * Real.exp (-6 * Real.log (N : ℝ)))) :
    MajorityDynamics.Literature.RandomGraphJumbledness := by
  refine ⟨C, hC, ?_⟩
  intro ε hε
  have hfirst := (tendsto_pow_mul_exp_neg_log_sq 1 hc).const_mul A
  have hsecond := (tendsto_pow_mul_exp_neg_log 2 (c := 6) (by norm_num)).const_mul B
  have hlim : Tendsto (fun N : ℕ =>
      A * N * Real.exp (-c * Real.log (N : ℝ) ^ 2) +
      B * (N : ℝ) ^ 2 * Real.exp (-6 * Real.log (N : ℝ))) atTop (𝓝 0) := by
    simpa only [pow_one, mul_assoc, mul_zero, zero_add] using hfirst.add hsecond
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((eventually_ge_atTop N₁).and (hlim.eventually (eventually_lt_nhds hε)))
  refine ⟨N₀, ?_⟩
  intro N hN p hp hdegree
  obtain ⟨hN₁, hsmall⟩ := hN₀ N hN
  refine (hfinite N hN₁ p hp hdegree).trans (ENNReal.ofReal_le_ofReal ?_)
  have hexp : Real.exp (-c * ((p : ℝ) * N)) ≤
      Real.exp (-c * Real.log (N : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hdegree hc.le]
  have hm := mul_le_mul_of_nonneg_left hexp (show 0 ≤ A * (N : ℝ) by positivity)
  linarith

end MajorityDynamics.Literature.RandomGraph
