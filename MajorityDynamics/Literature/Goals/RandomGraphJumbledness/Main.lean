import MajorityDynamics.Literature.Goals.RandomGraphJumbledness.Statement
import MajorityDynamics.Literature.RandomGraph.JumblednessFinite

/-! L06 — Random-graph jumbledness.
The classical result is Krivelevich–Sudakov (2006), Corollary 2.3,
https://arxiv.org/pdf/math/0503745v1#page=4 , and CKLT21 Lemma 4.1,
https://arxiv.org/pdf/2105.12709v1#page=15 . This new Lean implementation
uses a degree bound, the sharp binomial Bennett exponent, and a union bound
grouped by subset cardinalities. It retains ordered edges and overlapping sets.
The absolute constant is 256, chosen before epsilon and the density parameter.
-/
namespace MajorityDynamics.Literature
open Filter Topology MajorityDynamics.Paper

/-- The full density-uniform literature contract, with no imported theorem axiom. -/
theorem random_graph_jumbledness : RandomGraphJumbledness := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    ((eventually_ge_atTop (2 : ℕ)).and (hlog.eventually_ge_atTop 1))
  apply RandomGraph.jumbledness_of_uniform_failure_bound 256 1 4 (1 / 3)
    (by norm_num) (by norm_num) (by norm_num) N₁
  intro N hN p _ hdegree
  obtain ⟨hN2, hlogN⟩ := hN₁ N hN
  change 1 ≤ Real.log (N : ℝ) at hlogN
  have hd : 1 ≤ (p : ℝ) * N := by nlinarith
  have hp : 0 < (p : ℝ) := by
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith [p.property.1]
  have h := RandomGraph.jumbledness_failure_le hN2 p hp hd
  simpa only [one_mul, show -(1 / 3 : ℝ) * ((p : ℝ) * N) =
    -((p : ℝ) * N) / 3 by ring] using h

/-- info: 'MajorityDynamics.Literature.random_graph_jumbledness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms random_graph_jumbledness

end MajorityDynamics.Literature
