import MajorityDynamics.Combinatorics.DegreeRatios.Graph
import MajorityDynamics.Combinatorics.DegreeRatios.Bipartite

noncomputable section
open Filter

namespace MajorityDynamics.Combinatorics.DegreeRatios

theorem degree_ratios : DegreeRatiosTheorem := by
  intro θ T hθlo hθhi hT
  have hT0 : 0 < T := by linarith
  obtain ⟨n₀, hn₀⟩ := (eventually_atTop.mp (eventually_large_parameters θ T hθlo hθhi hT))
  refine ⟨errorConstant T, max 3 n₀, ?_, le_max_left _ _, ?_⟩
  · dsimp [errorConstant, relativeConstant]
    positivity
  · intro n hn p hp
    have hl := hn₀ n (le_trans (le_max_right _ _) hn) p hp
    exact ⟨fun m d hw => graph_estimate_of_large hT hl hw,
      fun ell m d hw => bipartite_estimate_of_large hT hl hw⟩

theorem graph_degree_ratio : GraphDegreeRatioTheorem := by
  intro θ T hθlo hθhi hT
  obtain ⟨C, n₀, hC, hn₀, hall⟩ := degree_ratios θ T hθlo hθhi hT
  exact ⟨C, n₀, hC, hn₀, fun n hn p hp => (hall n hn p hp).1⟩

theorem bipartite_degree_ratio : BipartiteDegreeRatioTheorem := by
  intro θ T hθlo hθhi hT
  obtain ⟨C, n₀, hC, hn₀, hall⟩ := degree_ratios θ T hθlo hθhi hT
  exact ⟨C, n₀, hC, hn₀, fun n hn p hp => (hall n hn p hp).2⟩

/-- Convert an actual positive ratio's log bound to the paper's multiplier. -/
theorem multiplicative_of_log_bound {R p C : ℝ} {n : ℕ} {d : ℤ}
    (hR : 0 < R) (hp : 0 < p)
    (he : |Real.log R + (d : ℝ) * Real.log p - p * n| ≤ C * Real.log n) :
    Real.exp (-C * Real.log n) * p ^ (-d) * Real.exp (p * n) ≤ R ∧
      R ≤ Real.exp (C * Real.log n) * p ^ (-d) * Real.exp (p * n) := by
  have hid (s : ℝ) : Real.exp (s * Real.log n) * p ^ (-d) * Real.exp (p * n) =
      Real.exp (s * Real.log n - (d : ℝ) * Real.log p + p * n) := by
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos hp]
    push_cast
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  constructor
  · calc
      _ = Real.exp (-C * Real.log n - (d : ℝ) * Real.log p + p * n) := hid (-C)
      _ ≤ Real.exp (Real.log R) := Real.exp_le_exp.mpr (by linarith [(abs_le.mp he).1])
      _ = R := Real.exp_log hR
  · calc
      R = Real.exp (Real.log R) := (Real.exp_log hR).symm
      _ ≤ Real.exp (C * Real.log n - (d : ℝ) * Real.log p + p * n) :=
        Real.exp_le_exp.mpr (by linarith [(abs_le.mp he).2])
      _ = _ := (hid C).symm

theorem graph_multiplicative_of_estimate {C p : ℝ} {n : ℕ} {m d : ℤ}
    (hp : 0 < p) (he : GraphEstimate C n p m d) :
    Real.exp (-C * Real.log n) * p ^ (-d) * Real.exp (p * n) ≤ graphRatio n m d ∧
      graphRatio n m d ≤ Real.exp (C * Real.log n) * p ^ (-d) * Real.exp (p * n) :=
  multiplicative_of_log_bound he.2.1 hp he.2.2

theorem bipartite_multiplicative_of_estimate {C p : ℝ} {n : ℕ} {ell m d : ℤ}
    (hp : 0 < p) (he : BipartiteEstimate C n p ell m d) :
    Real.exp (-C * Real.log n) * p ^ (-d) * Real.exp (p * n) ≤ bipartiteRatio n ell m d ∧
      bipartiteRatio n ell m d ≤ Real.exp (C * Real.log n) * p ^ (-d) * Real.exp (p * n) :=
  multiplicative_of_log_bound he.2.1 hp he.2.2

theorem graph_multiplicative :
    ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
      ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 3 ≤ n₀ ∧
        ∀ n : ℕ, n₀ ≤ n → ∀ p : ℝ, DensityWindow θ T n p →
          ∀ m d : ℤ, GraphWindow T n p m d →
            Real.exp (-C * Real.log n) * p ^ (-d) * Real.exp (p * n) ≤ graphRatio n m d ∧
              graphRatio n m d ≤ Real.exp (C * Real.log n) * p ^ (-d) * Real.exp (p * n) := by
  intro θ T hθlo hθhi hT
  obtain ⟨C, n₀, hC, hn₀, hall⟩ := graph_degree_ratio θ T hθlo hθhi hT
  refine ⟨C, n₀, hC, hn₀, ?_⟩
  intro n hn p hp m d hw
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hT0 : 0 < T := by linarith
  have hp0 : 0 < p := (by positivity : 0 < T⁻¹ * (n : ℝ) ^ (-θ)).trans hp.1
  exact graph_multiplicative_of_estimate hp0 (hall n hn p hp m d hw)

theorem bipartite_multiplicative :
    ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
      ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 3 ≤ n₀ ∧
        ∀ n : ℕ, n₀ ≤ n → ∀ p : ℝ, DensityWindow θ T n p →
          ∀ ell m d : ℤ, BipartiteWindow T n p ell m d →
            Real.exp (-C * Real.log n) * p ^ (-d) * Real.exp (p * n) ≤ bipartiteRatio n ell m d ∧
              bipartiteRatio n ell m d ≤ Real.exp (C * Real.log n) * p ^ (-d) * Real.exp (p * n) := by
  intro θ T hθlo hθhi hT
  obtain ⟨C, n₀, hC, hn₀, hall⟩ := bipartite_degree_ratio θ T hθlo hθhi hT
  refine ⟨C, n₀, hC, hn₀, ?_⟩
  intro n hn p hp ell m d hw
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hT0 : 0 < T := by linarith
  have hp0 : 0 < p := (by positivity : 0 < T⁻¹ * (n : ℝ) ^ (-θ)).trans hp.1
  exact bipartite_multiplicative_of_estimate hp0 (hall n hn p hp ell m d hw)

end MajorityDynamics.Combinatorics.DegreeRatios
