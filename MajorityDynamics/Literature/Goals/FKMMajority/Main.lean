import MajorityDynamics.Literature.Goals.FKMMajority.Statement
import MajorityDynamics.Literature.FKMAdapters.FixedInitial
import MajorityDynamics.Literature.FKMAdapters.GraphLaw

namespace MajorityDynamics.Literature

theorem fkm_majority : FKMMajorityTheorem := MD.theorem_1_1

example : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    ∃ L : ℝ, 0 < L ∧ ∃ N₀ : ℕ, ∀ N > N₀,
      ∀ p : ℝ, L / Real.sqrt N ≤ p → p ≤ 1 →
        1 - ε ≤ MD.Pr (MD.q N p) (MD.Good (n := N)) := fkm_majority

/-- The deterministic-initial-state consequence actually used in the full
uniform theorem. Its contract is separately checked, without randomizing or
adding a probabilistic assumption on the initial coloring. -/
example : ∀ c : ℝ, 0 < c → c ≤ 1 → ∀ ε : ℝ, 0 < ε →
    ∃ L : ℝ, 0 < L ∧ ∃ N₀ : ℕ, ∀ N > N₀,
      ∀ p : ℝ, L / Real.sqrt N ≤ p → p ≤ 1 → ∀ s : Fin N → Bool,
        c * Real.sqrt N ≤
          (((MD.sset s true).card : ℝ) - 2 - (MD.sset s false).card) →
        MD.Pr (MD.q N p) (fun x => ¬ ∀ v, MD.Sfix x s 4 v = true) ≤ ε :=
  MD.fixed_initial_dense

/-- info: 'MD.fixed_initial_dense' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MD.fixed_initial_dense

/-- info: 'MajorityDynamics.Literature.FKMAdapters.event_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FKMAdapters.event_probability

end MajorityDynamics.Literature
