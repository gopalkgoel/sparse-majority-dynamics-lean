import MajorityDynamics.GraphProcess.FaithfulTrajectory.Averaging
import MajorityDynamics.GraphProcess.LocalTheorem.Main

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace MajorityDynamics.GraphProcess.FaithfulTrajectory
open FineState Local CoarseKernel

/-- The actual coarse process inherits any uniform current-state kernel bound.
Positive current fibers supply attainability automatically. -/
theorem actual_one_step {V : Type*} [Fintype V] (n : ℕ)
    (p : unitInterval) (c : V → Bool) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (good : Set (CoarseData V n)) (next : Set (CoarseData V (n+1))) (ε : ℝ≥0∞)
    (hstep : ∀ y ∈ good, pAttainable p y → Kbar p y nextᶜ ≤ ε) :
    SimpleGraph.binomialRandom V p {G | rho p (actualState G c (n+1)) ∉ next} ≤
      SimpleGraph.binomialRandom V p {G | rho p (actualState G c n) ∉ good} + ε := by
  apply finite_current_state_bound (SimpleGraph.binomialRandom V p)
    (fun G => rho p (actualState G c n)) (measurable_of_countable _) good
    {G | rho p (actualState G c (n+1)) ∉ next} ε
  intro y hy hpos
  have h := proposition_2_5 p c y hp hp1 hpos
  change cond (SimpleGraph.binomialRandom V p) (currentEvent p c y)
    {G | rho p (actualState G c (n+1)) ∈ nextᶜ} ≤ ε
  rw [h.2 nextᶜ]
  exact hstep y hy h.1

/-- A locally successful transition may be consumed by any proved deterministic
inclusion. The original local theorem supplies the probability bound. -/
theorem local_success_failure {V : Type*} [Fintype V] {n : ℕ}
    (p : unitInterval) (y : CoarseData V n) (q : Tilt n) (C ε : ℝ)
    (next : Set (CoarseData V (n+1)))
    [IsProbabilityMeasure (Kbar p y)]
    (hloc : (Kbar p y).real {z | ¬LocalTransition.LocalSuccess y q p C z} ≤ ε)
    (hinc : ∀ z, LocalTransition.LocalSuccess y q p C z → z ∈ next) :
    Kbar p y nextᶜ ≤ ENNReal.ofReal ε := by
  rw [← ofReal_measureReal (μ := Kbar p y) (s := nextᶜ)]
  apply ENNReal.ofReal_le_ofReal
  apply le_trans (measureReal_mono ?_) hloc
  intro z hz hs
  exact hz (hinc z hs)

end MajorityDynamics.GraphProcess.FaithfulTrajectory
