import MajorityDynamics.GraphProcess.CoarseKernel.Fiber
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.CoarseKernel
open FineState Local
variable {V : Type*} [Fintype V] {n : ℕ}

/-- Average over the full graph-induced fiber, not over a selected representative. -/
def Kbar (p : unitInterval) (y : CoarseData V n) : Measure (CoarseData V (n+1)) :=
  ∑ σ : State V n, Lambda p y {σ} • (FineKernel.K σ).map (rho p)

theorem Kbar_apply (p : unitInterval) (y : CoarseData V n) (B : Set (CoarseData V (n+1))) :
    Kbar p y B = ∑ σ : State V n, Lambda p y {σ} * FineKernel.K σ {τ | rho p τ ∈ B} := by
  simp only [Kbar, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_of_countable _) (Set.toFinite B).measurableSet]
  rfl

theorem Kbar_probability (p : unitInterval) (y : CoarseData V n)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hy : pAttainable p y) :
    IsProbabilityMeasure (Kbar p y) := by
  have := Lambda_probability p y hp hp1 hy
  constructor
  rw [Kbar_apply]
  simp only [Set.mem_univ, Set.ofPred_true, measure_univ, mul_one]
  simp

theorem Kbar_unattainable (p : unitInterval) (y : CoarseData V n) (hy : ¬ pAttainable p y) :
    Kbar p y = 0 := by simp [Kbar,Lambda_unattainable p y hy]

def currentEvent (p : ℝ) (c : V → Bool) (y : CoarseData V n) : Set (SimpleGraph V) :=
  {G | rho p (actualState G c n) = y}

theorem compatible_of_positive (p : ℝ) (c : V → Bool) (y : CoarseData V n)
    (μ : Measure (SimpleGraph V)) (h : 0 < μ (currentEvent p c y)) :
    CompatibleInitial y.part c := by
  obtain ⟨G,hG⟩ := nonempty_of_measure_ne_zero h.ne'
  have hp : (actualState G c n).part = y.part := congrArg CoarseData.part hG
  rw [← hp]
  exact ((actualState_eq_iff G c (actualState G c n)).mp rfl).1

theorem attainable_of_positive (p : ℝ) (c : V → Bool) (y : CoarseData V n)
    (μ : Measure (SimpleGraph V)) (h : 0 < μ (currentEvent p c y)) : pAttainable p y := by
  obtain ⟨G,hG⟩ := nonempty_of_measure_ne_zero h.ne'
  exact ⟨actualState G c n,hG⟩

theorem currentEvent_eq_E (p : ℝ) (c : V → Bool) (y : CoarseData V n)
    (hc : CompatibleInitial y.part c) : currentEvent p c y = E p y := by
  ext G; exact (E_iff_actual p y G c hc).symm

theorem current_fine_law (p : unitInterval) (c : V → Bool) (y : CoarseData V n)
    (hc : CompatibleInitial y.part c) :
    (cond (SimpleGraph.binomialRandom V p) (currentEvent p c y)).map
      (fun G => actualState G c n) = Lambda p y := by
  rw [currentEvent_eq_E p c y hc]
  unfold Lambda
  ext A hA
  rw [Measure.map_apply (measurable_of_countable _) hA,
    Measure.map_apply (measurable_of_countable _) hA,
    cond_apply (Set.toFinite _).measurableSet, cond_apply (Set.toFinite _).measurableSet]
  congr 2
  ext G
  have he (hG : G ∈ E p y) : actualState G c n = actualState G (initial y) n :=
    (actual_eq_raw p y G hG c hc).trans
      (actual_eq_raw p y G hG _ (canonical_compatible y)).symm
  change (G ∈ E p y ∧ actualState G c n ∈ A) ↔
    (G ∈ E p y ∧ actualState G (initial y) n ∈ A)
  exact ⟨fun ⟨hG,hA⟩ => ⟨hG, he hG ▸ hA⟩, fun ⟨hG,hA⟩ => ⟨hG, (he hG).symm ▸ hA⟩⟩

end MajorityDynamics.GraphProcess.CoarseKernel
