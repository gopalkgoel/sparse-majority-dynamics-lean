import MajorityDynamics.GraphProcess.CoarseKernel.Kernel
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.CoarseKernel
open FineState Local
variable {V : Type*} [Fintype V] {n : ℕ}

/-- Proposition 2.5. All compatibility, attainability and positive fine-event
premises are consequences of the positive actual coarse event. -/
theorem coarse_transition (p : unitInterval) (c : V → Bool) (y : CoarseData V n)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hpos : 0 < SimpleGraph.binomialRandom V p (currentEvent p c y))
    (B : Set (CoarseData V (n+1))) :
    cond (SimpleGraph.binomialRandom V p) (currentEvent p c y)
      {G | rho p (actualState G c (n+1)) ∈ B} = Kbar p y B := by
  let μ := SimpleGraph.binomialRandom V p
  let C := currentEvent (p:ℝ) c y
  let ν := cond μ C
  let X := fun G : SimpleGraph V => actualState G c n
  let A := {G : SimpleGraph V | rho p (actualState G c (n+1)) ∈ B}
  have : IsProbabilityMeasure ν := cond_isProbabilityMeasure hpos.ne'
  have hc := compatible_of_positive p c y μ hpos
  have hw (σ : State V n) : Lambda p y {σ} = ν (X ⁻¹' {σ}) := by
    rw [← current_fine_law p c y hc, Measure.map_apply (measurable_of_countable _)
      (MeasurableSet.singleton _)]
  have ht := congrArg (fun ξ : Measure (SimpleGraph V) => ξ A)
    (sum_meas_smul_cond_fiber (X := X) (measurable_of_countable _) ν)
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul] at ht
  rw [Kbar_apply]
  change ν A = _
  rw [← ht]
  apply Finset.sum_congr rfl
  intro σ _
  rw [hw]
  by_cases hz : ν (X ⁻¹' {σ}) = 0
  · simp only [hz,zero_mul]
  · have hinter : μ (C ∩ X ⁻¹' {σ}) ≠ 0 := by
      intro hzero
      apply hz
      change cond μ C (X ⁻¹' {σ}) = 0
      rw [cond_apply (Set.toFinite C).measurableSet,hzero,mul_zero]
    obtain ⟨G,hG⟩ := nonempty_of_measure_ne_zero hinter
    have hr : rho (p:ℝ) σ = y := by
      have hstate : actualState G c n = σ := hG.2
      have hcoarse : rho (p:ℝ) (actualState G c n) = y := hG.1
      rwa [hstate] at hcoarse
    have hsub : X ⁻¹' {σ} ⊆ C := by
      intro H hH
      change actualState H c n = σ at hH
      change rho (p:ℝ) (actualState H c n) = y
      rwa [hH]
    have hstatepos : 0 < μ (FineKernel.stateEvent c σ) := by
      apply lt_of_lt_of_le (pos_iff_ne_zero.mpr hinter)
      exact measure_mono (Set.inter_subset_right)
    have hcond : cond ν (X ⁻¹' {σ}) = cond μ (FineKernel.stateEvent c σ) := by
      dsimp [ν]
      rw [cond_cond_eq_cond_inter (Set.toFinite C).measurableSet
        (Set.toFinite _).measurableSet μ, Set.inter_eq_right.mpr hsub]
      rfl
    rw [hcond]
    congr 1
    exact FineKernel.present_transition c σ p hp hp1 hstatepos {τ | rho p τ ∈ B}

theorem proposition_2_5 (p : unitInterval) (c : V → Bool) (y : CoarseData V n)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hpos : 0 < SimpleGraph.binomialRandom V p (currentEvent p c y)) :
    pAttainable p y ∧ ∀ B : Set (CoarseData V (n+1)),
      cond (SimpleGraph.binomialRandom V p) (currentEvent p c y)
        {G | rho p (actualState G c (n+1)) ∈ B} = Kbar p y B :=
  ⟨attainable_of_positive p c y _ hpos, coarse_transition p c y hp hp1 hpos⟩

theorem coarse_transition_law (p : unitInterval) (c : V → Bool) (y : CoarseData V n)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hpos : 0 < SimpleGraph.binomialRandom V p (currentEvent p c y)) :
    (cond (SimpleGraph.binomialRandom V p) (currentEvent p c y)).map
      (fun G => rho p (actualState G c (n+1))) = Kbar p y := by
  ext B hB
  rw [Measure.map_apply (measurable_of_countable _) hB]
  exact coarse_transition p c y hp hp1 hpos B

end MajorityDynamics.GraphProcess.CoarseKernel
