import MajorityDynamics.GraphProcess.NonLumpability.States

noncomputable section
open MeasureTheory
namespace MajorityDynamics.GraphProcess.NonLumpability
open Universal FineState History CoarseKernel FineKernel

/-- This event inspects only the next coarse partition. -/
def nextEvent : Set (Local.CoarseData (Fin 8) 1) :=
  {y | Local.partSizes y.part (append (label false) false) = 4}

theorem projected_probability (variant : Bool) :
    ((FineKernel.K (state variant)).map (rho (1 / 2 : ℝ))) nextEvent =
      if variant then 0 else 1 := by
  rw [Measure.map_apply (measurable_of_countable _) (Set.toFinite _).measurableSet,
    FineKernel.K_apply]
  have h : {F | sampleNext (state variant) F ∈ rho (1 / 2 : ℝ) ⁻¹' nextEvent} =
      if variant then ∅ else Set.univ := by
    ext F
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, nextEvent, rho_part,
      sampleNext_part, refinement_size]
    cases variant <;> simp
  rw [h]
  cases variant <;> simp

theorem first_probability :
    ((FineKernel.K (state false)).map (rho (1 / 2 : ℝ))) nextEvent = 1 := by
  exact projected_probability false

theorem second_probability :
    ((FineKernel.K (state true)).map (rho (1 / 2 : ℝ))) nextEvent = 0 := by
  exact projected_probability true

/-- No coarse kernel reproduces every fine-state transition. This does not
assert that a particular projected process fails to be Markov. -/
theorem no_coarse_kernel :
    ¬ ∃ Q : Local.CoarseData (Fin 8) 0 → Measure (Local.CoarseData (Fin 8) 1),
      ∀ σ : State (Fin 8) 0,
        (FineKernel.K σ).map (rho (1 / 2 : ℝ)) = Q (rho (1 / 2 : ℝ) σ) := by
  rintro ⟨Q, hQ⟩
  have he : (FineKernel.K (state false)).map (rho (1 / 2 : ℝ)) =
      (FineKernel.K (state true)).map (rho (1 / 2 : ℝ)) := by
    rw [hQ, hQ, same_coarse]
  have hp := congrArg (fun μ : Measure (Local.CoarseData (Fin 8) 1) => μ nextEvent) he
  rw [first_probability, second_probability] at hp
  exact one_ne_zero hp

end MajorityDynamics.GraphProcess.NonLumpability
