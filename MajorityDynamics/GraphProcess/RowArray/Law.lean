import MajorityDynamics.GraphProcess.RowArray.Basic

/-! The vertex-binomial product law transported to its actual finite support. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace MajorityDynamics.GraphProcess.RowArray
open Universal
variable {V : Type*} [Fintype V] {n : ℕ}

instance rowLaw_probability (sizes : Local.Sizes n) (q : Local.Tilt n) (s : History (n + 1)) :
    IsProbabilityMeasure (Local.rowLaw sizes q s) := by
  unfold Local.rowLaw
  infer_instance

/-- Product of the existing actual binomial row measures, before support transport. -/
def naturalLaw (π : V → History (n + 1)) (q : Local.Tilt n) :
    Measure (V → History (n + 1) → ℕ) :=
  Measure.pi fun v => Local.rowLaw (Local.partSizes π) q (π v)

instance (π : V → History (n + 1)) (q : Local.Tilt n) :
    IsProbabilityMeasure (naturalLaw π q) := by
  unfold naturalLaw Local.rowLaw
  infer_instance

theorem naturalLaw_support (π : V → History (n + 1)) (q : Local.Tilt n) :
    ∀ᵐ a ∂naturalLaw π q, a ∈ Set.range (@naturalRows V _ n π) := by
  have h : ∀ᵐ a ∂naturalLaw π q, ∀ v t,
      a v t ≤ Local.trials (Local.partSizes π) (π v) t := by
    rw [ae_all_iff]
    intro v
    exact (Measure.tendsto_eval_ae_ae (μ := fun w => Local.rowLaw (Local.partSizes π) q (π w)) (i := v)).eventually
      (Binomial.law_ae_box (Local.trials (Local.partSizes π) (π v)) (q (π v)))
  filter_upwards [h] with a ha
  exact ⟨fun v t => ⟨a v t, Nat.lt_succ_of_le (ha v t)⟩, rfl⟩

/-- The paper's R on the finite ambient degree arrays; no extra constraints. -/
def law (π : V → History (n + 1)) (q : Local.Tilt n) : Measure (Ambient π) :=
  (naturalLaw π q).comap naturalRows

theorem naturalRows_law (π : V → History (n + 1)) (q : Local.Tilt n) :
    (law π q).map naturalRows = naturalLaw π q := by
  rw [law, (naturalRows_embedding π).map_comap,
    Measure.restrict_eq_self_of_ae_mem (naturalLaw_support π q)]

instance (π : V → History (n + 1)) (q : Local.Tilt n) : IsProbabilityMeasure (law π q) := by
  apply (Measure.isProbabilityMeasure_map_iff (naturalRows_embedding π).measurable.aemeasurable).mp
  rw [naturalRows_law]
  infer_instance

theorem row_law (π : V → History (n + 1)) (q : Local.Tilt n) (v : V) :
    (law π q).map (fun d => naturalRows d v) = Local.rowLaw (Local.partSizes π) q (π v) := by
  calc
    _ = ((law π q).map naturalRows).map (Function.eval v) :=
      (Measure.map_map (measurable_pi_apply v) (naturalRows_embedding π).measurable).symm
    _ = _ := by rw [naturalRows_law]; exact (measurePreserving_eval _ v).map_eq

theorem coordinate_law (π : V → History (n + 1)) (q : Local.Tilt n) (v : V)
    (t : History (n + 1)) :
    (law π q).map (fun d => naturalRows d v t) =
      binomial (Local.trials (Local.partSizes π) (π v) t)
        (Binomial.closedProbability (q (π v) t)) := by
  calc
    _ = ((law π q).map (fun d => naturalRows d v)).map (Function.eval t) :=
      (Measure.map_map (measurable_pi_apply t) (measurable_of_countable _)).symm
    _ = _ := by rw [row_law]; exact Binomial.coordinate_law _ _ _

theorem joint_rectangle (π : V → History (n + 1)) (q : Local.Tilt n)
    (E : V → Set (History (n + 1) → ℕ)) :
    law π q {d | ∀ v, naturalRows d v ∈ E v} =
      ∏ v, Local.rowLaw (Local.partSizes π) q (π v) (E v) := by
  have h := congrArg (fun μ : Measure (V → History (n + 1) → ℕ) =>
    μ (Set.univ.pi E)) (naturalRows_law π q)
  rw [Measure.map_apply (naturalRows_embedding π).measurable (Set.to_countable _).measurableSet,
    naturalLaw, Measure.pi_pi] at h
  have he : naturalRows ⁻¹' (Set.univ.pi E) = {d : Ambient π | ∀ v, naturalRows d v ∈ E v} := by
    ext d
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_ofPred_eq]
  rw [he] at h
  exact h

theorem independent_rows (π : V → History (n + 1)) (q : Local.Tilt n) :
    iIndepFun (fun v d => naturalRows d v) (law π q) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun _ => (measurable_of_countable _).aemeasurable)).mpr
  simp_rw [row_law]
  exact naturalRows_law π q

/-- Before history conditioning, coordinates within every row are independent. -/
theorem independent_row_coordinates (π : V → History (n + 1)) (q : Local.Tilt n) (v : V) :
    iIndepFun (fun t d => naturalRows d v t) (law π q) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun _ => (measurable_of_countable _).aemeasurable)).mpr
  simp_rw [coordinate_law]
  exact row_law π q v

/-- Full entry rectangle factorization, including entries in different rows. -/
theorem entry_rectangle (π : V → History (n + 1)) (q : Local.Tilt n)
    (E : V → History (n + 1) → Set ℕ) :
    law π q {d | ∀ v t, naturalRows d v t ∈ E v t} =
      ∏ v, ∏ t, binomial (Local.trials (Local.partSizes π) (π v) t)
        (Binomial.closedProbability (q (π v) t)) (E v t) := by
  have he : {d : Ambient π | ∀ v t, naturalRows d v t ∈ E v t} =
      {d | ∀ v, naturalRows d v ∈ Set.univ.pi (E v)} := by
    ext d
    simp only [Set.mem_ofPred_eq, Set.mem_univ_pi]
  rw [he, joint_rectangle]
  simp only [Local.rowLaw, Binomial.law, Measure.pi_pi]

end MajorityDynamics.GraphProcess.RowArray
