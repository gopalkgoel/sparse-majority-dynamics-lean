import MajorityDynamics.GraphProcess.RowArray.Law

/-! Fact 3.6: conditioning by the original vertexwise histories gives independent conditional rows. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace MajorityDynamics.GraphProcess.RowArray
open Universal
variable {V : Type*} [Fintype V] {n : ℕ}

/-- The literal original history event on a natural row. -/
def rowHistory (s : History (n + 1)) : Set (History (n + 1) → ℕ) :=
  {a | WithLp.toLp 2 (fun t => (a t : ℝ)) ∈ Universal.historyEvent s}

/-- I_Pi on ambient arrays, with exactly the original strict/weak tie rules. -/
def history (π : V → History (n + 1)) : Set (Ambient π) :=
  {d | ∀ v, realRow d v ∈ Universal.historyEvent (π v)}

theorem history_product (π : V → History (n + 1)) :
    history π = naturalRows ⁻¹' (Set.univ.pi fun v => rowHistory (π v)) := by
  ext d
  simp only [history, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_univ_pi]
  rfl

theorem rowHistory_support (sizes : Local.Sizes n) (s : History (n + 1)) :
    Local.historySupport sizes s =
      Finset.univ.filter (fun a : Binomial.Box (Local.trials sizes s) =>
        Binomial.point a ∈ rowHistory s) := rfl

theorem rowCondition_eq_cond (sizes : Local.Sizes n) (q : Local.Tilt n)
    (s : History (n + 1)) :
    Local.rowCondition sizes q s = cond (Local.rowLaw sizes q s) (rowHistory s) := by
  unfold Local.rowCondition Local.rowLaw
  rw [rowHistory_support]
  convert Binomial.conditionalLaw_filter (Local.trials sizes s) (q s) (rowHistory s) using 2
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem history_mass (π : V → History (n + 1)) (q : Local.Tilt n) :
    law π q (history π) =
      ∏ v, Local.rowLaw (Local.partSizes π) q (π v) (rowHistory (π v)) := by
  exact joint_rectangle π q (fun v => rowHistory (π v))

theorem history_pos_of_vertices (π : V → History (n + 1)) (q : Local.Tilt n)
    (h : ∀ v, 0 < Local.rowLaw (Local.partSizes π) q (π v) (rowHistory (π v))) :
    0 < law π q (history π) := by
  rw [history_mass]
  exact pos_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun v _ => (h v).ne')

theorem history_pos (π : V → History (n + 1)) (q : Local.Tilt n)
    (h : ∀ s, 0 < Local.rowLaw (Local.partSizes π) q s (rowHistory s)) :
    0 < law π q (history π) := history_pos_of_vertices π q fun v => h (π v)

/-- Exact product conditioning on the unconstrained natural-row carrier. -/
theorem natural_conditioning (π : V → History (n + 1)) (q : Local.Tilt n)
    (h : ∀ v, 0 < Local.rowLaw (Local.partSizes π) q (π v) (rowHistory (π v))) :
    cond (naturalLaw π q) (Set.univ.pi fun v => rowHistory (π v)) =
      Measure.pi (fun v => Local.rowCondition (Local.partSizes π) q (π v)) := by
  have (v : V) : IsProbabilityMeasure
      (Local.rowCondition (Local.partSizes π) q (π v)) := by
    rw [rowCondition_eq_cond]
    exact cond_isProbabilityMeasure (h v).ne'
  symm
  apply Measure.pi_eq
  intro E hE
  rw [cond_apply (MeasurableSet.univ_pi (fun _ => (Set.to_countable _).measurableSet)),
    naturalLaw, Measure.pi_pi, ← Set.pi_inter_distrib, Measure.pi_pi]
  simp_rw [rowCondition_eq_cond, cond_apply (Set.to_countable _).measurableSet]
  rw [Finset.prod_mul_distrib, ENNReal.prod_inv_distrib]
  intro i _ j _ _
  exact Or.inl (h i).ne'

/-- Full Fact 3.6: the natural-row joint pushforward is the actual product of
existing conditional binomial row measures, not merely a marginal assertion. -/
theorem conditioned_rows_of_vertices (π : V → History (n + 1)) (q : Local.Tilt n)
    (h : ∀ v, 0 < Local.rowLaw (Local.partSizes π) q (π v) (rowHistory (π v))) :
    (cond (law π q) (history π)).map naturalRows =
      Measure.pi (fun v => Local.rowCondition (Local.partSizes π) q (π v)) := by
  rw [history_product, law, ← comap_cond (naturalRows_embedding π)
    (naturalLaw_support π q) (Set.to_countable _).measurableSet,
    (naturalRows_embedding π).map_comap]
  have hs : ∀ᵐ a ∂cond (naturalLaw π q) (Set.univ.pi fun v => rowHistory (π v)),
      a ∈ Set.range (@naturalRows V _ n π) :=
    cond_absolutelyContinuous.ae_le (naturalLaw_support π q)
  rw [Measure.restrict_eq_self_of_ae_mem hs]
  exact natural_conditioning π q h

theorem conditioned_rows (π : V → History (n + 1)) (q : Local.Tilt n)
    (h : ∀ s, 0 < Local.rowLaw (Local.partSizes π) q s (rowHistory s)) :
    (cond (law π q) (history π)).map naturalRows =
      Measure.pi (fun v => Local.rowCondition (Local.partSizes π) q (π v)) :=
  conditioned_rows_of_vertices π q fun v => h (π v)

theorem conditioned_row_law (π : V → History (n + 1)) (q : Local.Tilt n)
    (h : ∀ s, 0 < Local.rowLaw (Local.partSizes π) q s (rowHistory s)) (v : V) :
    (cond (law π q) (history π)).map (fun d => naturalRows d v) =
      Local.rowCondition (Local.partSizes π) q (π v) := by
  have (w : V) : IsProbabilityMeasure (Local.rowCondition (Local.partSizes π) q (π w)) := by
    rw [rowCondition_eq_cond]
    exact cond_isProbabilityMeasure (h _).ne'
  calc
    _ = ((cond (law π q) (history π)).map naturalRows).map (Function.eval v) :=
      (Measure.map_map (measurable_pi_apply v) (naturalRows_embedding π).measurable).symm
    _ = _ := by rw [conditioned_rows π q h]; exact (measurePreserving_eval _ v).map_eq

theorem conditioned_independent_rows (π : V → History (n + 1)) (q : Local.Tilt n)
    (h : ∀ s, 0 < Local.rowLaw (Local.partSizes π) q s (rowHistory s)) :
    iIndepFun (fun v d => naturalRows d v) (cond (law π q) (history π)) := by
  have : IsProbabilityMeasure (cond (law π q) (history π)) :=
    cond_isProbabilityMeasure (history_pos π q h).ne'
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun _ => (measurable_of_countable _).aemeasurable)).mpr
  simp_rw [conditioned_row_law π q h]
  exact conditioned_rows π q h

theorem conditioned_rectangle (π : V → History (n + 1)) (q : Local.Tilt n)
    (h : ∀ s, 0 < Local.rowLaw (Local.partSizes π) q s (rowHistory s))
    (E : V → Set (History (n + 1) → ℕ)) :
    cond (law π q) (history π) {d | ∀ v, naturalRows d v ∈ E v} =
      ∏ v, Local.rowCondition (Local.partSizes π) q (π v) (E v) := by
  have (w : V) : IsProbabilityMeasure (Local.rowCondition (Local.partSizes π) q (π w)) := by
    rw [rowCondition_eq_cond]
    exact cond_isProbabilityMeasure (h _).ne'
  have hh := congrArg (fun μ : Measure (V → History (n + 1) → ℕ) =>
    μ (Set.univ.pi E)) (conditioned_rows π q h)
  rw [Measure.map_apply (naturalRows_embedding π).measurable (Set.to_countable _).measurableSet,
    Measure.pi_pi] at hh
  have he : naturalRows ⁻¹' (Set.univ.pi E) = {d : Ambient π | ∀ v, naturalRows d v ∈ E v} := by
    ext d
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_ofPred_eq]
  rw [he] at hh
  exact hh

theorem conditioned_row_in_part (π : V → History (n + 1)) (q : Local.Tilt n)
    (h : ∀ s, 0 < Local.rowLaw (Local.partSizes π) q s (rowHistory s))
    {v : V} {s : History (n + 1)} (hv : v ∈ History.block π s) :
    (cond (law π q) (history π)).map (fun d => naturalRows d v) =
      Local.rowCondition (Local.partSizes π) q s := by
  rw [conditioned_row_law π q h, (History.mem_block π s v).mp hv]

theorem history_iff_blocks (π : V → History (n + 1)) (d : Ambient π) :
    d ∈ history π ↔ ∀ s v, v ∈ History.block π s →
      realRow d v ∈ Universal.historyEvent s := by
  constructor
  · intro h s v hv
    simpa only [(History.mem_block π s v).mp hv] using h v
  · intro h v
    exact h (π v) v (by simp)

end MajorityDynamics.GraphProcess.RowArray
