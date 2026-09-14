import MajorityDynamics.GraphProcess.RowArray.Statistics
import MajorityDynamics.GraphProcess.GraphicalArray.CountFibers

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace MajorityDynamics.GraphProcess.BlockPairLaws
open Universal
variable {V : Type*} [Fintype V] {n : ℕ}

/-- The actual array mass, as the product of its original binomial row masses. -/
def mass (π : V → History (n + 1)) (q : Local.Tilt n) (d : RowArray.Ambient π) : ℝ :=
  ∏ v, Binomial.mass (Local.trials (Local.partSizes π) (π v)) (q (π v)) (d v)

theorem mass_pos (π : V → History (n + 1)) (q : Local.Tilt n) (d : RowArray.Ambient π) :
    0 < mass π q d :=
  Finset.prod_pos fun v _ => Binomial.mass_pos _ _ (d v)

theorem law_singleton_real (π : V → History (n + 1)) (q : Local.Tilt n)
    (d : RowArray.Ambient π) : (RowArray.law π q).real {d} = mass π q d := by
  have h := congrArg (fun μ : Measure (V → History (n + 1) → ℕ) =>
    μ {RowArray.naturalRows d}) (RowArray.naturalRows_law π q)
  rw [Measure.map_apply (RowArray.naturalRows_embedding π).measurable
    (measurableSet_singleton _)] at h
  have he : RowArray.naturalRows ⁻¹' {RowArray.naturalRows d} = {d} := by
    ext a
    simp only [Set.mem_preimage, Set.mem_singleton_iff, (RowArray.naturalRows_injective π).eq_iff]
  rw [he] at h
  rw [measureReal_def, h, RowArray.naturalLaw, Measure.pi_singleton, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl fun v _ => Binomial.law_singleton _ _ (d v)

theorem law_singleton (π : V → History (n + 1)) (q : Local.Tilt n)
    (d : RowArray.Ambient π) : RowArray.law π q {d} = ENNReal.ofReal (mass π q d) := by
  rw [← law_singleton_real, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem law_singleton_pos (π : V → History (n + 1)) (q : Local.Tilt n)
    (d : RowArray.Ambient π) : 0 < RowArray.law π q {d} := by
  rw [law_singleton]
  exact ENNReal.ofReal_pos.mpr (mass_pos π q d)

/-- Broad count capacities give a positive denominator for every original tilt. -/
theorem exactTotals_pos (y : Local.CoarseData V n) (q : Local.Tilt n) :
    0 < RowArray.law y.part q (RowArray.exactTotals y.part y.edge) := by
  obtain ⟨G, hG⟩ := GraphicalArray.coarse_fixedCount_nonempty y
  apply lt_of_lt_of_le (law_singleton_pos y.part q (RowArray.graphArray y.part G))
  apply measure_mono
  intro d hd
  obtain rfl := Set.mem_singleton_iff.mp hd
  exact (RowArray.totals_graphArray y.part G).trans hG

theorem conditioned_probability (y : Local.CoarseData V n) (q : Local.Tilt n) :
    IsProbabilityMeasure (cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge)) :=
  cond_isProbabilityMeasure (ne_of_gt (exactTotals_pos y q))

end MajorityDynamics.GraphProcess.BlockPairLaws
