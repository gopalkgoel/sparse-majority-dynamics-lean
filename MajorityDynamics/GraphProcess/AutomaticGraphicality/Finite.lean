import MajorityDynamics.GraphProcess.AutomaticGraphicality.Basic
import MajorityDynamics.GraphProcess.AutomaticGraphicality.Relabel
import MajorityDynamics.GraphProcess.AutomaticGraphicality.Bounds

/-! Finite, deterministic automatic graphicality on the actual ambient arrays. -/
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable
namespace MajorityDynamics.GraphProcess.AutomaticGraphicality
open Universal BlockDecomposition
variable {V : Type*} [Fintype V] {n : ℕ}

/-- A common maximum bound and sufficient count bounds give actual realizability.
The hypotheses concern the supplied array, never an attained fine state. -/
theorem graphical_of_uniform_bound (y : Local.CoarseData V n)
    (d : RowArray.Ambient y.part) (D : ℝ) (hD : 0 ≤ D)
    (htot : RowArray.totals d = y.edge)
    (hdeg : ∀ v t, (RowArray.values d v t : ℝ) ≤ D)
    (hint : ∀ s, D * (D + 1) ≤ (y.edge s s : ℝ))
    (hcross : ∀ s t, D ^ 2 ≤ (y.edge s t : ℝ)) :
    GraphicalArray.Graphical d := by
  classical
  let : DecidableEq (Universal.History (n + 1)) := fun _ _ => Classical.propDecidable _
  apply (graphical_blockwise y.part (RowArray.values d)).mpr
  constructor
  · intro s
    unfold InternalGraphical
    apply graphical_of_bound (fun v : Block y.part s => RowArray.values d v s) D
    · intro v
      exact (RowArray.values_bounds d v s).1
    · exact hD
    · intro v
      exact hdeg v s
    · convert block_sum_even y d htot s using 1
      congr
      exact Subsingleton.elim _ _
    · have hs := block_sum_eq y d htot s s
      convert hint s using 1
      rw [← hs]
      congr
      exact Subsingleton.elim _ _
  · intro s t _
    unfold CrossGraphical
    apply cross_of_bound (fun v : Block y.part s => RowArray.values d v t)
      (fun w : Block y.part t => RowArray.values d w s) D
    · intro v
      exact (RowArray.values_bounds d v t).1
    · intro w
      exact (RowArray.values_bounds d w s).1
    · exact hD
    · intro v
      exact hdeg v t
    · intro w
      exact hdeg w s
    · convert opposite_sums y d htot s t using 1 <;> congr <;> exact Subsingleton.elim _ _
    · have hs := block_sum_eq y d htot s t
      convert hcross s t using 1
      rw [← hs]
      congr
      exact Subsingleton.elim _ _

/-- Appendix B.1 in an explicit deterministic small-density / large-degree regime. -/
theorem finite_graphicality (y : Local.CoarseData V n)
    (d : RowArray.Ambient y.part) {T p : ℝ}
    (hN : 0 < (Fintype.card V : ℝ)) (hT : 1 < T) (hp : 0 < p)
    (hx : 1 ≤ p * Fintype.card V) (hxT : 4 * T ^ 6 ≤ p * Fintype.card V)
    (hpSmall : p ≤ 1 / (12 * T ^ 2))
    (hsizes : ∀ s, (Fintype.card V : ℝ) / T ≤ (y.sizes s : ℝ))
    (hcounts : ∀ s t, |(y.edge s t : ℝ) - p * (y.sizes s : ℝ) * (y.sizes t : ℝ)| ≤
      T * (Fintype.card V : ℝ) ^ 2 * p / Real.sqrt (p * Fintype.card V))
    (htot : RowArray.totals d = y.edge) (hreg : RowArray.Regular p d) :
    GraphicalArray.Graphical d := by
  have hT0 : 0 < T := by linarith
  have hD : 0 ≤ 2 * p * (Fintype.card V : ℝ) := by positivity
  have hm : ∀ s t, p * (Fintype.card V : ℝ) ^ 2 / (2 * T ^ 2) ≤ (y.edge s t : ℝ) :=
    fun s t => count_lower hN hT hp hxT (hsizes s) (hsizes t) (hcounts s t)
  apply graphical_of_uniform_bound y d (2 * p * Fintype.card V) hD htot
  · intro v t
    exact degree_upper hp.le (by exact_mod_cast y.sizes_le_card t) hx (hreg v t)
  · intro s
    exact (internal_bound hT0 hp.le hN.le hx hpSmall hD le_rfl).trans (hm s s)
  · intro s t
    simpa only [pow_two] using
      (cross_bound hT0 hp.le hN.le hpSmall hD hD le_rfl le_rfl).trans (hm s t)

end MajorityDynamics.GraphProcess.AutomaticGraphicality
