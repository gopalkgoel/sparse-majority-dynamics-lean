import MajorityDynamics.Local.RowModel
import MajorityDynamics.Binomial.Conditioning

/-!
# The exact local template and its conservation identities

Source: §3, `def:local-template`, used to define the idealized process in §5.
The output sizes are real numbers; the later idealized construction rounds
them down. No partition, graphicality, tilt-existence, or asymptotic claim is
built into these definitions.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace MajorityDynamics.Local

open Universal
variable {n : ℕ}

/-- The conditioning event is the original history predicate on the actual
binomial row, including ties. The finite-support enumeration changes no law. -/
theorem rowCondition_eq_actual (sizes : Sizes n) (q : Tilt n) (s : History (n + 1)) :
    rowCondition sizes q s = ProbabilityTheory.cond (rowLaw sizes q s)
      {a | WithLp.toLp 2 (fun t => (a t : ℝ)) ∈ historyEvent s} := by
  unfold rowCondition rowLaw
  rw [← Binomial.conditionalLaw_filter]
  congr 1
  ext a
  simp only [historySupport, Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

theorem splitProbability_eq_measure (sizes : Sizes n) (q : Tilt n)
    (s : History (n + 1)) (b : Bool) :
    splitProbability sizes q s b =
      (rowCondition sizes q s).real (Binomial.event (childSupport sizes s b)) :=
  (Binomial.conditionalLaw_event _ _ _ _ (childSupport_subset sizes s b)).symm

theorem splitMoment_eq_integral (sizes : Sizes n) (q : Tilt n)
    (s : History (n + 1)) (b : Bool) (t : History (n + 1)) :
    splitMoment sizes q s b t = ∫ a,
      (Binomial.event (childSupport sizes s b)).indicator (fun a => (a t : ℝ)) a
        ∂rowCondition sizes q s :=
  by
    simpa only [splitMoment, rowCondition, Binomial.vector, Binomial.point] using
      (Binomial.conditionalLaw_indicator (trials sizes s) (q s) _ _
        (childSupport_subset sizes s b) (fun a => (a t : ℝ))).symm

theorem splitProbability_add (sizes : Sizes n) (q : Tilt n) (s : History (n + 1))
    (hS : (historySupport sizes s).Nonempty) :
    splitProbability sizes q s false + splitProbability sizes q s true = 1 := by
  classical
  simp only [splitProbability, Binomial.eventMass]
  rw [← add_div, ← Finset.sum_union (childSupport_disjoint sizes s), childSupport_union]
  exact div_self (Binomial.eventMass_pos (trials sizes s) (q s) hS).ne'

theorem splitMoment_add (sizes : Sizes n) (q : Tilt n) (s t : History (n + 1)) :
    splitMoment sizes q s false t + splitMoment sizes q s true t = rowMean sizes q s t := by
  classical
  rw [splitMoment, splitMoment, ← add_div,
    ← Finset.sum_union (childSupport_disjoint sizes s), childSupport_union]
  simp [rowMean, Binomial.conditionalMean, Binomial.expectation, Binomial.conditionalWeight,
    Finset.sum_div, div_mul_eq_mul_div]

/-- `nˡᵒᶜ[sb]`: real-valued, before any floor operation. -/
def templateSizes (sizes : Sizes n) (q : Tilt n) (u : History (n + 2)) : ℝ :=
  (sizes (parent u) : ℝ) * splitProbability sizes q (parent u) (last u)

/-- `ℓˡᵒᶜ[sb,t]`: the conditional first moment with the split indicator. -/
def templateHalfEdges (sizes : Sizes n) (q : Tilt n)
    (u : History (n + 2)) (t : History (n + 1)) : ℝ :=
  (sizes (parent u) : ℝ) * splitMoment sizes q (parent u) (last u) t

/-- `mˡᵒᶜ[sb,tc]`, with the paper's ordered-edge convention. -/
def templateEdges (sizes : Sizes n) (m : EdgeCounts n) (q : Tilt n)
    (u v : History (n + 2)) : ℝ :=
  templateHalfEdges sizes q u (parent v) * templateHalfEdges sizes q v (parent u) /
    m (parent u) (parent v)

/-- The exact domain on which the paper invokes its local template. -/
def TemplateDefined (sizes : Sizes n) (m : EdgeCounts n) : Prop :=
  (∀ s, 0 < sizes s) ∧ (∀ s, (historySupport sizes s).Nonempty) ∧ ∀ s t, m s t ≠ 0

theorem templateSizes_children (sizes : Sizes n) (q : Tilt n) (s : History (n + 1))
    (hS : (historySupport sizes s).Nonempty) :
    templateSizes sizes q (append s false) + templateSizes sizes q (append s true) = sizes s := by
  simp only [templateSizes, parent_append, last_append, ← mul_add, splitProbability_add sizes q s hS,
    mul_one]

theorem templateHalfEdges_children (sizes : Sizes n) (q : Tilt n) (s t : History (n + 1)) :
    templateHalfEdges sizes q (append s false) t + templateHalfEdges sizes q (append s true) t =
      (sizes s : ℝ) * rowMean sizes q s t := by
  simp only [templateHalfEdges, parent_append, last_append, ← mul_add, splitMoment_add]

theorem templateHalfEdges_children_of_solves (sizes : Sizes n) (m : EdgeCounts n)
    (q : Tilt n) (h : Solves sizes m q) (s t : History (n + 1)) :
    templateHalfEdges sizes q (append s false) t + templateHalfEdges sizes q (append s true) t =
      m s t := by rw [templateHalfEdges_children, h s t]

theorem templateEdges_symmetric (sizes : Sizes n) (m : EdgeCounts n) (q : Tilt n)
    (hm : ∀ s t, m s t = m t s) (u v : History (n + 2)) :
    templateEdges sizes m q u v = templateEdges sizes m q v u := by
  rw [templateEdges, templateEdges, hm (parent u) (parent v), mul_comm]

/-- Summing the four refined block-pair counts recovers the old ordered count. -/
theorem templateEdges_children_of_solves (sizes : Sizes n) (m : EdgeCounts n)
    (q : Tilt n) (h : Solves sizes m q) (hm : ∀ s t, m s t = m t s)
    (s t : History (n + 1)) (hne : m s t ≠ 0) :
    templateEdges sizes m q (append s false) (append t false) +
      templateEdges sizes m q (append s false) (append t true) +
      templateEdges sizes m q (append s true) (append t false) +
      templateEdges sizes m q (append s true) (append t true) = m s t := by
  calc
    _ = (templateHalfEdges sizes q (append s false) t + templateHalfEdges sizes q (append s true) t) *
        (templateHalfEdges sizes q (append t false) s + templateHalfEdges sizes q (append t true) s) /
        m s t := by simp only [templateEdges, parent_append]; ring
    _ = m s t := by
      rw [templateHalfEdges_children_of_solves sizes m q h s t,
        templateHalfEdges_children_of_solves sizes m q h t s, hm t s]
      exact mul_div_cancel_right₀ (m s t) hne

end MajorityDynamics.Local
