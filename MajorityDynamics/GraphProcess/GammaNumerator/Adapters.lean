import MajorityDynamics.GraphProcess.RowArray.Statistics

/-! Actual array pushforward and prescribed-total numerator identities. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace MajorityDynamics.GraphProcess.GammaNumerator
open Universal
universe u
variable {V : Type u} [Fintype V] {n : ℕ}

/-- The paper's graph-induced degree-array law, with no conditioning. -/
def arrayLaw (π : V → History (n+1)) (p : unitInterval) :
    Measure (RowArray.Ambient π) :=
  (SimpleGraph.binomialRandom V p).map (RowArray.graphArray π)

instance arrayLaw_probability (π : V → History (n+1)) (p : unitInterval) :
    IsProbabilityMeasure (arrayLaw π p) := by
  unfold arrayLaw
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

/-- Exact pushforward on every array event. -/
theorem arrayLaw_real (π : V → History (n+1)) (p : unitInterval)
    (E : Set (RowArray.Ambient π)) :
    (arrayLaw π p).real E =
      (SimpleGraph.binomialRandom V p).real {G | RowArray.graphArray π G ∈ E} := by
  rw [measureReal_def, arrayLaw, Measure.map_apply (measurable_of_countable _)
    (Set.toFinite _).measurableSet]
  rfl

/-- On the literal ordered-total event, the two Gamma predicates coincide. -/
theorem gamma_eq_on_exactTotals (π : V → History (n+1))
    (m : History (n+1) → History (n+1) → ℤ) (C p : ℝ)
    (d : RowArray.Ambient π) (hd : d ∈ RowArray.exactTotals π m) :
    RowArray.Gamma π m C p d ↔ RowArray.Gamma π (RowArray.totals d) C p d := by
  change RowArray.totals d = m at hd
  rw [hd]

/-- Additional restrictions, including the original history event, only shrink
    the numerator. Diagonal totals remain ordered degree sums. -/
theorem restricted_numerator_le (π : V → History (n+1)) (p : unitInterval)
    (m : History (n+1) → History (n+1) → ℤ) (C : ℝ)
    (E : Set (RowArray.Ambient π)) :
    (arrayLaw π p).real {d | ¬ RowArray.Gamma π m C p d ∧ d ∈ E ∧
        RowArray.Regular p d ∧ d ∈ RowArray.exactTotals π m} ≤
      (arrayLaw π p).real {d | ¬ RowArray.Gamma π (RowArray.totals d) C p d ∧
        RowArray.Regular p d} := by
  apply measureReal_mono (μ := arrayLaw π p) _ (measure_ne_top _ _)
  intro d hd
  exact ⟨fun h => hd.1 ((gamma_eq_on_exactTotals π m C p d hd.2.2.2).mpr h), hd.2.2.1⟩

/-- Literal B.3 numerator, with the original history and ordered count events. -/
theorem paper_numerator_le (π : V → History (n+1)) (p : unitInterval)
    (m : History (n+1) → History (n+1) → ℤ) (C : ℝ) :
    (arrayLaw π p).real {d | ¬ RowArray.Gamma π m C p d ∧
        d ∈ RowArray.history π ∧ RowArray.Regular p d ∧ d ∈ RowArray.exactTotals π m} ≤
      (SimpleGraph.binomialRandom V p).real {G |
        ¬ RowArray.Gamma π (RowArray.totals (RowArray.graphArray π G)) C p
          (RowArray.graphArray π G) ∧ RowArray.Regular p (RowArray.graphArray π G)} := by
  exact (restricted_numerator_le π p m C (RowArray.history π)).trans_eq
    (arrayLaw_real π p {d | ¬ RowArray.Gamma π (RowArray.totals d) C p d ∧
      RowArray.Regular p d})

end MajorityDynamics.GraphProcess.GammaNumerator
