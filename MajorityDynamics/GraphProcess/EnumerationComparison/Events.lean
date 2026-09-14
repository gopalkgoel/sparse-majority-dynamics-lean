import MajorityDynamics.GraphProcess.EnumerationComparison.Product

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.EnumerationComparison

theorem sandwich_event {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (μ ν : Measure X) [SigmaFinite μ] [SigmaFinite ν]
    (C : ℝ) (E : Set X) (h : ∀ d ∈ E, Sandwich C (μ.real {d}) (ν.real {d})) :
    Sandwich C (μ.real E) (ν.real E) := by
  classical
  have he : (E.toFinite.toFinset : Set X) = E := E.toFinite.coe_toFinset
  have hμ : μ.real E = ∑ d ∈ E.toFinite.toFinset, μ.real {d} := by
    rw [sum_measureReal_singleton, he]
  have hν : ν.real E = ∑ d ∈ E.toFinite.toFinset, ν.real {d} := by
    rw [sum_measureReal_singleton, he]
  rw [Sandwich, hμ, hν, Finset.mul_sum, Finset.mul_sum]
  exact ⟨Finset.sum_le_sum (fun d hd => (h d (by simpa using hd)).1),
    Finset.sum_le_sum (fun d hd => (h d (by simpa using hd)).2)⟩

end MajorityDynamics.GraphProcess.EnumerationComparison
