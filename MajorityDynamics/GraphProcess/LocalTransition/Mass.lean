import MajorityDynamics.GraphProcess.RowArray.Statistics
import MajorityDynamics.Local.Admissibility

/-! Nonnegative child half-edge masses and their exact parent-count bounds. -/
noncomputable section
open scoped BigOperators
namespace MajorityDynamics.GraphProcess.LocalTransition
open Universal Local RowArray
variable {V : Type*} [Fintype V] {n : ℕ}

theorem templateHalfEdges_nonneg (sizes : Sizes n) (q : Tilt n)
    (u : History (n + 2)) (t : History (n + 1)) :
    0 ≤ templateHalfEdges sizes q u t := by
  unfold templateHalfEdges splitMoment
  apply mul_nonneg (Nat.cast_nonneg _)
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro a _
    exact mul_nonneg (Binomial.mass_pos _ _ _).le (by
      unfold Binomial.vector
      positivity)
  · unfold Binomial.eventMass
    exact Finset.sum_nonneg fun a _ => (Binomial.mass_pos _ _ a).le

theorem templateHalfEdges_bounds (y : CoarseData V n) (q : Tilt n)
    (hsol : Solves y.sizes y.realEdges q)
    (s : History (n + 1)) (b : Bool) (t : History (n + 1)) :
    0 ≤ templateHalfEdges y.sizes q (append s b) t ∧
      templateHalfEdges y.sizes q (append s b) t ≤ y.realEdges s t := by
  have hf := templateHalfEdges_nonneg y.sizes q (append s false) t
  have ht := templateHalfEdges_nonneg y.sizes q (append s true) t
  have hc := templateHalfEdges_children_of_solves y.sizes y.realEdges q hsol s t
  cases b <;> constructor <;> linarith

theorem childMass_nonneg {π : V → History (n + 1)} (d : Ambient π)
    (s : History (n + 1)) (b : Bool) (t : History (n + 1)) :
    0 ≤ childMass d s b t := by
  unfold childMass
  exact Finset.sum_nonneg fun v _ => (values_bounds d v t).1

theorem childMass_bounds (p : ℝ) (y : CoarseData V n) (σ : FineState.State V n)
    (hρ : CoarseKernel.rho p σ = y)
    (s : History (n + 1)) (b : Bool) (t : History (n + 1)) :
    0 ≤ (childMass (stateArray σ) s b t : ℝ) ∧
      (childMass (stateArray σ) s b t : ℝ) ≤ y.realEdges s t := by
  have hf : 0 ≤ (childMass (stateArray σ) s false t : ℝ) := by
    exact_mod_cast childMass_nonneg (stateArray σ) s false t
  have ht : 0 ≤ (childMass (stateArray σ) s true t : ℝ) := by
    exact_mod_cast childMass_nonneg (stateArray σ) s true t
  have hc := childMass_conservation (stateArray σ) (stateArray_history σ) s t
  have he : totals (stateArray σ) s t = y.edge s t := by
    have h := congrArg (fun z : CoarseData V n => z.edge s t) hρ
    simpa only [CoarseKernel.rho_edge, totals_stateArray] using h
  rw [he] at hc
  have hcr : (childMass (stateArray σ) s false t : ℝ) +
      (childMass (stateArray σ) s true t : ℝ) = y.realEdges s t := by
    unfold CoarseData.realEdges
    exact_mod_cast hc
  cases b <;> constructor <;> linarith

end MajorityDynamics.GraphProcess.LocalTransition
