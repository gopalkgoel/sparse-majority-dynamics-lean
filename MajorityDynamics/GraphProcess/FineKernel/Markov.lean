import MajorityDynamics.GraphProcess.FineKernel.Kernel
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.FineKernel
open FineState
variable {V : Type*} [Fintype V] {n : ℕ}

/-- Proposition 2.3: the literal conditional pushforward given the present state. -/
theorem present_transition_law (c : V → Bool) (σ : State V n) (p : unitInterval)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (h : 0 < SimpleGraph.binomialRandom V p (stateEvent c σ)) :
    (cond (SimpleGraph.binomialRandom V p) (stateEvent c σ)).map
      (fun G => actualState G c (n+1)) = K σ := by
  rw [state_conditional_graph c σ p hp hp1 h]
  exact (K_eq_uniform_graph σ c (compatible_of_positive c σ _ h)).symm

/-- The paper's event-probability formula with the actual binomial graph law. -/
theorem present_transition (c : V → Bool) (σ : State V n) (p : unitInterval)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (h : 0 < SimpleGraph.binomialRandom V p (stateEvent c σ))
    (A : Set (State V (n+1))) :
    cond (SimpleGraph.binomialRandom V p) (stateEvent c σ)
      {G | actualState G c (n+1) ∈ A} = K σ A := by
  rw [← present_transition_law c σ p hp hp1 h,
    Measure.map_apply (measurable_of_countable _) (Set.toFinite _).measurableSet]
  rfl

/-- All states through the current day, with their actual heterogeneous types. -/
def pastEvent (c : V → Bool) (h : (i : Fin (n+1)) → State V i.val) :
    Set (SimpleGraph V) := {G | ∀ i, actualState G c i.val = h i}

/-- A witness supplies consistency; no consistency hypothesis is assumed. -/
theorem pastEvent_eq_present (c : V → Bool) (h : (i : Fin (n+1)) → State V i.val)
    (hne : (pastEvent c h).Nonempty) :
    pastEvent c h = stateEvent c (h (Fin.last n)) := by
  obtain ⟨G₀, h₀⟩ := hne
  ext G
  constructor
  · intro hG
    exact hG (Fin.last n)
  · intro hG i
    have hi : i.val ≤ n := Nat.le_of_lt_succ i.isLt
    have hh : project hi (h (Fin.last n)) = h i := by
      rw [← h₀ (Fin.last n)]
      exact (project_actualState hi G₀ c).trans (h₀ i)
    rw [← hh, ← hG]
    exact (project_actualState hi G c).symm

/-- Whole-history Markov law, derived from positive past mass and prefix recovery. -/
theorem past_transition_law (c : V → Bool) (h : (i : Fin (n+1)) → State V i.val)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hpos : 0 < SimpleGraph.binomialRandom V p (pastEvent c h)) :
    (cond (SimpleGraph.binomialRandom V p) (pastEvent c h)).map
      (fun G => actualState G c (n+1)) = K (h (Fin.last n)) := by
  have he := pastEvent_eq_present c h (nonempty_of_measure_ne_zero hpos.ne')
  rw [he] at hpos ⊢
  exact present_transition_law c _ p hp hp1 hpos

theorem past_transition (c : V → Bool) (h : (i : Fin (n+1)) → State V i.val)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hpos : 0 < SimpleGraph.binomialRandom V p (pastEvent c h))
    (A : Set (State V (n+1))) :
    cond (SimpleGraph.binomialRandom V p) (pastEvent c h)
      {G | actualState G c (n+1) ∈ A} = K (h (Fin.last n)) A := by
  rw [← past_transition_law c h p hp hp1 hpos,
    Measure.map_apply (measurable_of_countable _) (Set.toFinite _).measurableSet]
  rfl
end MajorityDynamics.GraphProcess.FineKernel
