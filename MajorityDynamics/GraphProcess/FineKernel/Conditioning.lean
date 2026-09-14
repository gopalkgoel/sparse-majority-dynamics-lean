import MajorityDynamics.GraphProcess.FineKernel.Uniform
noncomputable section
open MeasureTheory ProbabilityTheory
open unitInterval (toNNReal)
open scoped Classical ENNReal NNReal BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.FineKernel
open FineState History BlockDecomposition
open MajorityDynamics.Probability.FixedDegreeSampling
variable {V : Type*} [Fintype V] {n : ℕ}

def realizerEvent (σ : State V n) : Set (SimpleGraph V) :=
  {G | degreeArray σ.part G = σ.deg}

def stateEvent (c : V → Bool) (σ : State V n) : Set (SimpleGraph V) :=
  {G | actualState G c n = σ}

theorem realizer_same_degree (σ : State V n) (G H : realizerEvent σ) (v : V) :
    G.val.degree v = H.val.degree v := by
  have hg := sum_degreeArray σ.part G.val v
  have hh := sum_degreeArray σ.part H.val v
  rw [G.property] at hg
  rw [H.property] at hh
  exact_mod_cast hg.symm.trans hh

theorem realizer_same_edge_count (σ : State V n) (G H : realizerEvent σ) :
    G.val.edgeSet.ncard = H.val.edgeSet.ncard :=
  graph_edge_count_constant (fun v => H.val.degree v)
    ⟨G.val, fun v => realizer_same_degree σ G H v⟩ ⟨H.val, fun _ => rfl⟩

/-- Constant positive Bernoulli weights imply uniformity on the actual array fiber. -/
theorem realizer_conditional (σ : State V n) (p : unitInterval)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    0 < SimpleGraph.binomialRandom V p (realizerEvent σ) ∧
      cond (SimpleGraph.binomialRandom V p) (realizerEvent σ) = uniformOn (realizerEvent σ) := by
  obtain ⟨G, hG⟩ := σ.realizable
  apply conditional_eq_uniform _ _ ⟨G, hG⟩
    ((toNNReal p : ℝ≥0∞) ^ G.edgeSet.ncard *
      (toNNReal (unitInterval.symm p) : ℝ≥0∞) ^ ((Nat.card V).choose 2 - G.edgeSet.ncard))
    (bernoulli_weight_ne_zero p hp hp1 _ _)
  intro H hH
  rw [SimpleGraph.binomialRandom_singleton,
    realizer_same_edge_count σ ⟨H, hH⟩ ⟨G, hG⟩]

/-- A positive actual state event forces compatibility with the fixed coloring. -/
theorem compatible_of_positive (c : V → Bool) (σ : State V n) (μ : Measure (SimpleGraph V))
    (h : 0 < μ (stateEvent c σ)) : CompatibleInitial σ.part c := by
  obtain ⟨G, hG⟩ := nonempty_of_measure_ne_zero h.ne'
  exact (actualState_eq_iff G c σ).mp hG |>.1

theorem stateEvent_eq_realizer (c : V → Bool) (σ : State V n)
    (μ : Measure (SimpleGraph V)) (h : 0 < μ (stateEvent c σ)) :
    stateEvent c σ = realizerEvent σ :=
  conditioning_event σ c (compatible_of_positive c σ μ h)

/-- No compatibility premise survives: it is derived from positive state mass. -/
theorem state_conditional_graph (c : V → Bool) (σ : State V n) (p : unitInterval)
    (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (h : 0 < SimpleGraph.binomialRandom V p (stateEvent c σ)) :
    cond (SimpleGraph.binomialRandom V p) (stateEvent c σ) = uniformOn (realizerEvent σ) := by
  rw [stateEvent_eq_realizer c σ _ h]
  exact (realizer_conditional σ p hp hp1).2
end MajorityDynamics.GraphProcess.FineKernel
