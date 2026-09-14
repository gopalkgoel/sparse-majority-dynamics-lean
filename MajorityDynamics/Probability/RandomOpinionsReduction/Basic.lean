import MajorityDynamics.Paper.Problem
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic

/-! # Random opinions: concrete laws and target (`cor:random-opinions`)

Coordinates of the joint space are `(c, G)`, coloring first. The bit `false`
represents opinion +1. The update and day convention are exactly `Paper`'s.
-/

noncomputable section
open MeasureTheory

namespace MajorityDynamics.Probability.RandomOpinionsReduction

instance graph_measurableSingleton {V : Type*} [Finite V] :
    MeasurableSingletonClass (SimpleGraph V) := by
  constructor
  intro G
  have he : ({G} : Set (SimpleGraph V)) = SimpleGraph.edgeSet ⁻¹' {G.edgeSet} := by
    ext H
    simp [SimpleGraph.edgeSet_injective.eq_iff]
  rw [he]
  exact (measurableSet_singleton _).preimage SimpleGraph.measurable_edgeSet

def fairBitLaw : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

instance : IsProbabilityMeasure fairBitLaw := by
  unfold fairBitLaw
  infer_instance

def uniformColoringLaw (N : ℕ) : Measure (Paper.Coloring N) :=
  Measure.pi (fun _ : Fin N => fairBitLaw)

instance (N : ℕ) : IsProbabilityMeasure (uniformColoringLaw N) := by
  unfold uniformColoringLaw
  infer_instance

def jointLaw (N : ℕ) (p : unitInterval) :
    Measure (Paper.Coloring N × Paper.Graph N) :=
  (uniformColoringLaw N).prod (Paper.graphLaw N p)

instance (N : ℕ) (p : unitInterval) : IsProbabilityMeasure (jointLaw N p) := by
  unfold jointLaw
  infer_instance

def consensusEvent (N : ℕ) (θ : ℝ) : Set (Paper.Coloring N × Paper.Graph N) :=
  {z | ∃ b : Bool, ∀ t : ℕ, Paper.convergenceDay θ ≤ t →
    ∀ v, Paper.coloringOnDay z.2 z.1 t v = b}

def RandomOpinionsTheorem : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ p : unitInterval, Paper.densityRange θ T N p →
        jointLaw N p (consensusEvent N θ)ᶜ ≤ ENNReal.ofReal ε

def flip {N : ℕ} (c : Paper.Coloring N) : Paper.Coloring N := fun v => !(c v)

@[simp] theorem flip_flip {N : ℕ} (c : Paper.Coloring N) : flip (flip c) = c := by
  funext v
  simp [flip]

theorem fairBitLaw_singleton (b : Bool) : fairBitLaw {b} = 1 / 2 := by
  simp [fairBitLaw, PMF.uniformOfFintype_apply]

theorem coloring_coordinates_independent (N : ℕ) :
    ProbabilityTheory.iIndepFun (fun v (c : Paper.Coloring N) => c v)
      (uniformColoringLaw N) :=
  ProbabilityTheory.iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

theorem coloring_coordinate_law (N : ℕ) (v : Fin N) :
    (uniformColoringLaw N).map (fun c => c v) = fairBitLaw :=
  (measurePreserving_eval (fun _ : Fin N => fairBitLaw) v).map_eq

end MajorityDynamics.Probability.RandomOpinionsReduction
