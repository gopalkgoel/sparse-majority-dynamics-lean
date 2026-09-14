import MajorityDynamics.GraphProcess.LocalTheorem.Main

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.LocalTheorem
open Universal
universe u

/-- Expanded original L1-L4 contract, including real templates, original kappa
flag, exact unrounded error scales and ordered diagonal incidences. -/
example {V : Type u} [Fintype V] {n : ℕ}
    (y : Local.CoarseData V n) (q : Local.Tilt n) (p C : ℝ)
    (z : Local.CoarseData V (n+1)) :
    LocalTransition.LocalSuccess y q p C z ↔
      (∀ v, parent (z.part v) = y.part v) ∧ z.reg = true ∧
      (∀ s b, |(z.sizes (append s b) : ℝ)-Local.templateSizes y.sizes q (append s b)| ≤
        C * (Real.sqrt (Fintype.card V) * Real.log (Fintype.card V))) ∧
      (∀ s t b c, |z.realEdges (append s b) (append t c)-
        Local.templateEdges y.sizes y.realEdges q (append s b) (append t c)| ≤
        C * ((Fintype.card V : ℝ)^2 * p *
          Real.sqrt ((p * Fintype.card V)^((1:ℝ)/7) / Fintype.card V) *
          Real.log (Fintype.card V))) := Iff.rfl

/-- Full original-input theorem at every paper day k=n+1; no transfer,
concentration, comparison or attainability premise is left in this consumer. -/
example {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : unitInterval, T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) →
      (p : ℝ) < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.Admissible y q T φ p →
      IsProbabilityMeasure (CoarseKernel.Kbar p y) ∧
      (CoarseKernel.Kbar p y).real {z | ¬ LocalTransition.LocalSuccess y q p C z} ≤ ε ∧
      1-ε ≤ (CoarseKernel.Kbar p y).real {z | LocalTransition.LocalSuccess y q p C z} :=
  local_coarse_transition n hθlo hθhi hT hφ hφ1

example {θ T φ : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) : LocalCoarseTransitionRealTheorem.{u} θ T φ 0 :=
  local_coarse_transition_real 0 hθlo hθhi hT hφ hφ1

end MajorityDynamics.GraphProcess.LocalTheorem

/-- info: 'MajorityDynamics.GraphProcess.LocalTheorem.fiber_degree_array_estimates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.LocalTheorem.fiber_degree_array_estimates

/-- info: 'MajorityDynamics.GraphProcess.LocalTheorem.local_coarse_transition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.LocalTheorem.local_coarse_transition

/-- info: 'MajorityDynamics.GraphProcess.LocalTheorem.local_coarse_transition_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.LocalTheorem.local_coarse_transition_real
