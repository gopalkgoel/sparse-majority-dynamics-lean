import MajorityDynamics.GraphProcess.LocalTransition.Main

noncomputable section
open MeasureTheory ProbabilityTheory
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.LocalTransition.Checks
open Universal
universe u

theorem original_deterministic {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n) (φ : ℝ),
      Local.Admissible y q T φ p → ∀ Cf Cs : ℝ, 0 ≤ Cf → 0 ≤ Cs →
      ∀ (σ : FineState.State V n) (τ : FineState.State V (n+1)),
      CoarseKernel.rho p σ = y → ((∀ s b, |((RowArray.childSet (RowArray.stateArray σ) s b).card : ℝ) -
          Local.templateSizes y.sizes q (append s b)| ≤
          Cf * (Real.sqrt (Fintype.card V) * Real.log (Fintype.card V))) ∧
        (∀ s t b, |(RowArray.childMass (RowArray.stateArray σ) s b t : ℝ) -
          Local.templateHalfEdges y.sizes q (append s b) t| ≤
          Cf * ((Fintype.card V : ℝ)^2 * p / Real.sqrt (Fintype.card V) *
            Real.log (Fintype.card V)))) → (τ.part = FineState.refinement σ ∧ CoarseKernel.Regular p τ.part τ.deg ∧
        ∀ s t b c, |(CoarseKernel.rho p τ).realEdges (append s b) (append t c) -
          (RowArray.childMass (RowArray.stateArray σ) s b t : ℝ) *
            (RowArray.childMass (RowArray.stateArray σ) t c s : ℝ) / y.realEdges s t| ≤
          Cs * ((Fintype.card V : ℝ)^2 * p *
            Real.sqrt ((p * Fintype.card V)^((1:ℝ)/7)/(Fintype.card V : ℝ)) *
            Real.log (Fintype.card V))) →
      ((∀ v, parent ((CoarseKernel.rho p τ).part v) = y.part v) ∧ (CoarseKernel.rho p τ).reg = true ∧
        (∀ s b, |((CoarseKernel.rho p τ).sizes (append s b) : ℝ) - Local.templateSizes y.sizes q (append s b)| ≤
          (Cf+Cs) * (Real.sqrt (Fintype.card V) * Real.log (Fintype.card V))) ∧
        (∀ s t b c, |(CoarseKernel.rho p τ).realEdges (append s b) (append t c) -
          Local.templateEdges y.sizes y.realEdges q (append s b) (append t c)| ≤
          (Cf+Cs) * ((Fintype.card V : ℝ)^2 * p *
            Real.sqrt ((p * Fintype.card V)^((1:ℝ)/7)/(Fintype.card V : ℝ)) *
            Real.log (Fintype.card V)))) := by
  simpa only [FiberGood, KernelGood, LocalSuccess, Refines, sizeScale, massScale, edgeScale] using
    (uniform_deterministic n hθlo hθhi hT)

theorem original_probability {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : unitInterval, T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) →
      (p : ℝ) < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n) (φ : ℝ),
      Local.Admissible y q T φ p → ∀ Cf Cs epsf epss : ℝ,
      0 ≤ Cf → 0 ≤ Cs → 0 ≤ epsf → 0 ≤ epss →
      ((CoarseKernel.Lambda p y).real {σ | ¬ ((∀ s b, |((RowArray.childSet (RowArray.stateArray σ) s b).card : ℝ) -
          Local.templateSizes y.sizes q (append s b)| ≤
          Cf * (Real.sqrt (Fintype.card V) * Real.log (Fintype.card V))) ∧
        (∀ s t b, |(RowArray.childMass (RowArray.stateArray σ) s b t : ℝ) -
          Local.templateHalfEdges y.sizes q (append s b) t| ≤
          Cf * ((Fintype.card V : ℝ)^2 * p / Real.sqrt (Fintype.card V) *
            Real.log (Fintype.card V))))} ≤ epsf) →
      (∀ σ, CoarseKernel.rho p σ = y → ((∀ s b, |((RowArray.childSet (RowArray.stateArray σ) s b).card : ℝ) -
          Local.templateSizes y.sizes q (append s b)| ≤
          Cf * (Real.sqrt (Fintype.card V) * Real.log (Fintype.card V))) ∧
        (∀ s t b, |(RowArray.childMass (RowArray.stateArray σ) s b t : ℝ) -
          Local.templateHalfEdges y.sizes q (append s b) t| ≤
          Cf * ((Fintype.card V : ℝ)^2 * p / Real.sqrt (Fintype.card V) *
            Real.log (Fintype.card V)))) →
        (FineKernel.K σ).real {τ | ¬ (τ.part = FineState.refinement σ ∧ CoarseKernel.Regular p τ.part τ.deg ∧
        ∀ s t b c, |(CoarseKernel.rho p τ).realEdges (append s b) (append t c) -
          (RowArray.childMass (RowArray.stateArray σ) s b t : ℝ) *
            (RowArray.childMass (RowArray.stateArray σ) t c s : ℝ) / y.realEdges s t| ≤
          Cs * ((Fintype.card V : ℝ)^2 * p *
            Real.sqrt ((p * Fintype.card V)^((1:ℝ)/7)/(Fintype.card V : ℝ)) *
            Real.log (Fintype.card V)))} ≤ epss) →
      IsProbabilityMeasure (CoarseKernel.Lambda p y) ∧
      IsProbabilityMeasure (CoarseKernel.Kbar p y) ∧
      CoarseKernel.Lambda p y {σ | CoarseKernel.rho p σ = y} = 1 ∧
      (CoarseKernel.Kbar p y).real {z | ¬ ((∀ v, parent (z.part v) = y.part v) ∧ z.reg = true ∧
        (∀ s b, |(z.sizes (append s b) : ℝ) - Local.templateSizes y.sizes q (append s b)| ≤
          (Cf+Cs) * (Real.sqrt (Fintype.card V) * Real.log (Fintype.card V))) ∧
        (∀ s t b c, |z.realEdges (append s b) (append t c) -
          Local.templateEdges y.sizes y.realEdges q (append s b) (append t c)| ≤
          (Cf+Cs) * ((Fintype.card V : ℝ)^2 * p *
            Real.sqrt ((p * Fintype.card V)^((1:ℝ)/7)/(Fintype.card V : ℝ)) *
            Real.log (Fintype.card V))))} ≤ epsf+epss := by
  simpa only [FiberGood, KernelGood, LocalSuccess, Refines, sizeScale, massScale, edgeScale] using
    (uniform_failure n hθlo hθhi hT)

theorem literal_refinement {V : Type*} [Fintype V] {n : ℕ}
    (π : V → History (n+1)) (π' : V → History (n+2)) :
    (∀ v, parent (π' v) = π v) ↔ ∀ s,
      Disjoint (History.block π' (append s false)) (History.block π' (append s true)) ∧
      History.block π' (append s false) ∪ History.block π' (append s true) =
        History.block π s := refines_iff_children π π'

theorem coefficient_one_adapter {V : Type*} [Fintype V] {n : ℕ}
    (y : Local.CoarseData V n) (q : Local.Tilt n) (p : ℝ)
    (σ : FineState.State V n) (d : RowArray.Ambient y.part)
    (hp : σ.part = y.part) (hd : σ.deg = RowArray.values d)
    (h2 : RowConcentration.R2 y q d) (h3 : RowConcentration.R3 y p q d) :
    (∀ s b, |((RowArray.childSet (RowArray.stateArray σ) s b).card : ℝ) -
      Local.templateSizes y.sizes q (append s b)| ≤
      Real.sqrt (Fintype.card V) * Real.log (Fintype.card V)) ∧
    (∀ s t b, |(RowArray.childMass (RowArray.stateArray σ) s b t : ℝ) -
      Local.templateHalfEdges y.sizes q (append s b) t| ≤
      (Fintype.card V : ℝ)^2 * p / Real.sqrt (Fintype.card V) * Real.log (Fintype.card V)) := by
  simpa only [FiberGood, one_mul, sizeScale, massScale] using
    fiberGood_of_rows y q p σ d hp hd h2 h3

theorem literal_scale (N : ℕ) (p : ℝ) (hN : 0 < (N : ℝ)) (hp : 0 < p) :
    (N : ℝ)^2 * p * Real.sqrt ((p*N)^((1:ℝ)/7)/(N : ℝ)) * Real.log (N : ℝ) =
      (p*N)^((1:ℝ)/14) * ((N : ℝ)^2*p/Real.sqrt (N : ℝ)*Real.log (N : ℝ)) :=
  edgeScale_eq N p hN hp

/-- Day index zero is included without changing the event or assumptions. -/
example {θ T : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V 0) (q : Local.Tilt 0) (φ : ℝ),
      Local.Admissible y q T φ p → ∀ Cf Cs : ℝ, 0 ≤ Cf → 0 ≤ Cs →
      ∀ (σ : FineState.State V 0) (τ : FineState.State V 1),
      CoarseKernel.rho p σ = y → FiberGood y q p Cf σ → KernelGood y p Cs σ τ →
      LocalSuccess y q p (Cf+Cs) (CoarseKernel.rho p τ) :=
  uniform_deterministic 0 hθlo hθhi hT

theorem original_typical_probability {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : unitInterval, T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) →
      (p : ℝ) < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n) (φ : ℝ),
      Local.Admissible y q T φ p → ∀ Cf Cs epsf epss : ℝ,
      0 ≤ Cf → 0 ≤ Cs → 0 ≤ epsf → 0 ≤ epss →
      ((CoarseKernel.Lambda p y).real {σ | ¬ ((∀ v t, |(σ.deg v t : ℝ) - p * y.sizes t| ≤
          Real.sqrt (p * Fintype.card V) * Real.log (Fintype.card V)^(2/3 : ℝ)) ∧
        ((∀ s b, |((RowArray.childSet (RowArray.stateArray σ) s b).card : ℝ) -
          Local.templateSizes y.sizes q (append s b)| ≤
          Cf * (Real.sqrt (Fintype.card V) * Real.log (Fintype.card V))) ∧
        (∀ s t b, |(RowArray.childMass (RowArray.stateArray σ) s b t : ℝ) -
          Local.templateHalfEdges y.sizes q (append s b) t| ≤
          Cf * ((Fintype.card V : ℝ)^2 * p / Real.sqrt (Fintype.card V) *
            Real.log (Fintype.card V)))))} ≤ epsf) →
      (∀ σ, CoarseKernel.rho p σ = y → ((∀ v t, |(σ.deg v t : ℝ) - p * y.sizes t| ≤
          Real.sqrt (p * Fintype.card V) * Real.log (Fintype.card V)^(2/3 : ℝ)) ∧
        ((∀ s b, |((RowArray.childSet (RowArray.stateArray σ) s b).card : ℝ) -
          Local.templateSizes y.sizes q (append s b)| ≤
          Cf * (Real.sqrt (Fintype.card V) * Real.log (Fintype.card V))) ∧
        (∀ s t b, |(RowArray.childMass (RowArray.stateArray σ) s b t : ℝ) -
          Local.templateHalfEdges y.sizes q (append s b) t| ≤
          Cf * ((Fintype.card V : ℝ)^2 * p / Real.sqrt (Fintype.card V) *
            Real.log (Fintype.card V))))) →
        (FineKernel.K σ).real {τ | ¬ (τ.part = FineState.refinement σ ∧ CoarseKernel.Regular p τ.part τ.deg ∧
        ∀ s t b c, |(CoarseKernel.rho p τ).realEdges (append s b) (append t c) -
          (RowArray.childMass (RowArray.stateArray σ) s b t : ℝ) *
            (RowArray.childMass (RowArray.stateArray σ) t c s : ℝ) / y.realEdges s t| ≤
          Cs * ((Fintype.card V : ℝ)^2 * p *
            Real.sqrt ((p * Fintype.card V)^((1:ℝ)/7)/(Fintype.card V : ℝ)) *
            Real.log (Fintype.card V)))} ≤ epss) →
      IsProbabilityMeasure (CoarseKernel.Lambda p y) ∧
      IsProbabilityMeasure (CoarseKernel.Kbar p y) ∧
      CoarseKernel.Lambda p y {σ | CoarseKernel.rho p σ = y} = 1 ∧
      (CoarseKernel.Kbar p y).real {z | ¬ ((∀ v, parent (z.part v) = y.part v) ∧ z.reg = true ∧
        (∀ s b, |(z.sizes (append s b) : ℝ) - Local.templateSizes y.sizes q (append s b)| ≤
          (Cf+Cs) * (Real.sqrt (Fintype.card V) * Real.log (Fintype.card V))) ∧
        (∀ s t b c, |z.realEdges (append s b) (append t c) -
          Local.templateEdges y.sizes y.realEdges q (append s b) (append t c)| ≤
          (Cf+Cs) * ((Fintype.card V : ℝ)^2 * p *
            Real.sqrt ((p * Fintype.card V)^((1:ℝ)/7)/(Fintype.card V : ℝ)) *
            Real.log (Fintype.card V))))} ≤ epsf+epss := by
  simpa only [FiberTypical, FiberGood, KernelGood, LocalSuccess, Refines,
    sizeScale, massScale, edgeScale] using uniform_typical_failure n hθlo hθhi hT

end MajorityDynamics.GraphProcess.LocalTransition.Checks

/-- info: 'MajorityDynamics.GraphProcess.LocalTransition.quotient_difference_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.LocalTransition.quotient_difference_le

/-- info: 'MajorityDynamics.GraphProcess.LocalTransition.edgeScale_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.LocalTransition.edgeScale_eq

/-- info: 'MajorityDynamics.GraphProcess.LocalTransition.uniform_numerical_regime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.LocalTransition.uniform_numerical_regime

/-- info: 'MajorityDynamics.GraphProcess.LocalTransition.templateHalfEdges_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.LocalTransition.templateHalfEdges_nonneg

/-- info: 'MajorityDynamics.GraphProcess.LocalTransition.templateHalfEdges_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.LocalTransition.templateHalfEdges_bounds

/-- info: 'MajorityDynamics.GraphProcess.LocalTransition.childMass_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.LocalTransition.childMass_nonneg

/-- info: 'MajorityDynamics.GraphProcess.LocalTransition.childMass_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.LocalTransition.childMass_bounds

/-- info: 'MajorityDynamics.GraphProcess.LocalTransition.refines_iff_children' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.LocalTransition.refines_iff_children

/-- info: 'MajorityDynamics.GraphProcess.LocalTransition.K_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.LocalTransition.K_split

/-- info: 'MajorityDynamics.GraphProcess.LocalTransition.fiberGood_of_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.LocalTransition.fiberGood_of_rows

/-- info: 'MajorityDynamics.GraphProcess.LocalTransition.mass_quotient_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.LocalTransition.mass_quotient_error

/-- info: 'MajorityDynamics.GraphProcess.LocalTransition.deterministic_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.LocalTransition.deterministic_finite

/-- info: 'MajorityDynamics.GraphProcess.LocalTransition.uniform_deterministic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.LocalTransition.uniform_deterministic

/-- info: 'MajorityDynamics.GraphProcess.LocalTransition.Kbar_real_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.LocalTransition.Kbar_real_apply

/-- info: 'MajorityDynamics.GraphProcess.LocalTransition.Kbar_failure_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.LocalTransition.Kbar_failure_le

/-- info: 'MajorityDynamics.GraphProcess.LocalTransition.finite_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.LocalTransition.finite_failure

/-- info: 'MajorityDynamics.GraphProcess.LocalTransition.Checks.original_deterministic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.LocalTransition.Checks.original_deterministic

/-- info: 'MajorityDynamics.GraphProcess.LocalTransition.uniform_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.LocalTransition.uniform_failure

/-- info: 'MajorityDynamics.GraphProcess.LocalTransition.Checks.original_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.LocalTransition.Checks.original_probability

/-- info: 'MajorityDynamics.GraphProcess.LocalTransition.Checks.literal_refinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.LocalTransition.Checks.literal_refinement

/-- info: 'MajorityDynamics.GraphProcess.LocalTransition.Checks.coefficient_one_adapter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.LocalTransition.Checks.coefficient_one_adapter

/-- info: 'MajorityDynamics.GraphProcess.LocalTransition.Checks.literal_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.LocalTransition.Checks.literal_scale

/-- info: 'MajorityDynamics.GraphProcess.LocalTransition.fiberTypical_of_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.LocalTransition.fiberTypical_of_good

/-- info: 'MajorityDynamics.GraphProcess.LocalTransition.uniform_typical_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.LocalTransition.uniform_typical_failure

/-- info: 'MajorityDynamics.GraphProcess.LocalTransition.Checks.original_typical_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.LocalTransition.Checks.original_typical_probability
