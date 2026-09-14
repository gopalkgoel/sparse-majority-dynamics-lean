import MajorityDynamics.Probability.ConditionedBinomialBox.Main

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace MajorityDynamics.Probability.ConditionedBinomialBox

-- The finite set has literal consecutive coordinate intervals, not only a cardinality.
example {d : ℕ} (a : Fin d → ℕ) (L : ℕ) (x : Fin d → ℕ) :
    x ∈ Geometry.box a L ↔ ∀ i, a i ≤ x i ∧ x i < a i+L :=
  Geometry.mem_box a L x

example {d : ℕ} (a : Fin d → ℕ) (L : ℕ) : (Geometry.box a L).card = L^d :=
  Geometry.card_box a L

variable {r d N L : ℕ} {M : Fin r → Fin d → ℤ} {strict : Fin r → Bool}
  {p cWidth CWidth A cPoint cEvent β : ℝ} {η : Fin d → ℕ}
  {q : Fin d → Binomial.Probability} {a : Fin d → ℕ}

-- Original mixed event, support and fixed central window are concrete fields.
example (h : BoxConclusion M strict N p η q cWidth CWidth A cPoint cEvent β a L)
    (x : Fin d → ℕ) (hx : x ∈ Geometry.box a L) :
    (∀ i, x i ≤ η i) ∧
    (∀ j, 0 < ∑ i, (M j i : ℝ)*(x i : ℝ)) ∧
    x ∈ Binomial.inequalityEvent (fun j i => (M j i : ℝ)) strict ∧
    ∀ i, |(x i : ℝ)-(η i : ℝ)*(q i : ℝ)| ≤
      A*Real.sqrt ((η i : ℝ)*(q i : ℝ)) :=
  ⟨h.support x hx, h.slack x hx, h.inside x hx, h.window x hx⟩

-- Both atom bounds use the actual product law and actual normalized restriction.
example (h : BoxConclusion M strict N p η q cWidth CWidth A cPoint cEvent β a L)
    (x : Fin d → ℕ) (hx : x ∈ Geometry.box a L) :
    cPoint*(p*N)^(-(d : ℝ)/2) ≤ (Binomial.law η q).real {x} ∧
    cPoint*(p*N)^(-(d : ℝ)/2) ≤
      (cond (Binomial.law η q)
        (Binomial.inequalityEvent (fun j i => (M j i : ℝ)) strict)).real {x} :=
  ⟨h.point x hx, h.conditioned_point x hx⟩

example (h : BoxConclusion M strict N p η q cWidth CWidth A cPoint cEvent β a L) :
    cEvent ≤ (Binomial.law η q).real (Geometry.box a L : Set (Fin d → ℕ)) ∧
    cEvent ≤ (Binomial.law η q).real
      (Binomial.inequalityEvent (fun j i => (M j i : ℝ)) strict) ∧
    IsProbabilityMeasure
      (cond (Binomial.law η q) (Binomial.inequalityEvent (fun j i => (M j i : ℝ)) strict)) :=
  ⟨h.box_mass, h.event_mass, h.conditioned_probability⟩

example (h : BoxConclusion M strict N p η q cWidth CWidth A cPoint cEvent β a L) :
    ∃ ν : Measure (Fin d → ℕ), IsProbabilityMeasure ν ∧
      cond (Binomial.law η q)
        (Binomial.inequalityEvent (fun j i => (M j i : ℝ)) strict) =
        ENNReal.ofReal β • uniformBox (Geometry.box a L) + ENNReal.ofReal (1-β) • ν :=
  h.mixture

-- Expanded closed endpoint: constants before all varying data; no geometric,
-- event-mass, atom-bound or mixture certificate is an input.
example (θ : ℝ) (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (d : ℕ) (hd : 1 ≤ d) (r : ℕ) (M : Fin r → Fin d → ℤ)
    (hM : Binomial.Approximation.OrthogonalRows M) (strict : Fin r → Bool)
    (T : ℝ) (hT : 1 < T) :
    ∃ cWidth CWidth β : ℝ, 0 < cWidth ∧ 0 < CWidth ∧ 0 < β ∧ β < 1 ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹ * (N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-θ) →
      ∀ (η : Fin d → ℕ) (q : Fin d → Binomial.Probability),
      (∀ i, (N : ℝ)/T ≤ (η i : ℝ)) →
      (∀ i, (η i : ℝ) ≤ T*N) →
      (∀ i, |(q i : ℝ)-p| ≤ T*p/Real.sqrt (p*N)) →
      (∀ j, |∑ i, (M j i : ℝ)*(η i : ℝ)| ≤ T*N/Real.sqrt (p*N)) →
      ∃ (a : Fin d → ℕ) (L : ℕ) (ν : Measure (Fin d → ℕ)),
        1 ≤ L ∧ cWidth*Real.sqrt (p*N) ≤ (L : ℝ) ∧
        (L : ℝ) ≤ CWidth*Real.sqrt (p*N) ∧ IsProbabilityMeasure ν ∧
        cond (Binomial.law η q)
          (Binomial.inequalityEvent (fun j i => (M j i : ℝ)) strict) =
          ENNReal.ofReal β • uniformBox (Geometry.box a L) + ENNReal.ofReal (1-β) • ν :=
  uniform_rectangular_mixture θ hθlo hθhi d hd r M hM strict T hT

end MajorityDynamics.Probability.ConditionedBinomialBox

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.uniform_regime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialBox.uniform_regime

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.GeometryScalar.coordinate_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialBox.GeometryScalar.coordinate_bounds

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.mem_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.mem_box

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.card_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.card_box

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.box_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.box_nonempty

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.matrixBound_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.matrixBound_one

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.width_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.width_pos

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.width_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.width_le_one

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.driftBound_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.driftBound_pos

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.window_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.window_pos

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.row_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.row_abs_le

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.column_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.column_abs_le

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.row_square_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.row_square_one

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.row_drift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.row_drift

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.center_deviation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.center_deviation

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.width_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.width_bounds

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.rounded_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.rounded_bounds

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.rounding_row_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.rounding_row_error

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.box_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.box_slack

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.event_of_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.event_of_slack

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.construct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialBox.Geometry.construct

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.atom_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialBox.atom_product

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.sqrt_pow_eq_rpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialBox.sqrt_pow_eq_rpow

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.coordinate_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialBox.coordinate_power

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.central_product_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialBox.central_product_lower

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.width_point_cancellation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialBox.width_point_cancellation

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.assemble' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialBox.assemble

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.uniform_component' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialBox.uniform_component

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.uniform_rectangular_mixture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialBox.uniform_rectangular_mixture

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.unconstrained_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialBox.unconstrained_event

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialBox.unconstrained_conditioning' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialBox.unconstrained_conditioning
