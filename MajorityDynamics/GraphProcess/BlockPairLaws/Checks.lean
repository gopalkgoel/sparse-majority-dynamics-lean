import MajorityDynamics.GraphProcess.BlockPairLaws.Main

/-! Expanded boundary checks and exact transitive dependency audits. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators Classical ENNReal
namespace MajorityDynamics.GraphProcess.BlockPairLaws.Checks
open Universal BlockDecomposition
variable {V : Type*} [Fintype V] {n : ℕ}

example (π : V → History (n+1)) (q : Local.Tilt n) (d : RowArray.Ambient π) :
    0 < RowArray.law π q {d} := law_singleton_pos π q d

example (y : Local.CoarseData V n) (q : Local.Tilt n) :
    0 < RowArray.law y.part q {d | RowArray.totals d = y.edge} := exactTotals_pos y q

example (y : Local.CoarseData V n) (q r : Local.Tilt n) :
    cond (RowArray.law y.part q) {d | RowArray.totals d = y.edge} =
      cond (RowArray.law y.part r) {d | RowArray.totals d = y.edge} := tilt_independent y q r

example (y : Local.CoarseData V n) (q : Local.Tilt n) :
    (cond (RowArray.law y.part q) {d | RowArray.totals d = y.edge}).map
      (fun d => (fun s => internalVector y.part d s, fun p => crossVector y.part d p)) =
      (Measure.pi fun s => internalBinomialLaw y.part y.edge s).prod
        (Measure.pi fun p => crossBinomialLaw y.part y.edge p) := binomial_components y q

example (y : Local.CoarseData V n) (q : Local.Tilt n)
    (A : ∀ s : History (n+1), Set (Block y.part s → ℕ))
    (B : ∀ p : Pair (History (n+1)),
      Set ((Block y.part p.val.1 → ℕ) × (Block y.part p.val.2 → ℕ))) :
    cond (RowArray.law y.part q) {d | RowArray.totals d = y.edge}
      {d | (∀ s, internalVector y.part d s ∈ A s) ∧ ∀ p, crossVector y.part d p ∈ B p} =
      (∏ s, internalBinomialLaw y.part y.edge s (A s)) *
        ∏ p, crossBinomialLaw y.part y.edge p (B p) := binomial_rectangle y q A B

example (y : Local.CoarseData V n) (d : RowArray.Ambient y.part) :
    GraphicalArray.law y.part y.edge {d} =
      (∏ s, internalGraphLaw y.part y.edge s {internalVector y.part d s}) *
        ∏ p, crossGraphLaw y.part y.edge p {crossVector y.part d p} := graphical_atom y d

example (y : Local.CoarseData V n) (q : Local.Tilt n) (d : RowArray.Ambient y.part) :
    cond (RowArray.law y.part q) {a | RowArray.totals a = y.edge} {d} =
      (∏ s, internalBinomialLaw y.part y.edge s {internalVector y.part d s}) *
        ∏ p, crossBinomialLaw y.part y.edge p {crossVector y.part d p} := binomial_atom y q d

example (y : Local.CoarseData V n) (s : History (n+1)) :
    internalGraphLaw y.part y.edge s =
      (uniformOn {G : SimpleGraph (Block y.part s) |
        G.edgeFinset.card = (y.edge s s / 2).toNat}).map (fun G v => G.degree v) :=
  internalGraphLaw_half_count y s

example (π : V → History (n+1))
    (m : History (n+1) → History (n+1) → ℤ) (s : History (n+1)) :
    internalBinomialLaw π m s =
      cond (Measure.pi fun _ : Block π s =>
        binomial (Local.partSizes π s - 1) (Binomial.closedProbability halfProbability))
        {a | ∑ v, (a v : ℤ) = m s s} := internalBinomialLaw_eq π m s

example (y : Local.CoarseData V n) (p : Pair (History (n+1))) :
    crossBinomialLaw y.part y.edge p =
      (cond (Measure.pi fun _ : Block y.part p.val.1 =>
        binomial (Local.partSizes y.part p.val.2) (Binomial.closedProbability halfProbability))
        {a | ∑ v, (a v : ℤ) = y.edge p.val.1 p.val.2}).prod
      (cond (Measure.pi fun _ : Block y.part p.val.2 =>
        binomial (Local.partSizes y.part p.val.1) (Binomial.closedProbability halfProbability))
        {a | ∑ v, (a v : ℤ) = y.edge p.val.1 p.val.2}) := crossBinomialLaw_eq y p

example (y : Local.CoarseData V n) (q : Local.Tilt n) (d : RowArray.Ambient y.part)
    (hd : RowArray.totals d = y.edge) :
    0 < cond (RowArray.law y.part q) {a | RowArray.totals a = y.edge} {d} :=
  binomial_atom_pos y q d hd

/-- info: 'MajorityDynamics.GraphProcess.BlockPairLaws.halfProbability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms halfProbability
/-- info: 'MajorityDynamics.GraphProcess.BlockPairLaws.halfTilt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms halfTilt
/-- info: 'MajorityDynamics.GraphProcess.BlockPairLaws.naturalCellsEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms naturalCellsEquiv
/-- info: 'MajorityDynamics.GraphProcess.BlockPairLaws.packEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms packEquiv
/-- info: 'MajorityDynamics.GraphProcess.BlockPairLaws.law_singleton_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms law_singleton_pos
/-- info: 'MajorityDynamics.GraphProcess.BlockPairLaws.exactTotals_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exactTotals_pos
/-- info: 'MajorityDynamics.GraphProcess.BlockPairLaws.conditioned_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms conditioned_probability
/-- info: 'MajorityDynamics.GraphProcess.BlockPairLaws.tilt_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tilt_independent
/-- info: 'MajorityDynamics.GraphProcess.BlockPairLaws.tilt_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tilt_half
/-- info: 'MajorityDynamics.GraphProcess.BlockPairLaws.natural_cells_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms natural_cells_law
/-- info: 'MajorityDynamics.GraphProcess.BlockPairLaws.cells_totals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cells_totals
/-- info: 'MajorityDynamics.GraphProcess.BlockPairLaws.cellTotal_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cellTotal_pos
/-- info: 'MajorityDynamics.GraphProcess.BlockPairLaws.cellCondition_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cellCondition_probability
/-- info: 'MajorityDynamics.GraphProcess.BlockPairLaws.cells_conditioned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cells_conditioned
/-- info: 'MajorityDynamics.GraphProcess.BlockPairLaws.ordered_cell_rectangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ordered_cell_rectangle
/-- info: 'MajorityDynamics.GraphProcess.BlockPairLaws.conditioned_components' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms conditioned_components
/-- info: 'MajorityDynamics.GraphProcess.BlockPairLaws.internalGraphLaw_half_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms internalGraphLaw_half_count
/-- info: 'MajorityDynamics.GraphProcess.BlockPairLaws.internalGraphLaw_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms internalGraphLaw_probability
/-- info: 'MajorityDynamics.GraphProcess.BlockPairLaws.crossGraphLaw_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms crossGraphLaw_probability
/-- info: 'MajorityDynamics.GraphProcess.BlockPairLaws.graphical_rectangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms graphical_rectangle
/-- info: 'MajorityDynamics.GraphProcess.BlockPairLaws.graphical_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms graphical_atom
/-- info: 'MajorityDynamics.GraphProcess.BlockPairLaws.internalBinomialLaw_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms internalBinomialLaw_probability
/-- info: 'MajorityDynamics.GraphProcess.BlockPairLaws.crossBinomialLaw_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms crossBinomialLaw_probability
/-- info: 'MajorityDynamics.GraphProcess.BlockPairLaws.cellCondition_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cellCondition_support
/-- info: 'MajorityDynamics.GraphProcess.BlockPairLaws.cross_binomial_rectangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cross_binomial_rectangle
/-- info: 'MajorityDynamics.GraphProcess.BlockPairLaws.binomial_components' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms binomial_components
/-- info: 'MajorityDynamics.GraphProcess.BlockPairLaws.binomial_rectangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms binomial_rectangle
/-- info: 'MajorityDynamics.GraphProcess.BlockPairLaws.binomial_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms binomial_atom
/-- info: 'MajorityDynamics.GraphProcess.BlockPairLaws.binomial_atom_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms binomial_atom_pos
/-- info: 'MajorityDynamics.GraphProcess.BlockPairLaws.enum_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms enum_factor

end MajorityDynamics.GraphProcess.BlockPairLaws.Checks
