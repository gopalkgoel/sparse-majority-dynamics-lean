import MajorityDynamics.GraphProcess.BlockCountProbability.Finite

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.BlockCountProbability
open BlockDecomposition
variable {V : Type*} [Fintype V] {n : ℕ}

example (p : unitInterval) (y : Local.CoarseData V n) :
    (SimpleGraph.binomialRandom V p).real
      {G : SimpleGraph V | History.edgeTotals y.part (History.degreeArray y.part G) = y.edge} =
    (∏ s, (ProbabilityTheory.binomial ((y.sizes s).choose 2) p).real
      {(y.edge s s / 2).toNat}) *
    (∏ z : BlockDecomposition.Pair (Universal.History (n+1)),
      (ProbabilityTheory.binomial (y.sizes z.val.1 * y.sizes z.val.2) p).real
        {(y.edge z.val.1 z.val.2).toNat}) := exact_factorization p y

example (y : Local.CoarseData V n) (s : Universal.History (n+1)) :
    2 * (((y.edge s s / 2).toNat : ℕ) : ℤ) = y.edge s s := diagonal_target_cast y s

end MajorityDynamics.GraphProcess.BlockCountProbability

/-- info: 'MajorityDynamics.GraphProcess.BlockCountProbability.internalSites_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.BlockCountProbability.internalSites_card

/-- info: 'MajorityDynamics.GraphProcess.BlockCountProbability.crossSites_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.BlockCountProbability.crossSites_card

/-- info: 'MajorityDynamics.GraphProcess.BlockCountProbability.signature_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.BlockCountProbability.signature_injective

/-- info: 'MajorityDynamics.GraphProcess.BlockCountProbability.sites_signature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.BlockCountProbability.sites_signature

/-- info: 'MajorityDynamics.GraphProcess.BlockCountProbability.sites_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.BlockCountProbability.sites_disjoint

/-- info: 'MajorityDynamics.GraphProcess.BlockCountProbability.sites_nondiag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.BlockCountProbability.sites_nondiag

/-- info: 'MajorityDynamics.GraphProcess.BlockCountProbability.internalSites_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.BlockCountProbability.internalSites_count

/-- info: 'MajorityDynamics.GraphProcess.BlockCountProbability.crossSites_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.BlockCountProbability.crossSites_count

/-- info: 'MajorityDynamics.GraphProcess.BlockCountProbability.diagonal_target_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.BlockCountProbability.diagonal_target_cast

/-- info: 'MajorityDynamics.GraphProcess.BlockCountProbability.cross_target_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.BlockCountProbability.cross_target_cast

/-- info: 'MajorityDynamics.GraphProcess.BlockCountProbability.fixedCount_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.BlockCountProbability.fixedCount_event

/-- info: 'MajorityDynamics.GraphProcess.BlockCountProbability.fixedCount_site_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.BlockCountProbability.fixedCount_site_event

/-- info: 'MajorityDynamics.GraphProcess.BlockCountProbability.exact_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.BlockCountProbability.exact_factorization

