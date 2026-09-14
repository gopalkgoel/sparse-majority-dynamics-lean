import MajorityDynamics.GraphProcess.NonLumpability.Main

noncomputable section
open MeasureTheory
namespace MajorityDynamics.GraphProcess.NonLumpability.Checks
open FineState CoarseKernel NonLumpability

example (b : Bool) : state b = actualState (graph b) coloring 0 := rfl

example (b : Bool) : (state b).part = fun v => (Universal.bits 1).symm (fun _ => coloring v) :=
  state_part b

example (b a c : Bool) :
    History.edgeTotals (state b).part (state b).deg (label a) (label c) =
      if a = c then 8 else 4 := state_edges b a c

example (b : Bool) : (rho (1 / 2 : ℝ) (state b)).reg = true := state_reg b

example : rho (1 / 2 : ℝ) (actualState (graph false) coloring 0) =
    rho (1 / 2 : ℝ) (actualState (graph true) coloring 0) := same_coarse

example : ((FineKernel.K (state false)).map (rho (1 / 2 : ℝ)))
    {y | Local.partSizes y.part (Universal.append (label false) false) = 4} = 1 :=
  first_probability

example : ((FineKernel.K (state true)).map (rho (1 / 2 : ℝ)))
    {y | Local.partSizes y.part (Universal.append (label false) false) = 4} = 0 :=
  second_probability

example : ¬ ∃ Q : Local.CoarseData (Fin 8) 0 → Measure (Local.CoarseData (Fin 8) 1),
    ∀ σ : FineState.State (Fin 8) 0,
      (FineKernel.K σ).map (CoarseKernel.rho (1 / 2 : ℝ)) =
        Q (CoarseKernel.rho (1 / 2 : ℝ) σ) := no_coarse_kernel

end MajorityDynamics.GraphProcess.NonLumpability.Checks

/-- info: 'MajorityDynamics.GraphProcess.NonLumpability.state_part' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.NonLumpability.state_part

/-- info: 'MajorityDynamics.GraphProcess.NonLumpability.state_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.NonLumpability.state_degree

/-- info: 'MajorityDynamics.GraphProcess.NonLumpability.rawDegree_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.NonLumpability.rawDegree_bounds

/-- info: 'MajorityDynamics.GraphProcess.NonLumpability.partition_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.NonLumpability.partition_size

/-- info: 'MajorityDynamics.GraphProcess.NonLumpability.state_edges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.NonLumpability.state_edges

/-- info: 'MajorityDynamics.GraphProcess.NonLumpability.threshold_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.NonLumpability.threshold_lower

/-- info: 'MajorityDynamics.GraphProcess.NonLumpability.state_regular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.NonLumpability.state_regular

/-- info: 'MajorityDynamics.GraphProcess.NonLumpability.state_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.NonLumpability.state_reg

/-- info: 'MajorityDynamics.GraphProcess.NonLumpability.same_coarse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.NonLumpability.same_coarse

/-- info: 'MajorityDynamics.GraphProcess.NonLumpability.next_color' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.NonLumpability.next_color

/-- info: 'MajorityDynamics.GraphProcess.NonLumpability.state_refinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.NonLumpability.state_refinement

/-- info: 'MajorityDynamics.GraphProcess.NonLumpability.refinement_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.NonLumpability.refinement_size

/-- info: 'MajorityDynamics.GraphProcess.NonLumpability.projected_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.NonLumpability.projected_probability

/-- info: 'MajorityDynamics.GraphProcess.NonLumpability.first_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.NonLumpability.first_probability

/-- info: 'MajorityDynamics.GraphProcess.NonLumpability.second_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.NonLumpability.second_probability

/-- info: 'MajorityDynamics.GraphProcess.NonLumpability.no_coarse_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.NonLumpability.no_coarse_kernel
