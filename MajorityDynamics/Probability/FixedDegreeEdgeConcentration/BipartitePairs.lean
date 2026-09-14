import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.GraphPairs

/-! Actual left/right neighborhood deletion and one-sided bipartite joint bounds. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.Probability.FixedDegreeEdgeConcentration
open FixedDegreeSampling
variable {L R : Type*} [Fintype L] [Fintype R]

/-- Exact transposition of a cross-edge set. -/
def transposeCross (E : CrossEdges L R) : CrossEdges R L := {z | (z.2,z.1) ∈ E}

omit [Fintype L] [Fintype R] in
@[simp] theorem transposeCross_transpose (E : CrossEdges L R) :
    transposeCross (transposeCross E) = E := by ext ⟨v,w⟩; rfl

omit [Fintype R] in
@[simp] theorem transposeCross_leftDegree (E : CrossEdges L R) (w : R) :
    leftDegree (transposeCross E) w = rightDegree E w := rfl

omit [Fintype L] in
@[simp] theorem transposeCross_rightDegree (E : CrossEdges L R) (v : L) :
    rightDegree (transposeCross E) v = leftDegree E v := rfl

/-- Full fixed-degree families, including the empty case, transpose exactly. -/
def transposeFamily (a : L → ℕ) (b : R → ℕ) : bipartiteFamily a b ≃ bipartiteFamily b a where
  toFun E := ⟨transposeCross E.val, ⟨E.property.2,E.property.1⟩⟩
  invFun E := ⟨transposeCross E.val, ⟨E.property.2,E.property.1⟩⟩
  left_inv E := Subtype.ext (transposeCross_transpose E.val)
  right_inv E := Subtype.ext (transposeCross_transpose E.val)

/-- Deleting a right vertex is left deletion after transposition, then transposition back. -/
def deleteRight (u : R) (E : CrossEdges L R) : CrossEdges L (Remaining u) :=
  transposeCross (deleteLeft u (transposeCross E))

omit [Fintype L] [Fintype R] in
@[simp] theorem deleteRight_mem (u : R) (E : CrossEdges L R) (x : L) (y : Remaining u) :
    (x,y) ∈ deleteRight u E ↔ (x,y.val) ∈ E := Iff.rfl

/-- A feasible exact left neighborhood supplies both admissibility and an actual
residual realization; neither is assumed for invalid or empty fibers. -/
theorem bipartite_fiber_feasible (a : L → ℕ) (b : R → ℕ) (v : L) (S : Finset R)
    (h : (bipartiteFamily a b ∩ {E | leftNeighbors E v = S}).Nonempty) :
    bipartiteAdmissible a b v S ∧
      (bipartiteFamily (fun z : Remaining v => a z) (residualRightDegree b S)).Nonempty := by
  obtain ⟨E,hE⟩ := h
  have ha := bipartite_neighborhood_admissible a b v S ⟨E,hE⟩
  exact ⟨ha, ⟨_, ((bipartite_neighborhood_removal_equiv a b v S ha) ⟨E,hE⟩).property⟩⟩

/-- Transposition retains the exact prescribed neighborhood. -/
def transposeNeighborhood (a : L → ℕ) (b : R → ℕ) (u : R) (S : Finset L) :
    {E : CrossEdges L R // E ∈ bipartiteFamily a b ∧ rightNeighbors E u = S} ≃
      bipartiteNeighborhoodFiber b a u S where
  toFun E := ⟨transposeCross E.val, ⟨⟨E.property.1.2,E.property.1.1⟩,E.property.2⟩⟩
  invFun E := ⟨transposeCross E.val, ⟨⟨E.property.1.2,E.property.1.1⟩,E.property.2⟩⟩
  left_inv E := Subtype.ext (transposeCross_transpose E.val)
  right_inv E := Subtype.ext (transposeCross_transpose E.val)

/-- Exact right-neighborhood deletion, with the right carrier reduced and the
left degrees decremented. Valid even when the realization families are empty. -/
def bipartite_right_removal_equiv (a : L → ℕ) (b : R → ℕ) (u : R) (S : Finset L)
    (h : bipartiteAdmissible b a u S) :
    {E : CrossEdges L R // E ∈ bipartiteFamily a b ∧ rightNeighbors E u = S} ≃
      bipartiteFamily (residualRightDegree a S) (fun z : Remaining u => b z) :=
  (transposeNeighborhood a b u S).trans
    ((bipartite_neighborhood_removal_equiv b a u S h).trans
      (transposeFamily (fun z : Remaining u => b z) (residualRightDegree a S)))

@[simp] theorem bipartite_right_removal_val (a : L → ℕ) (b : R → ℕ)
    (u : R) (S : Finset L) (h : bipartiteAdmissible b a u S)
    (E : {E : CrossEdges L R // E ∈ bipartiteFamily a b ∧ rightNeighbors E u = S}) :
    (bipartite_right_removal_equiv a b u S h E).val = deleteRight u E.val := rfl

/-- The exact admissible left-neighborhood fiber has the actual residual edge law. -/
theorem bipartite_left_fiber_edge_probability (a : L → ℕ) (b : R → ℕ)
    (v x : L) (y : R) (hx : x ≠ v) (S : Finset R)
    (hS : bipartiteAdmissible a b v S) :
    (uniformOn (bipartiteFamily a b ∩ {E | leftNeighbors E v = S})).real
      {E | (x,y) ∈ E} =
      (bipartiteFixedDegreeLaw (fun z : Remaining v => a z)
        (residualRightDegree b S)).real {F | (⟨x,hx⟩,y) ∈ F} := by
  apply uniform_event_of_equiv _ _ (bipartite_neighborhood_removal_equiv a b v S hS)
  intro E
  rfl

/-- Right deletion preserves the surviving edge with its literal orientation. -/
theorem bipartite_right_fiber_edge_probability (a : L → ℕ) (b : R → ℕ)
    (u y : R) (x : L) (hy : y ≠ u) (S : Finset L)
    (hS : bipartiteAdmissible b a u S) :
    (uniformOn (bipartiteFamily a b ∩ {E | rightNeighbors E u = S})).real
      {E | (x,y) ∈ E} =
      (bipartiteFixedDegreeLaw (residualRightDegree a S)
        (fun z : Remaining u => b z)).real {F | (x,⟨y,hy⟩) ∈ F} := by
  apply uniform_event_of_equiv _ _ (bipartite_right_removal_equiv a b u S hS)
  intro E
  rfl

/-- Exact left-neighborhood disintegration, including zero-mass fibers. -/
theorem bipartite_left_neighborhood_edge_probability (a : L → ℕ) (b : R → ℕ)
    (v x : L) (y : R) (hx : x ≠ v) (S : Finset R)
    (hS : bipartiteAdmissible a b v S) :
    (bipartiteFixedDegreeLaw a b).real {E | leftNeighbors E v = S ∧ (x,y) ∈ E} =
      (bipartiteFixedDegreeLaw a b).real {E | leftNeighbors E v = S} *
      (bipartiteFixedDegreeLaw (fun z : Remaining v => a z)
        (residualRightDegree b S)).real {F | (⟨x,hx⟩,y) ∈ F} := by
  have he := uniformOn_inter (s := bipartiteFamily a b)
    (t := {E | leftNeighbors E v = S}) (u := {E | (x,y) ∈ E}) (Set.toFinite _)
  have hr := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_mul] at hr
  change _ = (uniformOn (bipartiteFamily a b ∩ {E | leftNeighbors E v = S})).real
    {E | (x,y) ∈ E} * _ at hr
  rw [bipartite_left_fiber_edge_probability a b v x y hx S hS] at hr
  simpa only [mul_comm, Measure.real, bipartiteFixedDegreeLaw, Set.ofPred_and] using hr

/-- Exact right-neighborhood disintegration, on the correctly reduced right carrier. -/
theorem bipartite_right_neighborhood_edge_probability (a : L → ℕ) (b : R → ℕ)
    (u y : R) (x : L) (hy : y ≠ u) (S : Finset L)
    (hS : bipartiteAdmissible b a u S) :
    (bipartiteFixedDegreeLaw a b).real {E | rightNeighbors E u = S ∧ (x,y) ∈ E} =
      (bipartiteFixedDegreeLaw a b).real {E | rightNeighbors E u = S} *
      (bipartiteFixedDegreeLaw (residualRightDegree a S)
        (fun z : Remaining u => b z)).real {F | (x,⟨y,hy⟩) ∈ F} := by
  have he := uniformOn_inter (s := bipartiteFamily a b)
    (t := {E | rightNeighbors E u = S}) (u := {E | (x,y) ∈ E}) (Set.toFinite _)
  have hr := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_mul] at hr
  change _ = (uniformOn (bipartiteFamily a b ∩ {E | rightNeighbors E u = S})).real
    {E | (x,y) ∈ E} * _ at hr
  rw [bipartite_right_fiber_edge_probability a b u y x hy S hS] at hr
  simpa only [mul_comm, Measure.real, bipartiteFixedDegreeLaw, Set.ofPred_and] using hr

/-- Actual one-sided joint bound by deleting the left endpoint outside the second
edge. Only feasible residual families need a bound; empty/invalid fibers vanish. -/
theorem bipartite_joint_le_of_left_residual (a : L → ℕ) (b : R → ℕ)
    (v x : L) (u y : R) (hx : x ≠ v) (B : ℝ)
    (hB : ∀ S : Finset R, bipartiteAdmissible a b v S →
      (bipartiteFamily (fun z : Remaining v => a z) (residualRightDegree b S)).Nonempty →
      (bipartiteFixedDegreeLaw (fun z : Remaining v => a z)
        (residualRightDegree b S)).real {F | (⟨x,hx⟩,y) ∈ F} ≤ B) :
    (bipartiteFixedDegreeLaw a b).real {E | (v,u) ∈ E ∧ (x,y) ∈ E} ≤
      (bipartiteFixedDegreeLaw a b).real {E | (v,u) ∈ E} * B := by
  have h := uniform_partition_upper (bipartiteFamily a b) (fun E => leftNeighbors E v)
    {S | u ∈ S} {E | (x,y) ∈ E} (B := B) (by
      intro S _ hS
      obtain ⟨ha,hn⟩ := bipartite_fiber_feasible a b v S hS
      rw [bipartite_left_fiber_edge_probability a b v x y hx S ha]
      exact hB S ha hn)
  simpa only [leftNeighbors, Finset.mem_filter, Finset.mem_univ, true_and,
    Set.mem_ofPred_eq, bipartiteFixedDegreeLaw] using h

/-- The complementary orientation: delete the right endpoint outside the second
edge. In particular this covers distinct edges sharing their left endpoint. -/
theorem bipartite_joint_le_of_right_residual (a : L → ℕ) (b : R → ℕ)
    (v x : L) (u y : R) (hy : y ≠ u) (B : ℝ)
    (hB : ∀ S : Finset L, bipartiteAdmissible b a u S →
      (bipartiteFamily (residualRightDegree a S) (fun z : Remaining u => b z)).Nonempty →
      (bipartiteFixedDegreeLaw (residualRightDegree a S)
        (fun z : Remaining u => b z)).real {F | (x,⟨y,hy⟩) ∈ F} ≤ B) :
    (bipartiteFixedDegreeLaw a b).real {E | (v,u) ∈ E ∧ (x,y) ∈ E} ≤
      (bipartiteFixedDegreeLaw a b).real {E | (v,u) ∈ E} * B := by
  have h := uniform_partition_upper (bipartiteFamily a b) (fun E => rightNeighbors E u)
    {S | v ∈ S} {E | (x,y) ∈ E} (B := B) (by
      intro S _ hS
      obtain ⟨E,hE⟩ := hS
      have ha := bipartite_neighborhood_admissible b a u S
        ((transposeNeighborhood a b u S) ⟨E,hE⟩)
      have hn := ((bipartite_right_removal_equiv a b u S ha) ⟨E,hE⟩).property
      rw [bipartite_right_fiber_edge_probability a b u y x hy S ha]
      exact hB S ha ⟨_,hn⟩)
  simpa only [rightNeighbors, Finset.mem_filter, Finset.mem_univ, true_and,
    Set.mem_ofPred_eq, bipartiteFixedDegreeLaw] using h

end MajorityDynamics.Probability.FixedDegreeEdgeConcentration

/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_fiber_feasible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_fiber_feasible

/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_left_fiber_edge_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_left_fiber_edge_probability

/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_right_fiber_edge_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_right_fiber_edge_probability

/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_left_neighborhood_edge_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_left_neighborhood_edge_probability

/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_right_neighborhood_edge_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_right_neighborhood_edge_probability

/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_joint_le_of_left_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_joint_le_of_left_residual

/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_joint_le_of_right_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_joint_le_of_right_residual
