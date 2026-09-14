import MajorityDynamics.GraphProcess.BlockPairLaws.CellConditioning
import MajorityDynamics.GraphProcess.BlockPairLaws.PairProduct
import MajorityDynamics.GraphProcess.BlockPairLaws.Graphical

/-! Group independent ordered cells into internal blocks and unordered cross pairs. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators Classical ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.BlockPairLaws
open Universal BlockDecomposition
variable {V : Type*} [Fintype V] {n : ℕ}

abbrev DegreeComponents (π : V → History (n+1)) :=
  ((s : History (n+1)) → Block π s → ℕ) ×
  ((p : Pair (History (n+1))) → (Block π p.val.1 → ℕ) × (Block π p.val.2 → ℕ))

def packCells (π : V → History (n+1)) (a : Cells π) : DegreeComponents π :=
  (fun s => a s s, fun p => (a p.val.1 p.val.2, a p.val.2 p.val.1))

def unpackCells (π : V → History (n+1)) (a : DegreeComponents π) : Cells π :=
  fun s t => if h : s = t then a.1 s else
    if h' : s < t then (a.2 ⟨(s,t),h'⟩).1
    else (a.2 ⟨(t,s), lt_of_le_of_ne (le_of_not_gt h') (Ne.symm h)⟩).2

omit [Fintype V] in
theorem unpack_pack (π : V → History (n+1)) (a : Cells π) :
    unpackCells π (packCells π a) = a := by
  funext s t v
  by_cases h : s = t
  · subst t
    simp [unpackCells, packCells]
  · by_cases h' : s < t <;> simp [unpackCells, packCells, h, h']

omit [Fintype V] in
theorem pack_unpack (π : V → History (n+1)) (a : DegreeComponents π) :
    packCells π (unpackCells π a) = a := by
  apply Prod.ext
  · funext s v
    simp [packCells, unpackCells]
  · funext p
    apply Prod.ext
    · funext v
      simp [packCells, unpackCells, ne_of_lt p.property, p.property]
    · funext v
      simp [packCells, unpackCells, ne_of_gt p.property, not_lt_of_gt p.property]

def packEquiv (π : V → History (n+1)) : Cells π ≃ DegreeComponents π where
  toFun := packCells π
  invFun := unpackCells π
  left_inv := unpack_pack π
  right_inv := pack_unpack π

/-- Product law for every diagonal and single-orientation cross component. -/
def pairLaw (π : V → History (n+1))
    (m : History (n+1) → History (n+1) → ℤ) (q : Local.Tilt n) :
    Measure (DegreeComponents π) :=
  (Measure.pi fun s => cellCondition π m q s s).prod
    (Measure.pi fun p : Pair (History (n+1)) =>
      (cellCondition π m q p.val.1 p.val.2).prod (cellCondition π m q p.val.2 p.val.1))

theorem prod_measure_singleton {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν] (a : α × β) :
    μ.prod ν {a} = μ {a.1} * ν {a.2} := by
  have he : ({a} : Set (α × β)) = {a.1} ×ˢ {a.2} := by
    rw [Set.singleton_prod_singleton]
  rw [he, Measure.prod_prod]

theorem pack_pi (y : Local.CoarseData V n) (q : Local.Tilt n) :
    (Measure.pi (fun s => Measure.pi fun t => cellCondition y.part y.edge q s t)).map
      (packCells y.part) = pairLaw y.part y.edge q := by
  have (s t : History (n+1)) := cellCondition_probability y q s t
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have he : packCells y.part ⁻¹' {a} = {unpackCells y.part a} := by
    ext b
    exact (packEquiv y.part).eq_symm_apply.symm
  rw [he]
  simp only [Measure.pi_singleton, pairLaw, prod_measure_singleton]
  rw [prod_block_pairs]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro s _
    simp [unpackCells]
  · apply Finset.prod_congr rfl
    intro p _
    congr 1
    · simp [unpackCells, ne_of_lt p.property, p.property]
    · simp [unpackCells, ne_of_gt p.property, not_lt_of_gt p.property]

def degreeComponents (π : V → History (n+1)) (d : RowArray.Ambient π) :
    DegreeComponents π :=
  (fun s => internalVector π d s, fun p => crossVector π d p)

theorem degreeComponents_eq (π : V → History (n+1)) :
    degreeComponents π = packCells π ∘ (@cells V _ n π) := rfl

theorem conditioned_components (y : Local.CoarseData V n) (q : Local.Tilt n) :
    (cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge)).map
      (degreeComponents y.part) = pairLaw y.part y.edge q := by
  rw [degreeComponents_eq, ← Measure.map_map (measurable_of_countable _)
    (measurable_of_countable _), cells_conditioned, pack_pi]

theorem pair_rectangle (y : Local.CoarseData V n) (q : Local.Tilt n)
    (A : ∀ s : History (n+1), Set (Block y.part s → ℕ))
    (B : ∀ p : Pair (History (n+1)),
      Set ((Block y.part p.val.1 → ℕ) × (Block y.part p.val.2 → ℕ))) :
    cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge)
      {d | (∀ s, internalVector y.part d s ∈ A s) ∧
        ∀ p, crossVector y.part d p ∈ B p} =
      (∏ s, cellCondition y.part y.edge q s s (A s)) *
      ∏ p : Pair (History (n+1)),
        ((cellCondition y.part y.edge q p.val.1 p.val.2).prod
          (cellCondition y.part y.edge q p.val.2 p.val.1)) (B p) := by
  have (s t : History (n+1)) := cellCondition_probability y q s t
  have h := congrArg (fun μ : Measure (DegreeComponents y.part) =>
    μ ((Set.univ.pi A) ×ˢ (Set.univ.pi B))) (conditioned_components y q)
  rw [Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet] at h
  simpa only [pairLaw, Measure.prod_prod, Measure.pi_pi, Set.preimage,
    Set.mem_prod, Set.mem_univ_pi, degreeComponents] using h

end MajorityDynamics.GraphProcess.BlockPairLaws
