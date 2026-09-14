import MajorityDynamics.GraphProcess.GraphicalArray.Main

/-! Regroup the actual independent entries by their ordered source/target blocks. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators Classical ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.BlockPairLaws
open Universal BlockDecomposition
variable {V : Type*} [Fintype V] {n : ℕ}

abbrev Cells (π : V → History (n+1)) :=
  (s t : History (n+1)) → Block π s → ℕ

def naturalCellsEquiv (π : V → History (n+1)) :
    (V → History (n+1) → ℕ) ≃ Cells π where
  toFun a s t v := a v.val t
  invFun a v t := a (π v) t ⟨v,rfl⟩
  left_inv a := rfl
  right_inv a := by
    funext s t v
    rcases v with ⟨v,hv⟩
    cases hv
    rfl

def cells {π : V → History (n+1)} (d : RowArray.Ambient π) : Cells π :=
  naturalCellsEquiv π (RowArray.naturalRows d)

def cellNaturalLaw (π : V → History (n+1)) (q : Local.Tilt n)
    (s t : History (n+1)) : Measure (Block π s → ℕ) :=
  Measure.pi fun _ => binomial (Local.trials (Local.partSizes π) s t)
    (Binomial.closedProbability (q s t))

instance (π : V → History (n+1)) (q : Local.Tilt n) (s t : History (n+1)) :
    IsProbabilityMeasure (cellNaturalLaw π q s t) := by
  unfold cellNaturalLaw
  infer_instance

def cellsLaw (π : V → History (n+1)) (q : Local.Tilt n) : Measure (Cells π) :=
  Measure.pi fun s => Measure.pi fun t => cellNaturalLaw π q s t

instance (π : V → History (n+1)) (q : Local.Tilt n) :
    IsProbabilityMeasure (cellsLaw π q) := by
  unfold cellsLaw
  infer_instance

theorem ordered_fiber_prod {M : Type*} [CommMonoid M]
    (π : V → History (n+1))
    (f : ∀ s _t : History (n+1), Block π s → M) :
    (∏ v, ∏ t, f (π v) t ⟨v,rfl⟩) = ∏ s, ∏ t, ∏ v : Block π s, f s t v := by
  rw [← Fintype.prod_fiberwise π (fun v => ∏ t, f (π v) t ⟨v,rfl⟩)]
  apply Finset.prod_congr rfl
  intro s _
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro t _
  apply Finset.prod_congr rfl
  rintro ⟨v,hv⟩ _
  cases hv
  rfl

set_option maxHeartbeats 400000 in
theorem natural_cells_law (π : V → History (n+1)) (q : Local.Tilt n) :
    (RowArray.naturalLaw π q).map (naturalCellsEquiv π) = cellsLaw π q := by
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have he : naturalCellsEquiv π ⁻¹' {a} = {(naturalCellsEquiv π).symm a} := by
    ext b
    exact (naturalCellsEquiv π).eq_symm_apply.symm
  rw [he]
  simp only [RowArray.naturalLaw, Local.rowLaw, Binomial.law, cellsLaw,
    cellNaturalLaw, Measure.pi_singleton]
  exact ordered_fiber_prod π (fun s t v =>
    binomial (Local.trials (Local.partSizes π) s t)
      (Binomial.closedProbability (q s t)) {a s t v})

theorem cells_law (π : V → History (n+1)) (q : Local.Tilt n) :
    (RowArray.law π q).map (@cells V _ n π) = cellsLaw π q := by
  rw [show (@cells V _ n π) = (naturalCellsEquiv π) ∘ RowArray.naturalRows from rfl,
    ← Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    RowArray.naturalRows_law, natural_cells_law]

/-- Each ordered cell is conditioned on the literal integer degree sum. -/
def cellTotal (π : V → History (n+1))
    (m : History (n+1) → History (n+1) → ℤ) (s t : History (n+1)) :
    Set (Block π s → ℕ) := {a | ∑ v, (a v : ℤ) = m s t}

def cellsTotals (π : V → History (n+1))
    (m : History (n+1) → History (n+1) → ℤ) : Set (Cells π) :=
  Set.univ.pi fun s => Set.univ.pi fun t => cellTotal π m s t

theorem cells_totals (π : V → History (n+1))
    (m : History (n+1) → History (n+1) → ℤ) :
    RowArray.exactTotals π m = cells ⁻¹' cellsTotals π m := by
  ext d
  simp only [RowArray.exactTotals, Set.mem_ofPred_eq, Set.mem_preimage,
    cellsTotals, Set.mem_univ_pi, cellTotal]
  constructor
  · intro h s t
    have hh := congrFun (congrFun h s) t
    change (∑ v ∈ History.block π s, RowArray.values d v t) = m s t at hh
    rw [Finset.sum_subtype (History.block π s) (fun v => History.mem_block π s v)] at hh
    exact hh
  · intro h
    funext s t
    change (∑ v ∈ History.block π s, RowArray.values d v t) = m s t
    rw [Finset.sum_subtype (History.block π s) (fun v => History.mem_block π s v)]
    exact h s t

theorem cells_injective (π : V → History (n+1)) :
    Function.Injective (@cells V _ n π) :=
  (naturalCellsEquiv π).injective.comp (RowArray.naturalRows_injective π)

end MajorityDynamics.GraphProcess.BlockPairLaws
