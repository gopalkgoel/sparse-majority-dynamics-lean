import MajorityDynamics.GraphProcess.BlockPairLaws.PairLaw
import MajorityDynamics.GraphProcess.BlockPairLaws.Tilt

/-! The paper's actual reference-binomial degree-sequence laws. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators Classical ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.BlockPairLaws
open Universal BlockDecomposition
variable {V : Type*} [Fintype V] {n : ℕ}

def internalBinomialLaw (π : V → History (n+1))
    (m : History (n+1) → History (n+1) → ℤ) (s : History (n+1)) :
    Measure (Block π s → ℕ) := cellCondition π m (halfTilt n) s s

def crossBinomialLaw (π : V → History (n+1))
    (m : History (n+1) → History (n+1) → ℤ) (p : Pair (History (n+1))) :
    Measure ((Block π p.val.1 → ℕ) × (Block π p.val.2 → ℕ)) :=
  (cellCondition π m (halfTilt n) p.val.1 p.val.2).prod
    (cellCondition π m (halfTilt n) p.val.2 p.val.1)

theorem internalBinomialLaw_probability (y : Local.CoarseData V n) (s : History (n+1)) :
    IsProbabilityMeasure (internalBinomialLaw y.part y.edge s) :=
  cellCondition_probability y (halfTilt n) s s

theorem crossBinomialLaw_probability (y : Local.CoarseData V n) (p : Pair (History (n+1))) :
    IsProbabilityMeasure (crossBinomialLaw y.part y.edge p) := by
  have := cellCondition_probability y (halfTilt n) p.val.1 p.val.2
  have := cellCondition_probability y (halfTilt n) p.val.2 p.val.1
  unfold crossBinomialLaw
  infer_instance

/-- Literal A.1 internal comparison: Binomial(n[s]-1,1/2) entries, sum m[s,s]. -/
theorem internalBinomialLaw_eq (π : V → History (n+1))
    (m : History (n+1) → History (n+1) → ℤ) (s : History (n+1)) :
    internalBinomialLaw π m s =
      cond (Measure.pi fun _ : Block π s =>
        binomial (Local.partSizes π s - 1) (Binomial.closedProbability halfProbability))
        {a | ∑ v, (a v : ℤ) = m s s} := by
  simp only [internalBinomialLaw, cellCondition, cellNaturalLaw, Local.trials_self,
    halfTilt, cellTotal]

/-- Literal A.1 bipartite comparison: independently conditioned left/right binomials,
with the same m[s,t] on both sides, even if the original tilt was asymmetric. -/
theorem crossBinomialLaw_eq (y : Local.CoarseData V n) (p : Pair (History (n+1))) :
    crossBinomialLaw y.part y.edge p =
      (cond (Measure.pi fun _ : Block y.part p.val.1 =>
        binomial (Local.partSizes y.part p.val.2) (Binomial.closedProbability halfProbability))
        {a | ∑ v, (a v : ℤ) = y.edge p.val.1 p.val.2}).prod
      (cond (Measure.pi fun _ : Block y.part p.val.2 =>
        binomial (Local.partSizes y.part p.val.1) (Binomial.closedProbability halfProbability))
        {a | ∑ v, (a v : ℤ) = y.edge p.val.1 p.val.2}) := by
  simp only [crossBinomialLaw, cellCondition, cellNaturalLaw, halfTilt, cellTotal,
    Local.trials_other _ (ne_of_lt p.property), Local.trials_other _ (ne_of_gt p.property),
    y.edge_symm p.val.2 p.val.1]

theorem cellNaturalLaw_support (π : V → History (n+1)) (q : Local.Tilt n)
    (s t : History (n+1)) :
    ∀ᵐ a ∂cellNaturalLaw π q s t,
      ∀ v, a v ≤ Local.trials (Local.partSizes π) s t := by
  exact Binomial.law_ae_box (fun _ : Block π s => Local.trials (Local.partSizes π) s t)
    (fun _ => q s t)

theorem cellCondition_support (y : Local.CoarseData V n) (q : Local.Tilt n)
    (s t : History (n+1)) :
    ∀ᵐ a ∂cellCondition y.part y.edge q s t,
      (∀ v, a v ≤ Local.trials (Local.partSizes y.part) s t) ∧
        ∑ v, (a v : ℤ) = y.edge s t := by
  have h₁ : ∀ᵐ a ∂cellCondition y.part y.edge q s t,
      ∀ v, a v ≤ Local.trials (Local.partSizes y.part) s t :=
    cond_absolutelyContinuous.ae_le (cellNaturalLaw_support y.part q s t)
  have h₂ : ∀ᵐ a ∂cellCondition y.part y.edge q s t,
      a ∈ cellTotal y.part y.edge s t := by
    exact ae_cond_mem (Set.to_countable _).measurableSet
  filter_upwards [h₁,h₂] with a ha hb
  exact ⟨ha,hb⟩

/-- The two directed vectors remain independent after both sum constraints. -/
theorem cross_binomial_rectangle (y : Local.CoarseData V n)
    (p : Pair (History (n+1)))
    (A : Set (Block y.part p.val.1 → ℕ)) (B : Set (Block y.part p.val.2 → ℕ)) :
    crossBinomialLaw y.part y.edge p (A ×ˢ B) =
      cellCondition y.part y.edge (halfTilt n) p.val.1 p.val.2 A *
      cellCondition y.part y.edge (halfTilt n) p.val.2 p.val.1 B := by
  have := cellCondition_probability y (halfTilt n) p.val.1 p.val.2
  have := cellCondition_probability y (halfTilt n) p.val.2 p.val.1
  exact Measure.prod_prod A B

/-- Full joint component law, in the reference success probability 1/2. -/
theorem binomial_components (y : Local.CoarseData V n) (q : Local.Tilt n) :
    (cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge)).map
      (degreeComponents y.part) =
      (Measure.pi fun s => internalBinomialLaw y.part y.edge s).prod
        (Measure.pi fun p => crossBinomialLaw y.part y.edge p) := by
  rw [tilt_half]
  exact conditioned_components y (halfTilt n)

theorem binomial_rectangle (y : Local.CoarseData V n) (q : Local.Tilt n)
    (A : ∀ s : History (n+1), Set (Block y.part s → ℕ))
    (B : ∀ p : Pair (History (n+1)),
      Set ((Block y.part p.val.1 → ℕ) × (Block y.part p.val.2 → ℕ))) :
    cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge)
      {d | (∀ s, internalVector y.part d s ∈ A s) ∧
        ∀ p, crossVector y.part d p ∈ B p} =
      (∏ s, internalBinomialLaw y.part y.edge s (A s)) *
        ∏ p, crossBinomialLaw y.part y.edge p (B p) := by
  rw [tilt_half]
  exact pair_rectangle y (halfTilt n) A B

/-- Second identity of eq:enum-factor, including all nongraphical bounded arrays. -/
theorem binomial_atom (y : Local.CoarseData V n) (q : Local.Tilt n)
    (d : RowArray.Ambient y.part) :
    cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge) {d} =
      (∏ s, internalBinomialLaw y.part y.edge s {internalVector y.part d s}) *
        ∏ p, crossBinomialLaw y.part y.edge p {crossVector y.part d p} := by
  have he : {a : RowArray.Ambient y.part |
      (∀ s, internalVector y.part a s ∈ ({internalVector y.part d s} : Set _)) ∧
      ∀ p, crossVector y.part a p ∈ ({crossVector y.part d p} : Set _)} = {d} := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hi,hc⟩
      exact vectors_injective y.part a d hi hc
    · rintro rfl
      exact ⟨fun _ => rfl, fun _ => rfl⟩
  simpa only [he] using binomial_rectangle y q
    (fun s => {internalVector y.part d s}) (fun p => {crossVector y.part d p})

theorem binomial_atom_pos (y : Local.CoarseData V n) (q : Local.Tilt n)
    (d : RowArray.Ambient y.part) (hd : RowArray.totals d = y.edge) :
    0 < cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge) {d} := by
  rw [cond_apply (Set.toFinite _).measurableSet,
    Set.inter_singleton_of_mem (show d ∈ RowArray.exactTotals y.part y.edge from hd)]
  exact pos_iff_ne_zero.mpr (mul_ne_zero
    (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) (law_singleton_pos y.part q d).ne')

end MajorityDynamics.GraphProcess.BlockPairLaws
