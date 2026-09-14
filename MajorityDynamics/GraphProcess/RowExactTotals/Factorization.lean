import MajorityDynamics.GraphProcess.RowArray.Statistics
import MajorityDynamics.Probability.ConditionedBinomialFourier.Characteristic

/-! Exact regrouping of the actual history-conditioned array law into iid block copies. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators Classical ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.RowExactTotals
open Universal
open MajorityDynamics.Probability.ConditionedBinomialFourier
variable {V : Type*} [Fintype V] {n : ℕ}

/-- Enumerate every actual history fiber, including empty fibers. -/
def blockEnumeration (π : V → History (n+1)) (s : History (n+1)) :
    {v : V // π v = s} ≃ Fin (Local.partSizes π s) :=
  Fintype.equivFinOfCardEq (by simp [Local.partSizes, Fintype.card_subtype])

abbrev BlockCopies (π : V → History (n+1)) :=
  (s : History (n+1)) → Fin (Local.partSizes π s) → History (n+1) → ℕ

def fiberRowsEquiv (π : V → History (n+1)) :
    (V → History (n+1) → ℕ) ≃ ((s : History (n+1)) → {v : V // π v = s} → History (n+1) → ℕ) where
  toFun a _ v := a v.val
  invFun a v := a (π v) ⟨v,rfl⟩
  left_inv a := rfl
  right_inv a := by
    funext s v
    rcases v with ⟨v,hv⟩
    cases hv
    rfl

/-- This equivalence only permutes actual vertices; it does not replace their rows. -/
def blockCopiesEquiv (π : V → History (n+1)) :
    (V → History (n+1) → ℕ) ≃ BlockCopies π :=
  (fiberRowsEquiv π).trans (Equiv.piCongrRight fun s =>
    Equiv.piCongrLeft (fun _ : Fin (Local.partSizes π s) => History (n+1) → ℕ)
      (blockEnumeration π s))

def blockCopies {π : V → History (n+1)} (d : RowArray.Ambient π) : BlockCopies π :=
  blockCopiesEquiv π (RowArray.naturalRows d)

/-- The literal ordered integer target of a block of natural rows. -/
def blockTarget (m : ℕ) (z : History (n+1) → ℤ) :
    Set (Fin m → History (n+1) → ℕ) :=
  {x | ∀ t, (∑ j, (x j t : ℤ)) = z t}

theorem fiber_prod {M : Type*} [CommMonoid M] (π : V → History (n+1))
    (f : ∀ s, Fin (Local.partSizes π s) → M) :
    (∏ v, f (π v) (blockEnumeration π (π v) ⟨v,rfl⟩)) = ∏ s, ∏ j, f s j := by
  rw [← Fintype.prod_fiberwise π
    (fun v => f (π v) (blockEnumeration π (π v) ⟨v,rfl⟩))]
  apply Finset.prod_congr rfl
  intro s _
  rw [← (blockEnumeration π s).prod_comp (f s)]
  apply Finset.prod_congr rfl
  rintro ⟨v,hv⟩ _
  cases hv
  rfl

/-- Full joint iid-copy law, derived from the already proved actual row pushforward. -/
theorem conditioned_blockCopies (π : V → History (n+1)) (q : Local.Tilt n)
    (h : ∀ s, 0 < Local.rowLaw (Local.partSizes π) q s (RowArray.rowHistory s)) :
    (cond (RowArray.law π q) (RowArray.history π)).map blockCopies =
      Measure.pi (fun s => copyLaw (Local.rowCondition (Local.partSizes π) q s)
        (Local.partSizes π s)) := by
  have (s : History (n+1)) : IsProbabilityMeasure
      (Local.rowCondition (Local.partSizes π) q s) := by
    rw [RowArray.rowCondition_eq_cond]
    exact cond_isProbabilityMeasure (h s).ne'
  rw [show (@blockCopies V _ n π) = (blockCopiesEquiv π) ∘ RowArray.naturalRows from rfl,
    ← Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    RowArray.conditioned_rows π q h]
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have he : blockCopiesEquiv π ⁻¹' {a} = {(blockCopiesEquiv π).symm a} := by
    ext b
    exact (blockCopiesEquiv π).eq_symm_apply.symm
  rw [he]
  simp only [copyLaw, Measure.pi_singleton]
  exact fiber_prod π (fun s j => Local.rowCondition (Local.partSizes π) q s {a s j})

theorem blockCopies_sum (π : V → History (n+1)) (d : RowArray.Ambient π)
    (s t : History (n+1)) :
    (∑ j, (blockCopies d s j t : ℤ)) = RowArray.totals d s t := by
  simp only [blockCopies, blockCopiesEquiv, Equiv.trans_apply, Equiv.piCongrRight_apply,
    Pi.map_apply, Equiv.piCongrLeft_apply, eq_rec_constant, fiberRowsEquiv, Equiv.coe_fn_mk]
  change (∑ j, ((RowArray.naturalRows d) ((blockEnumeration π s).symm j).val t : ℤ)) =
    ∑ v ∈ History.block π s, RowArray.values d v t
  rw [Finset.sum_subtype (History.block π s) (fun v => History.mem_block π s v)]
  exact (blockEnumeration π s).symm.sum_comp
    (fun v : {v : V // π v = s} => RowArray.values d v.val t)

/-- The exact event has every ordered coordinate, including doubled diagonal counts. -/
theorem exactTotals_blockCopies (π : V → History (n+1))
    (m : History (n+1) → History (n+1) → ℤ) :
    RowArray.exactTotals π m = blockCopies ⁻¹'
      (Set.univ.pi fun s => blockTarget (Local.partSizes π s) (m s)) := by
  ext d
  simp only [RowArray.exactTotals, Set.mem_ofPred_eq, Set.mem_preimage,
    Set.mem_univ_pi, blockTarget]
  simp_rw [blockCopies_sum]
  exact ⟨fun h s t => congrFun (congrFun h s) t, fun h => funext fun s => funext (h s)⟩

theorem exactTotals_factorization (π : V → History (n+1)) (q : Local.Tilt n)
    (h : ∀ s, 0 < Local.rowLaw (Local.partSizes π) q s (RowArray.rowHistory s))
    (m : History (n+1) → History (n+1) → ℤ) :
    cond (RowArray.law π q) (RowArray.history π) (RowArray.exactTotals π m) =
      ∏ s, copyLaw (Local.rowCondition (Local.partSizes π) q s)
        (Local.partSizes π s) {x | ∀ t, (∑ j, (x j t : ℤ)) = m s t} := by
  have (s : History (n+1)) : IsProbabilityMeasure
      (Local.rowCondition (Local.partSizes π) q s) := by
    rw [RowArray.rowCondition_eq_cond]
    exact cond_isProbabilityMeasure (h s).ne'
  rw [exactTotals_blockCopies, ← Measure.map_apply (measurable_of_countable _)
    (Set.to_countable _).measurableSet, conditioned_blockCopies π q h, Measure.pi_pi]
  rfl

theorem exactTotals_real_factorization (y : Local.CoarseData V n) (q : Local.Tilt n)
    (h : ∀ s, 0 < Local.rowLaw y.sizes q s (RowArray.rowHistory s)) :
    (cond (RowArray.law y.part q) (RowArray.history y.part)).real
      (RowArray.exactTotals y.part y.edge) =
      ∏ s, (copyLaw (Local.rowCondition y.sizes q s) (y.sizes s)).real
        {x | ∀ t, (∑ j, (x j t : ℤ)) = y.edge s t} := by
  simp only [Measure.real, exactTotals_factorization y.part q h, ENNReal.toReal_prod]
  rfl

end MajorityDynamics.GraphProcess.RowExactTotals
