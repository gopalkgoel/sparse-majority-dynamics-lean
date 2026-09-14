import MajorityDynamics.GraphProcess.KernelEdgeSplitting.Basic

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.KernelEdgeSplitting
open Universal BlockDecomposition FineKernel
open MajorityDynamics.Probability.FixedDegreeSampling
open MajorityDynamics.Probability.FixedDegreeEdgeConcentration
variable {V : Type*} [Fintype V] {n : ℕ}

private theorem uniform_map_fst {α β : Type*} [Fintype α] [Fintype β] [Nonempty β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β] :
    (uniformOn (univ : Set (α × β))).map Prod.fst = uniformOn (univ : Set α) := by
  ext s _
  rw [Measure.map_apply (measurable_of_countable _) (Set.toFinite s).measurableSet]
  rw [← Set.prod_univ, uniform_prod_rectangle]
  simp

private theorem uniform_map_snd {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β] :
    (uniformOn (univ : Set (α × β))).map Prod.snd = uniformOn (univ : Set β) := by
  ext s _
  rw [Measure.map_apply (measurable_of_countable _) (Set.toFinite s).measurableSet]
  rw [← Set.univ_prod, uniform_prod_rectangle]
  simp

private theorem uniform_map_eval {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)] (i : ι) :
    (uniformOn (univ : Set (∀ j, X j))).map (fun x => x i) =
      uniformOn (univ : Set (X i)) := by
  ext s _
  rw [Measure.map_apply (measurable_of_countable _) (Set.toFinite s).measurableSet]
  let A : ∀ j, Set (X j) := fun j => if h : j = i then h ▸ s else univ
  have hA : {x : ∀ j, X j | x i ∈ s} = {x | ∀ j, x j ∈ A j} := by
    ext x
    simp only [mem_ofPred_eq]
    constructor
    · intro hx j
      by_cases h : j = i
      · subst j; simpa [A] using hx
      · simp [A, h]
    · intro hx
      simpa [A] using hx i
  change uniformOn univ {x : ∀ j, X j | x i ∈ s} = _
  rw [hA, uniform_pi_rectangle]
  rw [Finset.prod_eq_single i]
  · simp [A]
  · intro j _ hji
    simp [A, hji]
  · simp

/-- The sampled internal coordinate has precisely the existing fixed-degree law. -/
theorem internalSample_law (σ : FineState.State V n) (s : History (n+1)) :
    (componentLaw σ).map (internalSample σ s) =
      fixedDegreeLaw (fun v : Block σ.part s => (σ.deg v s).toNat) := by
  let : ∀ t, Nonempty (InternalFiber σ.part σ.deg t) := state_internal_nonempty σ
  let : ∀ p : Pair (History (n+1)), Nonempty (CrossFiber σ.part σ.deg p.val.1 p.val.2) :=
    fun p => state_cross_nonempty σ p.val.1 p.val.2
  change (uniformOn univ).map (Subtype.val ∘ (fun F : ∀ t, InternalFiber σ.part σ.deg t => F s) ∘ (Prod.fst : ComponentFiber σ.part σ.deg → _)) = _
  rw [← Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    ← Measure.map_map (measurable_of_countable _)
      (measurable_of_countable _), uniform_map_fst, uniform_map_eval, internal_value_law]

private theorem storedCross_law (σ : FineState.State V n) (p : Pair (History (n+1))) :
    (componentLaw σ).map (fun F => (F.2 p).val) =
      bipartiteFixedDegreeLaw (fun v : Block σ.part p.val.1 => (σ.deg v p.val.2).toNat)
        (fun w : Block σ.part p.val.2 => (σ.deg w p.val.1).toNat) := by
  let : ∀ t, Nonempty (InternalFiber σ.part σ.deg t) := state_internal_nonempty σ
  let : ∀ q : Pair (History (n+1)), Nonempty (CrossFiber σ.part σ.deg q.val.1 q.val.2) :=
    fun q => state_cross_nonempty σ q.val.1 q.val.2
  change (uniformOn univ).map (Subtype.val ∘ (fun F : ∀ q : Pair (History (n+1)), CrossFiber σ.part σ.deg q.val.1 q.val.2 => F p) ∘ (Prod.snd : ComponentFiber σ.part σ.deg → _)) = _
  rw [← Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    ← Measure.map_map (measurable_of_countable _)
      (measurable_of_countable _), uniform_map_snd, uniform_map_eval, cross_value_law]

/-- Exact transposition of the existing bipartite sampling measure. -/
theorem transpose_law {L R : Type*} [Fintype L] [Fintype R]
    (a : L → ℕ) (b : R → ℕ) :
    (bipartiteFixedDegreeLaw a b).map transposeCross = bipartiteFixedDegreeLaw b a := by
  rw [bipartiteFixedDegreeLaw, ← map_uniform_subtype]
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  exact map_uniform_fiber _ (transposeFamily a b)

/-- In increasing orientation, gluing recovers the stored cross coordinate. -/
theorem crossSample_of_lt (σ : FineState.State V n) (s t : History (n+1))
    (hst : s < t) (F : ComponentFiber σ.part σ.deg) :
    crossSample σ s t F = (F.2 ⟨(s,t),hst⟩).val := by
  ext e
  exact glue_cross σ.part (fiberComponents σ.part σ.deg F) ⟨(s,t),hst⟩ e.1 e.2

/-- Reversing labels transposes the same actual cross graph. -/
theorem crossSample_reverse (σ : FineState.State V n) (s t : History (n+1))
    (F : ComponentFiber σ.part σ.deg) :
    crossSample σ s t F = transposeCross (crossSample σ t s F) := by
  ext e
  exact (componentGraph σ F).adj_comm e.1.val e.2.val

/-- Every ordered pair of distinct blocks has its literal bipartite fixed-degree
law. The reversed orientation is transported from the single stored component. -/
theorem crossSample_law (σ : FineState.State V n) (s t : History (n+1)) (hst : s ≠ t) :
    (componentLaw σ).map (crossSample σ s t) =
      bipartiteFixedDegreeLaw (fun v : Block σ.part s => (σ.deg v t).toNat)
        (fun w : Block σ.part t => (σ.deg w s).toNat) := by
  rcases lt_or_gt_of_ne hst with h | h
  · simpa only [funext (crossSample_of_lt σ s t h)] using storedCross_law σ ⟨(s,t),h⟩
  · have hf : crossSample σ s t = transposeCross ∘ (fun F => (F.2 ⟨(t,s),h⟩).val) := by
      funext F
      rw [crossSample_reverse, crossSample_of_lt σ t s h]
      rfl
    rw [hf, ← Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
      storedCross_law, transpose_law]

/-- Transport any actual internal graph event, including concentration events. -/
theorem internalSample_real (σ : FineState.State V n) (s : History (n+1))
    (A : Set (SimpleGraph (Block σ.part s))) :
    (componentLaw σ).real {F | internalSample σ s F ∈ A} =
      (fixedDegreeLaw (fun v : Block σ.part s => (σ.deg v s).toNat)).real A := by
  have h := congrArg (fun μ : Measure (SimpleGraph (Block σ.part s)) => μ A)
    (internalSample_law σ s)
  rw [Measure.map_apply (measurable_of_countable _) (Set.toFinite A).measurableSet] at h
  exact congrArg ENNReal.toReal h

/-- Transport any actual cross-edge event in either orientation. -/
theorem crossSample_real (σ : FineState.State V n) (s t : History (n+1)) (hst : s ≠ t)
    (A : Set (CrossEdges (Block σ.part s) (Block σ.part t))) :
    (componentLaw σ).real {F | crossSample σ s t F ∈ A} =
      (bipartiteFixedDegreeLaw (fun v : Block σ.part s => (σ.deg v t).toNat)
        (fun w : Block σ.part t => (σ.deg w s).toNat)).real A := by
  have h := congrArg (fun μ : Measure (CrossEdges (Block σ.part s) (Block σ.part t)) => μ A)
    (crossSample_law σ s t hst)
  rw [Measure.map_apply (measurable_of_countable _) (Set.toFinite A).measurableSet] at h
  exact congrArg ENNReal.toReal h

end MajorityDynamics.GraphProcess.KernelEdgeSplitting
