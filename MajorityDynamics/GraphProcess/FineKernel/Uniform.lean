import MajorityDynamics.Probability.FixedDegreeSampling.Conditioning
import MajorityDynamics.GraphProcess.BlockDecomposition.Main
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators
namespace MajorityDynamics.GraphProcess.FineKernel
open MajorityDynamics.Probability.FixedDegreeSampling

section Uniform
variable {α β : Type*} [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  [MeasurableSpace β] [MeasurableSingletonClass β]

theorem uniform_univ_apply (s : Set α) :
    uniformOn Set.univ s = (Nat.card s : ℝ≥0∞) / Nat.card α := by
  rw [uniform_apply]
  simp only [Set.univ_inter, Set.ncard_univ]
  rfl

theorem map_uniform_equiv (e : α ≃ β) :
    (uniformOn (Set.univ : Set α)).map e = uniformOn (Set.univ : Set β) := by
  ext s _
  rw [Measure.map_apply (measurable_of_countable _) (Set.toFinite s).measurableSet,
    uniform_univ_apply, uniform_univ_apply, Nat.card_congr e]
  congr 2
  exact Nat.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))

theorem map_uniform_subtype (s : Set α) :
    (uniformOn (Set.univ : Set s)).map Subtype.val = uniformOn s := by
  ext t _
  rw [Measure.map_apply (measurable_of_countable _) (Set.toFinite t).measurableSet,
    uniform_univ_apply, uniform_apply]
  congr 2
  exact Nat.card_congr
    { toFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
      invFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩ }

theorem map_uniform_fiber (s : Set β) (e : α ≃ s) :
    (uniformOn (Set.univ : Set α)).map (fun x => (e x).val) = uniformOn s := by
  rw [← Function.comp_def, ← Measure.map_map (measurable_of_countable _)
    (measurable_of_countable _), map_uniform_equiv, map_uniform_subtype]
end Uniform

/-- Uniform on a finite dependent product gives the full joint rectangle product. -/
theorem uniform_pi_rectangle {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, Fintype (X i)] [∀ i, MeasurableSpace (X i)]
    [∀ i, MeasurableSingletonClass (X i)] (s : ∀ i, Set (X i)) :
    uniformOn (Set.univ : Set (∀ i, X i)) {x | ∀ i, x i ∈ s i} =
      ∏ i, uniformOn (Set.univ : Set (X i)) (s i) := by
  rw [uniform_univ_apply]
  have he : {x : (∀ i, X i) // ∀ i, x i ∈ s i} ≃ (∀ i, s i) :=
    { toFun := fun x i => ⟨x.val i, x.property i⟩
      invFun := fun x => ⟨fun i => (x i).val, fun i => (x i).property⟩ }
  have hn : Nat.card ↑({x | ∀ i, x i ∈ s i} : Set (∀ i, X i)) =
      Nat.card (∀ i, s i) := Nat.card_congr he
  rw [hn, Nat.card_pi, Nat.card_pi]
  simp only [Nat.cast_prod, uniform_univ_apply]
  exact (ENNReal.prod_div_distrib_of_ne_top (fun _ _ => ENNReal.natCast_ne_top _)).symm

theorem uniform_prod_rectangle {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β] (s : Set α) (t : Set β) :
    uniformOn (Set.univ : Set (α × β)) (s ×ˢ t) =
      uniformOn Set.univ s * uniformOn Set.univ t := by
  rw [uniform_univ_apply, uniform_univ_apply, uniform_univ_apply]
  have he : (s ×ˢ t) ≃ s × t :=
    { toFun := fun x => (⟨x.val.1, x.property.1⟩, ⟨x.val.2, x.property.2⟩)
      invFun := fun x => ⟨(x.1.val, x.2.val), x.1.property, x.2.property⟩ }
  rw [Nat.card_congr he, Nat.card_prod, Nat.card_prod, Nat.cast_mul, Nat.cast_mul]
  exact ENNReal.mul_div_mul_comm (Or.inr (ENNReal.natCast_ne_top _))
    (Or.inl (ENNReal.natCast_ne_top _))
end MajorityDynamics.GraphProcess.FineKernel
