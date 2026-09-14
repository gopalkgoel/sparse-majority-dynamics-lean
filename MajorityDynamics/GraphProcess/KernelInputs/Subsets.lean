import MajorityDynamics.GraphProcess.KernelInputs.Components
import MajorityDynamics.GraphProcess.KernelInputs.Children

noncomputable section
open scoped Classical BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.KernelInputs
open History FineState Local BlockDecomposition
variable {V : Type*} [Fintype V] {n : ℕ}

/-- The literal child subset on the original component's subtype carrier. -/
def childInBlock (σ : State V n) (s : Universal.History (n+1)) (b : Bool) :
    Finset (Block σ.part s) := (child σ s b).subtype (fun v => σ.part v = s)

@[simp] theorem mem_childInBlock (σ : State V n) (s : Universal.History (n+1))
    (b : Bool) (v : Block σ.part s) : v ∈ childInBlock σ s b ↔ v.val ∈ child σ s b :=
  Finset.mem_subtype

theorem childInBlock_map (σ : State V n) (s : Universal.History (n+1)) (b : Bool) :
    (childInBlock σ s b).map (Function.Embedding.subtype _) = child σ s b :=
  Finset.subtype_map_of_mem (fun _v hv => (mem_block _ _ _).mp (child_subset σ s b hv))

@[simp] theorem childInBlock_card (σ : State V n) (s : Universal.History (n+1))
    (b : Bool) : (childInBlock σ s b).card = (child σ s b).card := by
  rw [← childInBlock_map σ s b, Finset.card_map]

/-- Complementation is taken in the actual parent block carrier. -/
theorem childInBlock_complement (σ : State V n) (s : Universal.History (n+1))
    (b : Bool) : Finset.univ \ childInBlock σ s b = childInBlock σ s (!b) := by
  ext v
  have hc := congrArg (fun A : Finset V => v.val ∈ A) (child_complement σ s b)
  simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, mem_childInBlock,
    mem_block, v.property] using (Iff.of_eq hc)

theorem childInBlock_disjoint (σ : State V n) (s : Universal.History (n+1)) :
    Disjoint (childInBlock σ s false) (childInBlock σ s true) := by
  rw [Finset.disjoint_left]
  intro v hv hw
  exact Finset.disjoint_left.mp (child_partition σ s).1
    (mem_childInBlock _ _ _ _ |>.mp hv) (mem_childInBlock _ _ _ _ |>.mp hw)

theorem childInBlock_union (σ : State V n) (s : Universal.History (n+1)) :
    childInBlock σ s false ∪ childInBlock σ s true = Finset.univ := by
  ext v
  have hu := congrArg (fun A : Finset V => v.val ∈ A) (child_partition σ s).2
  simpa only [Finset.mem_union, Finset.mem_univ, mem_childInBlock, mem_block,
    v.property] using (Iff.of_eq hu)

/-- The component-carrier sum is exactly the original L statistic. -/
theorem childInBlock_mass (σ : State V n) (s : Universal.History (n+1)) (b : Bool)
    (t : Universal.History (n+1)) :
    (∑ v ∈ childInBlock σ s b, σ.deg v t) =
      RowArray.childMass (RowArray.stateArray σ) s b t := by
  change _ = ∑ v ∈ child σ s b, RowArray.values (RowArray.stateArray σ) v t
  simp only [RowArray.values_stateArray]
  rw [← childInBlock_map σ s b, Finset.sum_map]
  rfl

theorem childInBlock_mass_real (σ : State V n) (s : Universal.History (n+1)) (b : Bool)
    (t : Universal.History (n+1)) :
    (∑ v ∈ childInBlock σ s b, (σ.deg v t : ℝ)) =
      (RowArray.childMass (RowArray.stateArray σ) s b t : ℝ) := by
  exact_mod_cast childInBlock_mass σ s b t

/-- Natural degrees used by fixed-degree laws give the same real mass. -/
theorem childInBlock_nat_mass_real (σ : State V n) (s : Universal.History (n+1))
    (b : Bool) (t : Universal.History (n+1)) :
    (∑ v ∈ childInBlock σ s b, ((σ.deg v t).toNat : ℝ)) =
      (RowArray.childMass (RowArray.stateArray σ) s b t : ℝ) := by
  simp_rw [degree_cast_real]
  exact childInBlock_mass_real σ s b t

end MajorityDynamics.GraphProcess.KernelInputs
