import MajorityDynamics.GraphProcess.KernelSplitting.Degrees

/-! Finite support and exact vertex/child/value unions for S2. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.KernelSplitting
open Universal BlockDecomposition FineKernel KernelInputs
variable {V : Type*} [Fintype V] {n : ℕ}

/-- An actual entry of the sampled next array, centered at the actual deterministic child. -/
def EntryBad (σ : FineState.State V n) (p : ℝ) (v : V)
    (t : History (n+1)) (b : Bool) (F : ComponentFiber σ.part σ.deg) : Prop :=
  (p*Fintype.card V)^((4:ℝ)/7) <
    |((sampleNext σ F).deg v (append t b) : ℝ)-p*(child σ t b).card|

/-- The value union uses only the literal supported integer degrees, hence at
most `card V + 1` values. Unsupported targets have the empty event. -/
theorem entry_failure_le (σ : FineState.State V n) (p e : ℝ)
    (he : 0 ≤ e) (v : V) (t : History (n+1)) (b : Bool)
    (hpoint : ∀ a : ℤ, 0 ≤ a → a ≤ σ.deg v t →
      (p*Fintype.card V)^((4:ℝ)/7) < |(a:ℝ)-p*(child σ t b).card| →
      (componentLaw σ).real {F | (sampleNext σ F).deg v (append t b) = a} ≤ e) :
    (componentLaw σ).real {F | EntryBad σ p v t b F} ≤
      ((Fintype.card V : ℝ)+1)*e := by
  let bad : Fin (Fintype.card V+1) → Set (ComponentFiber σ.part σ.deg) := fun a =>
    {F | EntryBad σ p v t b F ∧ (sampleNext σ F).deg v (append t b) = (a.val : ℤ)}
  have hsub : {F | EntryBad σ p v t b F} ⊆ ⋃ a, bad a := by
    intro F hF
    have hnon := next_degree_nonneg σ F v t b
    have hcap := next_degree_le_card σ F v t b
    let a : Fin (Fintype.card V+1) := ⟨((sampleNext σ F).deg v (append t b)).toNat, by omega⟩
    exact Set.mem_iUnion.mpr ⟨a, hF, (Int.toNat_of_nonneg hnon).symm⟩
  have hb (a : Fin (Fintype.card V+1)) : (componentLaw σ).real (bad a) ≤ e := by
    by_cases ha : (a.val : ℤ) ≤ σ.deg v t
    · by_cases hbad : (p*Fintype.card V)^((4:ℝ)/7) <
          |((a.val : ℤ):ℝ)-p*(child σ t b).card|
      · exact (measureReal_mono (fun _ hF => hF.2)).trans
          (hpoint (a.val : ℤ) (by positivity) ha hbad)
      · have hempty : bad a = ∅ := by
          ext F
          simp only [bad, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          intro hF
          apply hbad
          simpa only [EntryBad, hF.2] using hF.1
        rw [hempty, measureReal_empty]
        exact he
    · have hempty : bad a = ∅ := by
        ext F
        simp only [bad, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hF
        exact ha (hF.2 ▸ next_degree_le_parent σ F v t b)
      rw [hempty, measureReal_empty]
      exact he
  calc
    _ ≤ (componentLaw σ).real (⋃ a, bad a) := measureReal_mono hsub
    _ ≤ ∑ a, (componentLaw σ).real (bad a) := measureReal_iUnion_fintype_le bad
    _ ≤ ∑ _a : Fin (Fintype.card V+1), e := Finset.sum_le_sum fun a _ => hb a
    _ = _ := by simp

/-- There are exactly `card V * 2^(n+2)` vertex/child entries. -/
theorem entry_count (V : Type*) [Fintype V] (n : ℕ) :
    Fintype.card (V × History (n+1) × Bool) = Fintype.card V * 2^(n+2) := by
  simp [Fintype.card_prod, pow_succ, mul_assoc]

/-- Actual regularity failure is exhausted by the vertex/child/value union.
The deterministic split is obtained from sampleNext, not supplied as a premise. -/
theorem K_regularity_failure_le (σ : FineState.State V n) (p e : ℝ) (he : 0 ≤ e)
    (hpoint : ∀ (v : V) (t : History (n+1)) (b : Bool) (a : ℤ),
      0 ≤ a → a ≤ σ.deg v t →
      (p*Fintype.card V)^((4:ℝ)/7) < |(a:ℝ)-p*(child σ t b).card| →
      (componentLaw σ).real {F | (sampleNext σ F).deg v (append t b) = a} ≤ e) :
    (K σ).real {τ | ¬ CoarseKernel.Regular p τ.part τ.deg} ≤
      (Fintype.card V : ℝ)*2^(n+2)*(Fintype.card V+1)*e := by
  let I := V × History (n+1) × Bool
  let bad : I → Set (ComponentFiber σ.part σ.deg) :=
    fun i => {F | EntryBad σ p i.1 i.2.1 i.2.2 F}
  have hevent : {F | ¬ CoarseKernel.Regular p (sampleNext σ F).part (sampleNext σ F).deg} =
      ⋃ i : I, bad i := by
    ext F
    simp only [Set.mem_ofPred_eq, CoarseKernel.Regular, not_forall, not_le,
      Set.mem_iUnion, Prod.exists, bad, I]
    constructor
    · rintro ⟨v,u,hu⟩
      refine ⟨v,parent u,last u,?_⟩
      have hc : Local.partSizes (sampleNext σ F).part u =
          (child σ (parent u) (last u)).card := by
        simp only [child, sampleNext_part, RowArray.childSet_stateArray,
          append_parent_last, History.block_card_partSizes]
      simpa only [EntryBad, append_parent_last, hc] using hu
    · rintro ⟨v,t,b,hb⟩
      refine ⟨v,append t b,?_⟩
      have hc : Local.partSizes (sampleNext σ F).part (append t b) =
          (child σ t b).card := by
        simp only [child, sampleNext_part, RowArray.childSet_stateArray,
          History.block_card_partSizes]
      simpa only [EntryBad, hc] using hb
  change ((K σ) {τ | ¬ CoarseKernel.Regular p τ.part τ.deg}).toReal ≤ _
  rw [K_apply]
  change (componentLaw σ).real {F | ¬ CoarseKernel.Regular p (sampleNext σ F).part
    (sampleNext σ F).deg} ≤ _
  rw [hevent]
  calc
    _ ≤ ∑ i : I, (componentLaw σ).real (bad i) := measureReal_iUnion_fintype_le bad
    _ ≤ ∑ _i : I, ((Fintype.card V : ℝ)+1)*e := by
      exact Finset.sum_le_sum fun i _ => entry_failure_le σ p e he i.1 i.2.1 i.2.2
        (hpoint i.1 i.2.1 i.2.2)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, I, entry_count,
        Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring

end MajorityDynamics.GraphProcess.KernelSplitting
