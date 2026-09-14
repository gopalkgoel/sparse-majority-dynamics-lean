import MajorityDynamics.Probability.NeighborhoodBulk.SubsetLaws
import Mathlib.MeasureTheory.Measure.Real

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodBulk
open FixedDegreeSampling

theorem uniform_real_congr {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (s E F : Set X) (h : ∀ x ∈ s, x ∈ E ↔ x ∈ F) : (uniformOn s).real E = (uniformOn s).real F := by
  have he : s ∩ E = s ∩ F := by ext x; exact and_congr_right (h x)
  simp only [measureReal_def, uniform_apply, he]

theorem partition_union {V : Type*} (A B R : Finset V) (hR : R ⊆ A ∪ B) :
    (R ∩ A) ∪ (R ∩ B) = R := by
  rw [← Finset.inter_union_distrib_left]
  exact Finset.inter_eq_left.mpr hR

theorem partition_card {V : Type*} (A B R : Finset V) (hAB : Disjoint A B) (hR : R ⊆ A ∪ B) :
    (R ∩ A).card + (R ∩ B).card = R.card := by
  rw [← Finset.card_union_of_disjoint (hAB.mono Finset.inter_subset_right Finset.inter_subset_right),
    partition_union A B R hR]

theorem partition_recover {V : Type*} (A B R₁ R₂ : Finset V) (hAB : Disjoint A B)
    (h₁ : R₁ ⊆ A) (h₂ : R₂ ⊆ B) :
    (R₁ ∪ R₂) ∩ A = R₁ ∧ (R₁ ∪ R₂) ∩ B = R₂ := by
  constructor
  · rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr h₁,
      Finset.disjoint_iff_inter_eq_empty.mp (hAB.symm.mono h₂ le_rfl), Finset.union_empty]
  · rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr h₂,
      Finset.disjoint_iff_inter_eq_empty.mp (hAB.mono h₁ le_rfl), Finset.empty_union]

theorem uniform_partition_sum {X V : Type*} [Fintype X] [Fintype V]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (s : Set X) (N : X → Finset V) (A B : Finset V) (k l : ℕ)
    (hAB : Disjoint A B) (hs : ∀ x ∈ s, N x ⊆ A ∪ B ∧ (N x).card = k + l) :
    (uniformOn s).real {x | (N x ∩ A).card = k} =
      ∑ R₁ ∈ A.powersetCard k, ∑ R₂ ∈ B.powersetCard l,
        (uniformOn s).real {x | N x = R₁ ∪ R₂} := by
  let f : X → Finset V × Finset V := fun x => (N x ∩ A, N x ∩ B)
  let F := (A.powersetCard k ×ˢ B.powersetCard l)
  have he : (uniformOn s).real {x | (N x ∩ A).card = k} =
      (uniformOn s).real (f ⁻¹' (F : Set (Finset V × Finset V))) := by
    apply uniform_real_congr
    intro x hx
    obtain ⟨hsub, hcard⟩ := hs x hx
    have hc := partition_card A B (N x) hAB hsub
    change (N x ∩ A).card = k ↔
      (N x ∩ A, N x ∩ B) ∈ (A.powersetCard k ×ˢ B.powersetCard l)
    rw [Finset.mem_product]
    simp only [Finset.mem_powersetCard]
    constructor
    · intro h
      exact ⟨⟨Finset.inter_subset_right, h⟩, ⟨Finset.inter_subset_right, by omega⟩⟩
    · exact fun h => h.1.2
  rw [he, ← sum_measureReal_preimage_singleton F (fun _ _ => (Set.toFinite _).measurableSet)]
  change (∑ b ∈ (A.powersetCard k ×ˢ B.powersetCard l), _) = _
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro R₁ h₁
  apply Finset.sum_congr rfl
  intro R₂ h₂
  obtain ⟨hsub₁, _⟩ := Finset.mem_powersetCard.mp h₁
  obtain ⟨hsub₂, _⟩ := Finset.mem_powersetCard.mp h₂
  apply uniform_real_congr
  intro x hx
  change (N x ∩ A, N x ∩ B) = (R₁, R₂) ↔ N x = R₁ ∪ R₂
  constructor
  · intro h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    change N x ∩ A = R₁ at h₁
    change N x ∩ B = R₂ at h₂
    simpa only [h₁, h₂] using (partition_union A B (N x) (hs x hx).1).symm
  · intro h
    rw [h]
    obtain ⟨ha, hb⟩ := partition_recover A B R₁ R₂ hAB hsub₁ hsub₂
    rw [ha, hb]

end MajorityDynamics.Probability.NeighborhoodBulk
