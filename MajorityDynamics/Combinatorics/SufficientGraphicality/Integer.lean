import MajorityDynamics.Combinatorics.SufficientGraphicality.Natural

/-! Literal nonnegative integer sequences. The maximum includes zero, so it
is zero on an empty sequence and the usual maximum on nonnegative sequences. -/
namespace MajorityDynamics.Combinatorics.SufficientGraphicality
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

def integerMax {n : ℕ} (d : Fin n → ℤ) : ℤ :=
  (insert 0 (univ.image d)).max' (by simp)

def IntegerGraphicalSufficientTheorem : Prop :=
  ∀ (n : ℕ) (d : Fin n → ℤ), (∀ i, 0 ≤ d i) → Even (∑ i, d i) →
    integerMax d * (integerMax d + 1) ≤ ∑ i, d i →
    ∃ G : SimpleGraph (Fin n), ∀ i, (G.degree i : ℤ) = d i

def IntegerBipartiteGraphicalSufficientTheorem : Prop :=
  ∀ (l n : ℕ) (a : Fin l → ℤ) (b : Fin n → ℤ),
    (∀ i, 0 ≤ a i) → (∀ j, 0 ≤ b j) → (∑ i, a i) = ∑ j, b j →
    integerMax a * integerMax b ≤ ∑ i, a i →
    ∃ G : SimpleGraph (Fin l ⊕ Fin n),
      (∀ i j, ¬ G.Adj (.inl i) (.inl j)) ∧
      (∀ i j, ¬ G.Adj (.inr i) (.inr j)) ∧
      (∀ i, (G.degree (.inl i) : ℤ) = a i) ∧
      (∀ j, (G.degree (.inr j) : ℤ) = b j)

@[simp] theorem total_toNat {n : ℕ} (d : Fin n → ℤ) (hd : ∀ i, 0 ≤ d i) :
    (total (fun i => (d i).toNat) : ℤ) = ∑ i, d i := by
  simp [total, hd]

@[simp] theorem maxDegree_toNat {n : ℕ} (d : Fin n → ℤ) (hd : ∀ i, 0 ≤ d i) :
    (maxDegree (fun i => (d i).toNat) : ℤ) = integerMax d := by
  apply le_antisymm
  · have hz : 0 ≤ integerMax d := le_max' _ 0 (by simp)
    have hi : ∀ i, (d i).toNat ≤ (integerMax d).toNat := by
      intro i
      exact Int.toNat_le_toNat (le_max' _ (d i) (by simp))
    have hs : maxDegree (fun i => (d i).toNat) ≤ (integerMax d).toNat :=
      Finset.sup_le fun i _ => hi i
    exact_mod_cast (show (maxDegree (fun i => (d i).toNat) : ℤ) ≤ integerMax d from
      (Int.ofNat_le.mpr hs).trans_eq (Int.toNat_of_nonneg hz))
  · apply max'_le
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · positivity
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hx
      simpa [Int.toNat_of_nonneg (hd i)] using
        (Int.ofNat_le.mpr (le_maxDegree (fun i => (d i).toNat) i))

theorem graphical_integer_of_natural (h : GraphicalSufficientTheorem) :
    IntegerGraphicalSufficientTheorem := by
  intro n d hd heven hbound
  have heven' : Even (total (fun i => (d i).toNat)) := by
    have : Even (total (fun i => (d i).toNat) : ℤ) := by simpa [total_toNat d hd] using heven
    exact_mod_cast this
  have hbound' : maxDegree (fun i => (d i).toNat) *
      (maxDegree (fun i => (d i).toNat) + 1) ≤ total (fun i => (d i).toNat) := by
    have : (maxDegree (fun i => (d i).toNat) : ℤ) *
        ((maxDegree (fun i => (d i).toNat) : ℤ) + 1) ≤
          (total (fun i => (d i).toNat) : ℤ) := by
      simpa only [maxDegree_toNat d hd, total_toNat d hd] using hbound
    exact_mod_cast this
  obtain ⟨G, hG⟩ := h n _ heven' hbound'
  refine ⟨G, fun i => ?_⟩
  rw [hG i, Int.toNat_of_nonneg (hd i)]

theorem bipartite_integer_of_natural (h : BipartiteGraphicalSufficientTheorem) :
    IntegerBipartiteGraphicalSufficientTheorem := by
  intro l n a b ha hb heq hbound
  have heq' : total (fun i => (a i).toNat) = total (fun j => (b j).toNat) := by
    have : (total (fun i => (a i).toNat) : ℤ) = (total (fun j => (b j).toNat) : ℤ) := by
      simpa only [total_toNat a ha, total_toNat b hb] using heq
    exact_mod_cast this
  have hbound' : maxDegree (fun i => (a i).toNat) * maxDegree (fun j => (b j).toNat) ≤
      total (fun i => (a i).toNat) := by
    have : (maxDegree (fun i => (a i).toNat) : ℤ) * (maxDegree (fun j => (b j).toNat) : ℤ) ≤
        (total (fun i => (a i).toNat) : ℤ) := by
      simpa only [maxDegree_toNat a ha, maxDegree_toNat b hb, total_toNat a ha] using hbound
    exact_mod_cast this
  obtain ⟨G, hL, hR, hA, hB⟩ := h l n _ _ heq' hbound'
  refine ⟨G, hL, hR, ?_, ?_⟩
  · intro i
    rw [hA i, Int.toNat_of_nonneg (ha i)]
  · intro j
    rw [hB j, Int.toNat_of_nonneg (hb j)]

end
end MajorityDynamics.Combinatorics.SufficientGraphicality
