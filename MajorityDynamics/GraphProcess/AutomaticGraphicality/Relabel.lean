import MajorityDynamics.Combinatorics.SufficientGraphicality.Main
import MajorityDynamics.Probability.FixedDegreeSampling.BipartiteGraph

/-! Transport A.8/A.9 to arbitrary finite vertex labels, with a real degree bound. -/
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable
namespace MajorityDynamics.GraphProcess.AutomaticGraphicality
open MajorityDynamics.Combinatorics.SufficientGraphicality
open MajorityDynamics.Probability.FixedDegreeSampling

private theorem integerMax_nonneg {n : ℕ} (d : Fin n → ℤ) : 0 ≤ integerMax d :=
  Finset.le_max' _ 0 (by simp)

private theorem integerMax_le_real {n : ℕ} (d : Fin n → ℤ) (D : ℝ)
    (hD : 0 ≤ D) (hd : ∀ i, (d i : ℝ) ≤ D) : (integerMax d : ℝ) ≤ D := by
  have hm := Finset.max'_mem (insert 0 (Finset.univ.image d)) (by simp)
  change integerMax d ∈ insert 0 (Finset.univ.image d) at hm
  rcases Finset.mem_insert.mp hm with hz | hm
  · rw [hz]
    simpa using hD
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
    rw [← hi]
    exact hd i

/-- A.8 for the original arbitrary finite vertex labels. -/
theorem graphical_of_bound {A : Type*} [Fintype A] (d : A → ℤ) (D : ℝ)
    (hd0 : ∀ v, 0 ≤ d v) (hD : 0 ≤ D) (hd : ∀ v, (d v : ℝ) ≤ D)
    (heven : Even (∑ v, d v)) (hbound : D * (D + 1) ≤ ((∑ v, d v : ℤ) : ℝ)) :
    ∃ G : SimpleGraph A, ∀ v, (G.degree v : ℤ) = d v := by
  let e : A ≃ Fin (Fintype.card A) := Fintype.equivFin A
  let a : Fin (Fintype.card A) → ℤ := fun i => d (e.symm i)
  have hsum : ∑ i, a i = ∑ v, d v := e.symm.sum_comp d
  have hmax : (integerMax a : ℝ) ≤ D := integerMax_le_real a D hD (fun i => hd _)
  have hmax0 : (0 : ℝ) ≤ integerMax a := by exact_mod_cast integerMax_nonneg a
  have hb : integerMax a * (integerMax a + 1) ≤ ∑ i, a i := by
    have h : (integerMax a : ℝ) * ((integerMax a : ℝ) + 1) ≤
        ((∑ i, a i : ℤ) : ℝ) := by
      calc
        _ ≤ D * (D + 1) := mul_le_mul hmax (by linarith) (by positivity) hD
        _ ≤ _ := by simpa [hsum] using hbound
    exact_mod_cast h
  obtain ⟨G, hG⟩ := graphical_sufficient_integer (Fintype.card A) a
    (fun i => hd0 _) (hsum ▸ heven) hb
  refine ⟨G.comap e, fun v => ?_⟩
  have hi := (SimpleGraph.Iso.comap e G).degree_eq v
  convert (congrArg (fun n : ℕ => (n : ℤ)) hi).symm.trans (hG (e v)) using 1 <;> simp [a]
  all_goals
    rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
    exact Fintype.card_congr (Equiv.refl _)

/-- A.9 transported to the literal cross-edge representation on the original labels. -/
theorem cross_of_bound {A B : Type*} [Fintype A] [Fintype B]
    (a : A → ℤ) (b : B → ℤ) (D : ℝ)
    (ha0 : ∀ v, 0 ≤ a v) (hb0 : ∀ w, 0 ≤ b w) (hD : 0 ≤ D)
    (ha : ∀ v, (a v : ℝ) ≤ D) (hb : ∀ w, (b w : ℝ) ≤ D)
    (hsum : ∑ v, a v = ∑ w, b w)
    (hbound : D ^ 2 ≤ ((∑ v, a v : ℤ) : ℝ)) :
    ∃ E : CrossEdges A B,
      (∀ v, (leftDegree E v : ℤ) = a v) ∧
      (∀ w, (rightDegree E w : ℤ) = b w) := by
  let eA : A ≃ Fin (Fintype.card A) := Fintype.equivFin A
  let eB : B ≃ Fin (Fintype.card B) := Fintype.equivFin B
  let aa : Fin (Fintype.card A) → ℤ := fun i => a (eA.symm i)
  let bb : Fin (Fintype.card B) → ℤ := fun j => b (eB.symm j)
  have hsA : ∑ i, aa i = ∑ v, a v := eA.symm.sum_comp a
  have hsB : ∑ j, bb j = ∑ w, b w := eB.symm.sum_comp b
  have hmaxA : (integerMax aa : ℝ) ≤ D := integerMax_le_real aa D hD (fun i => ha _)
  have hmaxB : (integerMax bb : ℝ) ≤ D := integerMax_le_real bb D hD (fun j => hb _)
  have hzB : (0 : ℝ) ≤ integerMax bb := by exact_mod_cast integerMax_nonneg bb
  have hbound' : integerMax aa * integerMax bb ≤ ∑ i, aa i := by
    have h : (integerMax aa : ℝ) * (integerMax bb : ℝ) ≤ ((∑ i, aa i : ℤ) : ℝ) := by
      calc
        _ ≤ D * D := mul_le_mul hmaxA hmaxB hzB hD
        _ ≤ _ := by simpa [pow_two, hsA] using hbound
    exact_mod_cast h
  obtain ⟨G, hL, hR, hA, hB⟩ := bipartite_graphical_sufficient_integer
    (Fintype.card A) (Fintype.card B) aa bb
    (fun i => ha0 _) (fun j => hb0 _) (hsA.trans (hsum.trans hsB.symm)) hbound'
  let e : A ⊕ B ≃ Fin (Fintype.card A) ⊕ Fin (Fintype.card B) :=
    Equiv.sumCongr eA eB
  let H : SimpleGraph (A ⊕ B) := G.comap e
  have hHL : ∀ v w : A, ¬ H.Adj (.inl v) (.inl w) := by
    intro v w
    exact hL (eA v) (eA w)
  have hHR : ∀ v w : B, ¬ H.Adj (.inr v) (.inr w) := by
    intro v w
    exact hR (eB v) (eB w)
  let E : CrossEdges A B := {x | H.Adj (.inl x.1) (.inr x.2)}
  have hEH : bipartiteGraph E = H := bipartiteGraph_surjective H hHL hHR
  refine ⟨E, ?_, ?_⟩
  · intro v
    rw [← degree_inl, hEH]
    have hi := (SimpleGraph.Iso.comap e G).degree_eq (Sum.inl v)
    change G.degree (.inl (eA v)) = H.degree (.inl v) at hi
    convert (congrArg (fun n : ℕ => (n : ℤ)) hi).symm.trans (hA (eA v)) using 1 <;> simp [aa]
    all_goals
      rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
      exact Fintype.card_congr (Equiv.refl _)
  · intro w
    rw [← degree_inr, hEH]
    have hi := (SimpleGraph.Iso.comap e G).degree_eq (Sum.inr w)
    change G.degree (.inr (eB w)) = H.degree (.inr w) at hi
    convert (congrArg (fun n : ℕ => (n : ℤ)) hi).symm.trans (hB (eB w)) using 1 <;> simp [bb]
    all_goals
      rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
      exact Fintype.card_congr (Equiv.refl _)

end MajorityDynamics.GraphProcess.AutomaticGraphicality
