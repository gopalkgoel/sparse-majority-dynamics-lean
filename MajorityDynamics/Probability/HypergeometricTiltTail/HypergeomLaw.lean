import MajorityDynamics.Probability.HypergeometricTiltTail.Hypergeom

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace MajorityDynamics.Probability.HypergeometricTiltTail

/-- Exact counting identity for the intersection of a uniform fixed-size subset
with an arbitrary literal subset of an arbitrary finite population. -/
theorem intersection_fiber_card_on {V : Type*} [DecidableEq V]
    (P S : Finset V) (hSP : S ⊆ P) {d t : ℕ} (htd : t ≤ d) :
    ((P.powersetCard d).filter
      (fun R => (R ∩ S).card = t)).card =
      S.card.choose t * (P.card - S.card).choose (d-t) := by
  classical
  let A := (P.powersetCard d).filter
      (fun R => (R ∩ S).card = t)
  let B := S.powersetCard t ×ˢ (P \ S).powersetCard (d-t)
  have hcard : A.card = B.card := by
    apply Finset.card_bij (fun R _ => (R ∩ S, R \ S))
    · intro R hR
      obtain ⟨hRd,hRt⟩ := Finset.mem_filter.mp hR
      obtain ⟨hRP,hRd⟩ := Finset.mem_powersetCard.mp hRd
      apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hRt⟩
      · apply Finset.mem_powersetCard.mpr
        constructor
        · intro x hx
          exact Finset.mem_sdiff.mpr ⟨hRP (Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2⟩
        · rw [Finset.card_sdiff, Finset.inter_comm, hRt, hRd]
    · intro R hR Q hQ heq
      have hi := congrArg Prod.fst heq
      have hs := congrArg Prod.snd heq
      ext x
      have hi' : (x ∈ R ∧ x ∈ S) ↔ (x ∈ Q ∧ x ∈ S) := by
        simpa only [Finset.mem_inter] using (congrArg (fun Z => x ∈ Z) hi).to_iff
      have hs' : (x ∈ R ∧ x ∉ S) ↔ (x ∈ Q ∧ x ∉ S) := by
        simpa only [Finset.mem_sdiff] using (congrArg (fun Z => x ∈ Z) hs).to_iff
      by_cases hx : x ∈ S <;> tauto
    · intro Q hQ
      obtain ⟨hQ1,hQ2⟩ := Finset.mem_product.mp hQ
      obtain ⟨hQ1S,hQ1c⟩ := Finset.mem_powersetCard.mp hQ1
      obtain ⟨hQ2S,hQ2c⟩ := Finset.mem_powersetCard.mp hQ2
      have hdis : Disjoint Q.1 Q.2 := by
        apply Finset.disjoint_left.mpr
        intro x hx1 hx2
        exact (Finset.mem_sdiff.mp (hQ2S hx2)).2 (hQ1S hx1)
      have hinter : (Q.1 ∪ Q.2) ∩ S = Q.1 := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hx|hx,hxS⟩
          · exact hx
          · exact False.elim ((Finset.mem_sdiff.mp (hQ2S hx)).2 hxS)
        · intro hx; exact ⟨Or.inl hx, hQ1S hx⟩
      have hdiff : (Q.1 ∪ Q.2) \ S = Q.2 := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hx|hx,hxS⟩
          · exact False.elim (hxS (hQ1S hx))
          · exact hx
        · intro hx; exact ⟨Or.inr hx, (Finset.mem_sdiff.mp (hQ2S hx)).2⟩
      refine ⟨Q.1 ∪ Q.2, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_powersetCard.mpr
          refine ⟨?_, ?_⟩
          · exact Finset.union_subset (hQ1S.trans hSP) (hQ2S.trans Finset.sdiff_subset)
          rw [Finset.card_union_of_disjoint hdis,hQ1c,hQ2c]
          omega
        · rw [hinter,hQ1c]
      · exact Prod.ext hinter hdiff
  simpa [A,B,Finset.card_product,Finset.card_powersetCard,
    Finset.card_sdiff_of_subset hSP] using hcard

/-- Literal normalized counting probability on an arbitrary finite population. -/
theorem hypergeomMass_eq_uniform_average_on {V : Type*} [DecidableEq V]
    (P S : Finset V) (hSP : S ⊆ P) {d t : ℕ} (htd : t ≤ d) :
    hypergeomMass P.card S.card d t =
      (P.card.choose d : ℝ)⁻¹ *
        ∑ R ∈ P.powersetCard d,
          (if (R ∩ S).card = t then (1 : ℝ) else 0) := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [intersection_fiber_card_on P S hSP htd, Nat.cast_mul]
  unfold hypergeomMass
  ring

/-- Full-population version of the exact counting identity. -/
theorem intersection_fiber_card {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) {d t : ℕ} (htd : t ≤ d) :
    (((Finset.univ : Finset V).powersetCard d).filter
      (fun R => (R ∩ S).card = t)).card =
      S.card.choose t * (Fintype.card V - S.card).choose (d-t) := by
  simpa using intersection_fiber_card_on Finset.univ S (Finset.subset_univ _) htd

/-- Literal normalized counting probability equals the hypergeometric atom. -/
theorem hypergeomMass_eq_uniform_average {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) {d t : ℕ} (htd : t ≤ d) :
    hypergeomMass (Fintype.card V) S.card d t =
      ((Fintype.card V).choose d : ℝ)⁻¹ *
        ∑ R ∈ (Finset.univ : Finset V).powersetCard d,
          (if (R ∩ S).card = t then (1 : ℝ) else 0) := by
  simpa using hypergeomMass_eq_uniform_average_on Finset.univ S (Finset.subset_univ _) htd

end MajorityDynamics.Probability.HypergeometricTiltTail
