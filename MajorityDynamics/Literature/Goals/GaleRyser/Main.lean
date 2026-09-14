import MajorityDynamics.Literature.Goals.GaleRyser.Statement
import MajorityDynamics.Literature.Graphicality.GaleRyserHall

/-! L04 — Gale–Ryser criterion, proved using finite Hall matching.

The statement is the classical sufficiency criterion of Gale (1957) and Ryser
(1957), in the sorted-left formulation (GR_k) of J. W. Miller, *Reduced Criteria
for Degree Sequences* (2013), §3.1.1, preprint p. 10:
https://jwmi.github.io/publications/Degree_Sequences.pdf .

The proof is a new Lean implementation: row-degree tokens and complementary
column-degree tokens are matched bijectively to the cells of a zero-one matrix.
Mathlib's proved finite Hall theorem supplies the matching; the cells occupied
by row tokens give the required labeled bipartite simple graph. -/
namespace MajorityDynamics.Combinatorics.SufficientGraphicality
open Finset

/-- The full Gale–Ryser sufficiency criterion, with arbitrary column ordering. -/
theorem gale_ryser : GaleRyserCriterion := by
  classical
  intro l n _ _ a b ha ht hp
  change (∑ i, a i) = ∑ j, b j at ht
  have hcap (A : Finset (Fin l)) : ∑ i ∈ A, a i ≤ ∑ j, min A.card (b j) := by
    by_cases hA : A.card = 0
    · have : A = ∅ := card_eq_zero.mp hA
      simp [this]
    · exact (sum_le_sorted_prefix a ha A).trans
        (hp A.card (by simpa using card_le_univ A) (by omega))
  have hfull : ∑ j, b j ≤ ∑ j, min l (b j) := by
    have h := hcap univ
    simpa only [card_univ, Fintype.card_fin, ht] using h
  have heq : (∑ j, min l (b j)) = ∑ j, b j :=
    le_antisymm (sum_le_sum fun j _ => min_le_right _ _) hfull
  have hb (j : Fin n) : b j ≤ l := by
    have h := (sum_eq_sum_iff_of_le (fun j (_ : j ∈ (univ : Finset (Fin n))) =>
      min_le_right l (b j))).mp heq j (mem_univ j)
    omega
  obtain ⟨e,he⟩ := gale_matching a b hb ht hcap
  exact gale_matching_bigraphical a b hb e he

end MajorityDynamics.Combinatorics.SufficientGraphicality
