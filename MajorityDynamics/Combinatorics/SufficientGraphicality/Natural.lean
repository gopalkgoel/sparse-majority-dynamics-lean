import MajorityDynamics.Combinatorics.SufficientGraphicality.Bounds
import MajorityDynamics.Combinatorics.SufficientGraphicality.Relabel

namespace MajorityDynamics.Combinatorics.SufficientGraphicality
open Finset

/-- A.8 with the sole external criterion exposed as an argument. -/
theorem graphical_sufficient_of_erdos_gallai (eg : ErdosGallaiCriterion) :
    GraphicalSufficientTheorem := by
  intro n d heven h
  by_cases hn : n = 0
  · subst n
    exact graphical_zero d (fun i => Fin.elim0 i)
  let e := descendingOrder d
  apply graphical_original_order d e
  apply eg n (by omega) (d ∘ e) (antitone_descendingOrder d)
  · simpa using heven
  · intro r hr _
    have hs : maxDegree (d ∘ e) * (maxDegree (d ∘ e) + 1) ≤ total (d ∘ e) := by
      simpa using h
    simpa using graphical_subset_bound (d ∘ e) hs (prefixSet n r hr)

/-- A.9 with the sole external criterion exposed as an argument. -/
theorem bipartite_graphical_sufficient_of_gale_ryser (gr : GaleRyserCriterion) :
    BipartiteGraphicalSufficientTheorem := by
  intro l n a b heq h
  by_cases hz : total a = 0
  · exact bipartite_zero a b (eq_zero_of_total_zero a hz)
      (eq_zero_of_total_zero b (heq.symm.trans hz))
  have hl : 0 < l := by
    by_contra! hle
    have : l = 0 := by omega
    subst l
    simp [total] at hz
  have hn : 0 < n := by
    by_contra! hle
    have : n = 0 := by omega
    subst n
    have hb0 : total b = 0 := by simp [total]
    exact hz (heq.trans hb0)
  let e := descendingOrder a
  apply bipartite_original_order a b e (Equiv.refl _)
  apply gr l n hl hn (a ∘ e) b (antitone_descendingOrder a)
  · simpa using heq
  · intro r hr _
    have heq' : total (a ∘ e) = total b := by simpa using heq
    have h' : maxDegree (a ∘ e) * maxDegree b ≤ total (a ∘ e) := by simpa using h
    simpa using bipartite_subset_bound (a ∘ e) b heq' h' (prefixSet l r hr)

end MajorityDynamics.Combinatorics.SufficientGraphicality
