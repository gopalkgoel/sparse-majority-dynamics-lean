import MajorityDynamics.Literature.Graphicality.Basic

/-!
# The two authorized external criteria

No proved Erdős–Gallai or Gale–Ryser criterion was found in pinned Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`.

* Erdős–Gallai: P. Erdős and T. Gallai, “Gráfok előírt fokszámú pontokkal”,
  Matematikai Lapok 11 (1960), 264–274. Standard full-range formulation:
  J. W. Miller, “Reduced Criteria for Degree Sequences”, Discrete Mathematics
  313 (2013), 550–562, introduction (preprint p. 1).
* Gale–Ryser: D. Gale, “A theorem on flows in networks”, Pacific J. Math.
  7 (1957), 1073–1082; H. J. Ryser, “Combinatorial properties of matrices
  of zeros and ones”, Canad. J. Math. 9 (1957), 371–377.
  Standard formulation: Miller, §3.1.1 (preprint p. 10), (GR_k).
  https://jwmi.github.io/publications/Degree_Sequences.pdf

Clause mapping: natural-valued functions supply nonnegativity; `Antitone`
supplies decreasing order; `total` supplies the parity/equal-sum clause;
`prefixSet n r hr` consists precisely of indices 0,...,r-1, and its complement
is the tail. The finite range is 1 ≤ r ≤ length. The Gale–Ryser right side
is the standard conjugate-prefix sum, equivalently Σ_j min(r,b_j), by counting
cells in the first r columns of the Ferrers diagram. Only the left side is
sorted. Neither cited full-range criterion has an additional upper-degree
hypothesis. `Graphical` and `Bigraphical` conclude actual simple graphs with
these labeled degrees, not just numerical inequalities. Imports are restricted
to positive lengths; empty cases are constructed in checked proofs.

These are sufficient directions of the external criteria, not the paper's
maximum-degree sufficient conditions. No other external input is introduced.
-/
namespace MajorityDynamics.Combinatorics.SufficientGraphicality
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Sufficient direction of Gale–Ryser, with only the left sequence sorted. -/
def GaleRyserCriterion : Prop :=
  ∀ (l n : ℕ), 0 < l → 0 < n → ∀ (a : Fin l → ℕ) (b : Fin n → ℕ),
    Antitone a → total a = total b →
    (∀ (r : ℕ) (hr : r ≤ l), 1 ≤ r →
      (∑ i ∈ prefixSet l r hr, a i) ≤ ∑ j, min r (b j)) → Bigraphical a b

end
end MajorityDynamics.Combinatorics.SufficientGraphicality
