import MajorityDynamics.GraphProcess.BlockDecomposition.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Classical

namespace MajorityDynamics.GraphProcess.BlockCountProbability
open Universal

/-- Exactly one factor per internal block and per strict unordered pair. -/
def factorCount (n : ℕ) : ℕ := 2^(n+1) + (2^(n+1)).choose 2

theorem factorCount_eq (n : ℕ) : factorCount n =
    Fintype.card (History (n+1)) +
      Fintype.card (BlockDecomposition.Pair (History (n+1))) := by
  have hp : Fintype.card (BlockDecomposition.Pair (History (n+1))) =
      (Fintype.card (History (n+1))).choose 2 := by
    rw [Fintype.card_subtype]
    exact Fintype.card_product_filter_lt
  rw [hp, history_card]
  rfl

theorem factorCount_pos (n : ℕ) : 0 < factorCount n := by
  unfold factorCount
  positivity

/-- Assemble a common exponential component bound without changing its size
dependence. -/
theorem product_lower (n N : ℕ) (C : ℝ)
    (f : History (n+1) → ℝ)
    (g : BlockDecomposition.Pair (History (n+1)) → ℝ)
    (hf : ∀ s, Real.exp (-C*N) ≤ f s)
    (hg : ∀ z, Real.exp (-C*N) ≤ g z) :
    Real.exp (-(C*factorCount n)*N) ≤ (∏ s, f s)*(∏ z, g z) := by
  have hi := Finset.prod_le_prod (s := Finset.univ)
    (fun (_ : History (n+1)) _ => (Real.exp_pos (-C*N)).le)
    (fun s _ => hf s)
  have hc := Finset.prod_le_prod (s := Finset.univ)
    (fun (_ : BlockDecomposition.Pair (History (n+1))) _ => (Real.exp_pos (-C*N)).le)
    (fun z _ => hg z)
  have h := mul_le_mul hi hc (Finset.prod_nonneg fun _ _ => (Real.exp_pos (-C*N)).le)
    (Finset.prod_nonneg fun s _ => (Real.exp_pos (-C*N)).le.trans (hf s))
  simp only [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul] at h
  rw [← Real.exp_add] at h
  have heq : -(C*factorCount n)*(N : ℝ) =
      (Fintype.card (History (n+1)) : ℝ)*(-C*N) +
      (Fintype.card (BlockDecomposition.Pair (History (n+1))) : ℝ)*(-C*N) := by
    rw [factorCount_eq, Nat.cast_add]
    ring
  rw [heq]
  exact h

end MajorityDynamics.GraphProcess.BlockCountProbability
