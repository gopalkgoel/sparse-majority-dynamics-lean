import MajorityDynamics.Literature.Goals.ErdosGallai.Statement
import MajorityDynamics.Literature.Goals.GaleRyser.Statement

/-! The paper's maximum-degree sufficient conditions, using shared classical
vocabulary. The two literature criteria themselves live under `Literature/Goals/`. -/
namespace MajorityDynamics.Combinatorics.SufficientGraphicality
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

def maxDegree {n : ℕ} (d : Fin n → ℕ) : ℕ := univ.sup d

def GraphicalSufficientTheorem : Prop :=
  ∀ (n : ℕ) (d : Fin n → ℕ), Even (total d) →
    maxDegree d * (maxDegree d + 1) ≤ total d → Graphical d

def BipartiteGraphicalSufficientTheorem : Prop :=
  ∀ (l n : ℕ) (a : Fin l → ℕ) (b : Fin n → ℕ), total a = total b →
    maxDegree a * maxDegree b ≤ total a → Bigraphical a b

theorem le_maxDegree {n : ℕ} (d : Fin n → ℕ) (i : Fin n) : d i ≤ maxDegree d :=
  le_sup (mem_univ i)

end
end MajorityDynamics.Combinatorics.SufficientGraphicality
