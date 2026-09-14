import MajorityDynamics.StrongBijection

/-!
# Exact contracts for perturbations of strong bijections

Source: `latest/main.tex`, Appendix D.3, `thm:perturbed-bijection`.
The radius agrees with the paper's maximum plus one for nonempty compact K.
Adding zero to the supremum set assigns radius one to empty K, where the
conclusion is vacuous. No convexity of the target or compact set is assumed.
All constants precede the varying perturbation, error and target point.
-/

noncomputable section

open Set

namespace MajorityDynamics.Analysis.Perturbation

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ} {B : Set (Space d)}

/-- The prescribed approximation radius; the inserted zero handles empty K. -/
def inverseRadius (f : StrongBijection B) (K : Set (Space d)) : ℝ :=
  sSup (insert 0 ((fun y => ‖f.invFun y‖) '' K)) + 1

/-- Geometry and inverse control supplied independently of the fixed-point argument. -/
def CompactControl (f : StrongBijection B) (K : Set (Space d)) : Prop :=
  ∃ (V : Set (Space d)) (r L : ℝ),
    IsCompact V ∧ K ⊆ V ∧ V ⊆ B ∧ 0 < r ∧ 1 ≤ L ∧
      (∀ y ∈ K, ∀ z, ‖z - y‖ ≤ r → z ∈ V) ∧
      ∀ u ∈ V, ∀ v ∈ V, ‖f.invFun u - f.invFun v‖ ≤ L * ‖u - v‖

/-- The local correction-map argument with an arbitrary absolute error δ. -/
def LocalPerturbationTheorem : Prop :=
  ∀ (d : ℕ) (B : Set (Space d)) (f : StrongBijection B)
    (V : Set (Space d)) (y : Space d) (r L R δ : ℝ),
    V ⊆ B → y ∈ V → 0 < r → 0 ≤ L → 0 ≤ δ →
    (∀ z, ‖z - y‖ ≤ r → z ∈ V) →
    (∀ u ∈ V, ∀ v ∈ V, ‖f.invFun u - f.invFun v‖ ≤ L * ‖u - v‖) →
    ‖f.invFun y‖ + 1 ≤ R → δ < r → L * δ ≤ 1 →
    ∀ g : Space d → Space d, Continuous g →
      (∀ x, ‖x‖ ≤ R → ‖g x - f.toFun x‖ ≤ δ) →
      ∃ x, g x = y ∧ ‖x - f.invFun y‖ ≤ L * δ

/-- Uniform solvability and the quantitative inverse bound on the exact fixed ball. -/
def PerturbationAt (f : StrongBijection B) (K : Set (Space d)) (C₀ : ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 0 < C ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ g : Space d → Space d, Continuous g →
        (∀ x, ‖x‖ ≤ inverseRadius f K → ‖g x - f.toFun x‖ ≤ C₀ * ε) →
        ∀ y ∈ K, ∃ x, g x = y ∧ ‖x - f.invFun y‖ ≤ C * ε

/-- The paper's full D.3 target, with no internal proof contracts as hypotheses. -/
def PerturbationTheorem : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (B : Set (Space d)) (f : StrongBijection B)
    (K : Set (Space d)), IsCompact K → K ⊆ B →
    ∀ C₀ : ℝ, 0 < C₀ → PerturbationAt f K C₀

end MajorityDynamics.Analysis.Perturbation
