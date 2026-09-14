import MajorityDynamics.Literature.DegreeEnumeration.ComparisonLaws
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Source-side quantities for the two degree enumeration theorems. Every
deviation is measured from the actual average, not the paper's reference p. -/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators
namespace MajorityDynamics.Literature.DegreeEnumeration

def graphAverage (n m : ℕ) : ℝ := 2 * (m : ℝ) / n
def graphDensity (n m : ℕ) : ℝ := graphAverage n m / ((n : ℝ) - 1)
def graphGamma {n : ℕ} (m : ℕ) (d : Fin n → ℕ) : ℝ :=
  (∑ i, ((d i : ℝ) - graphAverage n m) ^ 2) / ((n : ℝ) - 1) ^ 2
def graphCorrection {n : ℕ} (m : ℕ) (d : Fin n → ℕ) : ℝ :=
  Real.exp (1 / 4 - graphGamma m d ^ 2 /
    (4 * graphDensity n m ^ 2 * (1 - graphDensity n m) ^ 2))
def graphErrorScale (α : ℝ) (n m : ℕ) : ℝ :=
  Real.log n ^ 2 / Real.sqrt n + graphAverage n m ^ (5 * α - 3)

def GraphSourceData (α : ℝ) (n m : ℕ) (d : Fin n → ℕ) : Prop :=
  (∀ i, d i ≤ n - 1) ∧ (∑ i, d i) = 2 * m ∧
    ∀ i, |(d i : ℝ) - graphAverage n m| ≤ graphAverage n m ^ α

def bipartiteDensity (ell n m : ℕ) : ℝ := (m : ℝ) / ((ell : ℝ) * n)
def leftAverage (ell m : ℕ) : ℝ := (m : ℝ) / ell
def rightAverage (n m : ℕ) : ℝ := (m : ℝ) / n
def leftVariance {ell : ℕ} (m : ℕ) (a : Fin ell → ℕ) : ℝ :=
  (∑ i, ((a i : ℝ) - leftAverage ell m) ^ 2) / ell
def rightVariance {n : ℕ} (m : ℕ) (b : Fin n → ℕ) : ℝ :=
  (∑ j, ((b j : ℝ) - rightAverage n m) ^ 2) / n
def bipartiteCorrection {ell n : ℕ} (m : ℕ) (a : Fin ell → ℕ) (b : Fin n → ℕ) : ℝ :=
  Real.exp (-1 / 2 *
    (1 - leftVariance m a / (leftAverage ell m * (1 - bipartiteDensity ell n m))) *
    (1 - rightVariance m b / (rightAverage n m * (1 - bipartiteDensity ell n m))))
def bipartiteErrorScale (α : ℝ) (ell n m : ℕ) : ℝ :=
  Real.log ell ^ 2 / Real.sqrt ell + Real.log n ^ 2 / Real.sqrt n +
    min (leftAverage ell m) (rightAverage n m) ^ (5 * α - 5) *
      (m : ℝ) ^ 2 / ((ell : ℝ) * n)

def BipartiteSourceData (α : ℝ) (ell n m : ℕ)
    (a : Fin ell → ℕ) (b : Fin n → ℕ) : Prop :=
  (∀ i, a i ≤ n) ∧ (∀ j, b j ≤ ell) ∧
    (∑ i, a i) = m ∧ (∑ j, b j) = m ∧
    (∀ i, |(a i : ℝ) - leftAverage ell m| ≤ leftAverage ell m ^ α) ∧
    ∀ j, |(b j : ℝ) - rightAverage n m| ≤ rightAverage n m ^ α

def RelativeApproximation (bound P Q : ℝ) : Prop :=
  ∃ ε : ℝ, |ε| ≤ bound ∧ P = Q * (1 + ε)

/-- Sequence-level Theorem 1.4 of arXiv:1702.08373v3. The constant and eventual
threshold are outside all degree vectors; growth is an actual little-o statement. -/
def GraphEnumerationTheorem : Prop :=
  ∃ μ₀ : ℝ, 0 < μ₀ ∧
    ∀ α : ℝ, 1 / 2 < α → α < 3 / 5 → ∀ m : ℕ → ℕ,
      (∀ᶠ n in atTop, m n ≤ n.choose 2 ∧ graphDensity n (m n) ≤ μ₀) →
      (∀ K : ℝ, 0 < K →
        Asymptotics.IsLittleO atTop (fun n : ℕ => Real.log n ^ K / (n : ℝ))
          (fun n => graphDensity n (m n))) →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, ∀ d : Fin n → ℕ,
        GraphSourceData α n (m n) d →
        RelativeApproximation (C * graphErrorScale α n (m n))
          ((graphDegreeLaw (Fin n) (m n)).real {d})
          ((graphBinomialLaw (Fin n) (m n)).real {d} * graphCorrection (m n) d)

/-- The bipartite case of Theorem 1.1 of arXiv:2006.15797v1. Both growth
requirements and both centered degree spreads occur explicitly. -/
def BipartiteEnumerationTheorem : Prop :=
  ∃ μ₀ : ℝ, 0 < μ₀ ∧
    ∀ α : ℝ, 1 / 2 < α → α < 3 / 5 → ∀ ell m : ℕ → ℕ,
      (∀ᶠ n in atTop, 0 < ell n ∧ m n ≤ ell n * n ∧
        bipartiteDensity (ell n) n (m n) < μ₀) →
      Asymptotics.IsLittleO atTop
        (fun n => ((ell n : ℝ) + n) ^ (5 - 5 * α))
        (fun n => (ell n : ℝ) * n * (m n : ℝ) ^ (3 - 5 * α)) →
      (∀ K : ℝ, 0 < K → Asymptotics.IsLittleO atTop
        (fun n => (ell n : ℝ) * Real.log n ^ K + (n : ℝ) * Real.log (ell n) ^ K)
        (fun n => (m n : ℝ))) →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
        ∀ (a : Fin (ell n) → ℕ) (b : Fin n → ℕ),
          BipartiteSourceData α (ell n) n (m n) a b →
          RelativeApproximation (C * bipartiteErrorScale α (ell n) n (m n))
            ((bipartiteDegreeLaw (Fin (ell n)) (Fin n) (m n)).real {(a, b)})
            ((bipartiteBinomialLaw (Fin (ell n)) (Fin n) (m n)).real {(a, b)} *
              bipartiteCorrection (m n) a b)

end MajorityDynamics.Literature.DegreeEnumeration
