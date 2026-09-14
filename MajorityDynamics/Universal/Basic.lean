import MajorityDynamics.Analysis.ConditionalGaussian.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Histories and the concrete Gaussian row model

Source: §4, `def:gaussian-row` and `def:universal-nu-mu`.
`History k` is a finite coordinate type equipped with an equivalence to binary
strings of length `k`. This keeps the existing Euclidean Gaussian API literal:
there is no change of norm or abstract replacement for the probability law.
The parameter `n` in cones and levels denotes paper day `k = n + 1`.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped Matrix RealInnerProductSpace

namespace MajorityDynamics.Universal

open MajorityDynamics.Analysis

abbrev History (k : ℕ) := Fin (Fintype.card (Fin k → Bool))
abbrev Row (k : ℕ) := ConditionalGaussian.Space (Fintype.card (Fin k → Bool))

def bits (k : ℕ) : History k ≃ (Fin k → Bool) := (Fintype.equivFin _).symm

def sign (b : Bool) : ℝ := if b then -1 else 1

def append {k : ℕ} (s : History k) (b : Bool) : History (k + 1) :=
  (bits (k + 1)).symm (Fin.snoc (bits k s) b)

def parent {k : ℕ} (s : History (k + 1)) : History k :=
  (bits k).symm (Fin.init (bits (k + 1) s))

def last {k : ℕ} (s : History (k + 1)) : Bool := bits (k + 1) s (Fin.last k)

def flip {k : ℕ} (s : History k) : History k :=
  (bits k).symm (fun i => !(bits k s i))

def bitFlip {k : ℕ} (r : Fin k) (s : History k) : History k :=
  (bits k).symm (Function.update (bits k s) r (!(bits k s r)))

def character {k : ℕ} (r : Fin k) (t : History k) : ℝ := sign (bits k t r)

/-- The unsigned history imbalance; paper's `Z` includes the following sign. -/
def imbalance {k : ℕ} (r : Fin k) (x : Row k) : ℝ :=
  ∑ t, character r t * x t

def historyMatrix {n : ℕ} (s : History (n + 1)) :
    Matrix (Fin n) (History (n + 1)) ℝ :=
  fun r t => sign (bits (n + 1) s r.succ) * character r.castSucc t

def historyCone {n : ℕ} (s : History (n + 1)) : Set (Row (n + 1)) :=
  ConditionalGaussian.cone (historyMatrix s)

def childCone {n : ℕ} (s : History (n + 1)) (b : Bool) : Set (Row (n + 1)) :=
  historyCone s ∩ {x | 0 < sign b * imbalance (Fin.last n) x}

/-- Keep the old opinion on ties, exactly as in §2's relations `≥_{ab}`. -/
def decision (old new : Bool) (z : ℝ) : Prop :=
  0 < sign new * z ∨ (z = 0 ∧ new = old)

def historyEvent {n : ℕ} (s : History (n + 1)) : Set (Row (n + 1)) :=
  {x | ∀ r : Fin n,
    decision (bits (n + 1) s r.castSucc) (bits (n + 1) s r.succ)
      (imbalance r.castSucc x)}

def childEvent {n : ℕ} (s : History (n + 1)) (b : Bool) : Set (Row (n + 1)) :=
  historyEvent s ∩ {x | decision (last s) b (imbalance (Fin.last n) x)}

def covariance {k : ℕ} (ν : History k → ℝ) : ConditionalGaussian.Covariance (Fintype.card (Fin k → Bool)) :=
  Matrix.diagonal ν

def rowLaw {k : ℕ} (ν : History k → ℝ) (γ : Row k) : Measure (Row k) :=
  ConditionalGaussian.gaussianLaw (covariance ν) γ

def meanMap {n : ℕ} (s : History (n + 1)) (ν : History (n + 1) → ℝ) :=
  ConditionalGaussian.conditionalMean (covariance ν) (historyCone s)

def rowFlip {k : ℕ} (x : Row k) : Row k := WithLp.toLp 2 (fun t => x (flip t))

/-- Data at one level. Positivity and cone membership are proved separately. -/
structure Level (n : ℕ) where
  ν : History (n + 1) → ℝ
  μ : History (n + 1) → History (n + 1) → ℝ

def Level.weightedRow {n : ℕ} (a : Level n) (s : History (n + 1)) : Row (n + 1) :=
  WithLp.toLp 2 (fun t => a.ν t * a.μ s t)

structure Level.Valid {n : ℕ} (a : Level n) : Prop where
  positive : ∀ s, 0 < a.ν s
  total : ∑ s, a.ν s = 1
  symmetric : ∀ s t, a.μ s t = a.μ t s
  cone : ∀ s, a.weightedRow s ∈ historyCone s

structure Level.FlipInvariant {n : ℕ} (a : Level n) : Prop where
  ν_flip : ∀ s, a.ν (flip s) = a.ν s
  μ_flip : ∀ s t, a.μ (flip s) (flip t) = a.μ s t

end MajorityDynamics.Universal
