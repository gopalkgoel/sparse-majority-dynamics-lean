import MajorityDynamics.GraphProcess.RowArray.Statistics
import MajorityDynamics.GraphProcess.BlockDecomposition.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.EnumerationBounds
open Universal
variable {V : Type*} [Fintype V] {n : ℕ}

def avg (y : Local.CoarseData V n) (s t : History (n+1)) : ℝ :=
  (y.edge s t : ℝ) / (y.sizes s : ℝ)

def squareSum (y : Local.CoarseData V n) (d : RowArray.Ambient y.part)
    (s t : History (n+1)) : ℝ :=
  ∑ v ∈ History.block y.part s, ((RowArray.values d v t : ℝ) - avg y s t)^2

def muI (y : Local.CoarseData V n) (s : History (n+1)) : ℝ :=
  avg y s s / ((y.sizes s : ℝ) - 1)

def muC (y : Local.CoarseData V n) (s t : History (n+1)) : ℝ :=
  (y.edge s t : ℝ) / ((y.sizes s : ℝ) * (y.sizes t : ℝ))

def gamma2 (y : Local.CoarseData V n) (d : RowArray.Ambient y.part)
    (s : History (n+1)) : ℝ := squareSum y d s s / ((y.sizes s : ℝ) - 1)^2

def variance (y : Local.CoarseData V n) (d : RowArray.Ambient y.part)
    (s t : History (n+1)) : ℝ := squareSum y d s t / (y.sizes s : ℝ)

def internalCorrection (y : Local.CoarseData V n) (d : RowArray.Ambient y.part)
    (s : History (n+1)) : ℝ :=
  1/4 - (gamma2 y d s)^2 / (4 * (muI y s)^2 * (1-muI y s)^2)

def crossCorrection (y : Local.CoarseData V n) (d : RowArray.Ambient y.part)
    (s t : History (n+1)) : ℝ :=
  -(1/2) * (1 - variance y d s t / (avg y s t * (1-muC y s t))) *
    (1 - variance y d t s / (avg y t s * (1-muC y s t)))

def correction (y : Local.CoarseData V n) (d : RowArray.Ambient y.part) : ℝ :=
  (∑ s, internalCorrection y d s) +
    ∑ z : BlockDecomposition.Pair (History (n+1)), crossCorrection y d z.val.1 z.val.2

/-- An intermediate finite regime; the closed endpoints derive every field. -/
structure Prepared (y : Local.CoarseData V n) (d : RowArray.Ambient y.part)
    (T p : ℝ) : Prop where
  card_pos : 0 < (Fintype.card V : ℝ)
  density_pos : 0 < p
  mean_one : 1 ≤ p * Fintype.card V
  size_two : ∀ s, 2 ≤ (y.sizes s : ℝ)
  size_lower : ∀ s, (Fintype.card V : ℝ) / T ≤ (y.sizes s : ℝ)
  size_pred_lower : ∀ s, (Fintype.card V : ℝ) / (2*T) ≤ (y.sizes s : ℝ)-1
  avg_lower : ∀ s t, p * Fintype.card V / (2*T^2) ≤ avg y s t
  avg_upper : ∀ s t, avg y s t ≤ 2*T*p*Fintype.card V
  avg_center : ∀ s t, |avg y s t - p*(y.sizes t : ℝ)| ≤ T^2*Real.sqrt (p*Fintype.card V)
  internal_lower : ∀ s, p/(2*T^2) ≤ muI y s
  internal_upper : ∀ s, muI y s ≤ 4*T^2*p
  cross_lower : ∀ s t, p/(2*T^2) ≤ muC y s t
  cross_upper : ∀ s t, muC y s t ≤ 4*T^2*p
  density_small : 4*T^2*p ≤ 1/2
  entry : ∀ s t v, v ∈ History.block y.part s →
    |(RowArray.values d v t : ℝ)-avg y s t| ≤ 2*(p*Fintype.card V)^(4/7:ℝ)
  entry_enumeration : ∀ s t v, v ∈ History.block y.part s →
    |(RowArray.values d v t : ℝ)-avg y s t| ≤ (avg y s t)^(7/12:ℝ)

end MajorityDynamics.GraphProcess.EnumerationBounds
