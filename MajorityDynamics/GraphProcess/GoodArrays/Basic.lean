import MajorityDynamics.GraphProcess.EnumerationBounds.Basic
import MajorityDynamics.Local.Admissibility

noncomputable section
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.GoodArrays
open Universal
variable {V : Type*} [Fintype V] {n : ℕ}

def labelCount (n : ℕ) : ℕ := 2^(n+1)

def window (n : ℕ) (T p : ℝ) (N : ℕ) : ℝ :=
  Real.sqrt (p*N) / (100*T*(labelCount n : ℝ))

def radiusCoefficient (n : ℕ) (T : ℝ) : ℝ :=
  1 / (200*T*(labelCount n : ℝ))

def E0 (y : Local.CoarseData V n) (T p : ℝ) : Finset (RowArray.Ambient y.part) :=
  Finset.univ.filter fun d => RowArray.totals d = y.edge ∧
    ∀ s t v, v ∈ History.block y.part s →
      |(RowArray.values d v t : ℝ) - EnumerationBounds.avg y s t| ≤
        window n T p (Fintype.card V)

@[simp] theorem mem_E0 (y : Local.CoarseData V n) (T p : ℝ)
    (d : RowArray.Ambient y.part) : d ∈ E0 y T p ↔
      RowArray.totals d = y.edge ∧ ∀ s t v, v ∈ History.block y.part s →
        |(RowArray.values d v t : ℝ) - (y.edge s t : ℝ)/(y.sizes s : ℝ)| ≤
          Real.sqrt (p*Fintype.card V)/(100*T*((2^(n+1) : ℕ) : ℝ)) := by
  simp [E0, EnumerationBounds.avg, window, labelCount]

def Separated (y : Local.CoarseData V n) (T p : ℝ) : Prop :=
  ∀ s (r : Fin n),
    decision (bits (n+1) s r.castSucc) (bits (n+1) s r.succ)
      ((∑ t, character r.castSucc t * y.realEdges s t) -
        sign (bits (n+1) s r.succ) * (T⁻¹ * Local.edgeScale (Fintype.card V) p))

/-- Finite numerical preparation, proved uniformly from the original hypotheses. -/
structure Regime (y : Local.CoarseData V n) (T p : ℝ) : Prop where
  card_pos : 0 < (Fintype.card V : ℝ)
  density_pos : 0 < p
  size_pos : ∀ s, 0 < (y.sizes s : ℝ)
  center : ∀ s t, |EnumerationBounds.avg y s t - p*(y.sizes t : ℝ)| ≤
    T^2*Real.sqrt (p*Fintype.card V)
  lower : ∀ s t, window n T p (Fintype.card V) ≤ EnumerationBounds.avg y s t
  upper : ∀ s t, EnumerationBounds.avg y s t + window n T p (Fintype.card V) ≤
    (y.sizes t : ℝ)-1
  radius : 1 + radiusCoefficient n T * Real.sqrt (p*Fintype.card V) ≤
    window n T p (Fintype.card V)
  sqrt_size : ∀ s, Real.sqrt (p*Fintype.card V) ≤ T*(y.sizes s : ℝ)
  regular : (T^2+1)*Real.sqrt (p*Fintype.card V) ≤ (p*Fintype.card V)^(4/7:ℝ)

theorem labelCount_pos (n : ℕ) : 0 < labelCount n := by unfold labelCount; positivity

theorem radiusCoefficient_pos (n : ℕ) {T : ℝ} (hT : 1 < T) :
    0 < radiusCoefficient n T := by
  unfold radiusCoefficient
  have : (0 : ℝ) < labelCount n := by exact_mod_cast labelCount_pos n
  positivity

end MajorityDynamics.GraphProcess.GoodArrays
