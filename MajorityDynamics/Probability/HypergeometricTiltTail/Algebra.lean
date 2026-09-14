import MajorityDynamics.Probability.FixedSizeExponential.Basic

noncomputable section
open scoped BigOperators
namespace MajorityDynamics.Probability.HypergeometricTiltTail

/-- The literal selected-minus-unselected weight on an actual finite population. -/
def tiltWeight {V : Type*} [DecidableEq V] (P R : Finset V)
    (p L : ℝ) (β : V → ℝ) : ℝ :=
  (∑ v ∈ R, β v) / Real.sqrt (p * L) -
    (∑ v ∈ P \ R, β v) * Real.sqrt (p * L) / L

/-- The coefficient of a selected vertex after removing the population constant. -/
def tiltCoefficient {V : Type*} (p L : ℝ) (β : V → ℝ) (v : V) : ℝ :=
  (1 + p) * β v / Real.sqrt (p * L)

/-- The population constant in the exact linearization. -/
def tiltConstant {V : Type*} (P : Finset V) (p L : ℝ) (β : V → ℝ) : ℝ :=
  Real.sqrt (p * L) / L * ∑ v ∈ P, β v

theorem sqrt_div_eq {p L : ℝ} (hp : 0 < p) (hL : 0 < L) :
    Real.sqrt (p * L) / L = p / Real.sqrt (p * L) := by
  have hs : 0 < Real.sqrt (p * L) := Real.sqrt_pos.2 (mul_pos hp hL)
  have he := Real.sq_sqrt (mul_pos hp hL).le
  field_simp
  nlinarith

/-- Exact weight linearization, for an actual subset of the population. -/
theorem tiltWeight_linear {V : Type*} [DecidableEq V]
    {P R : Finset V} (hRP : R ⊆ P) {p L : ℝ} (hp : 0 < p) (hL : 0 < L)
    (β : V → ℝ) :
    tiltWeight P R p L β = (∑ v ∈ R, tiltCoefficient p L β v) -
      tiltConstant P p L β := by
  have hsum := Finset.sum_sdiff hRP (f := β)
  unfold tiltWeight tiltCoefficient tiltConstant
  rw [← Finset.sum_div, ← Finset.mul_sum]
  rw [mul_div_assoc, sqrt_div_eq hp hL, ← hsum]
  ring

/-- Split the selected weight into its two independent pieces. -/
theorem tiltWeight_union {V : Type*} [DecidableEq V]
    {P S R Q : Finset V} (hSP : S ⊆ P) (hRS : R ⊆ S) (hQ : Q ⊆ P \ S)
    {p L : ℝ} (hp : 0 < p) (hL : 0 < L) (β : V → ℝ) :
    tiltWeight P (R ∪ Q) p L β =
      (∑ v ∈ R, tiltCoefficient p L β v) +
      (∑ v ∈ Q, tiltCoefficient p L β v) - tiltConstant P p L β := by
  have hRP : R ∪ Q ⊆ P := Finset.union_subset (hRS.trans hSP)
    (hQ.trans Finset.sdiff_subset)
  rw [tiltWeight_linear hRP hp hL]
  rw [Finset.sum_union]
  exact Finset.disjoint_left.mpr (by
    intro x hxR hxQ
    exact (Finset.mem_sdiff.mp (hQ hxQ)).2 (hRS hxR))

/-- Sum of coefficients on a genuine subpopulation. -/
theorem sum_tiltCoefficient {V : Type*} (A : Finset V) (p L : ℝ) (β : V → ℝ) :
    (∑ v ∈ A, tiltCoefficient p L β v) =
      (1 + p) / Real.sqrt (p * L) * ∑ v ∈ A, β v := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  unfold tiltCoefficient
  ring

/-- The exact two-piece mean agrees with the centered coefficient formula. -/
theorem pair_mean_eq {V : Type*} [DecidableEq V]
    {P S : Finset V} (hSP : S ⊆ P) {p L : ℝ} (hp : 0 < p) (hL : 0 < L)
    (β : V → ℝ) (k l : ℕ) :
    (k : ℝ) / S.card * (∑ v ∈ S, tiltCoefficient p L β v) +
      (l : ℝ) / (P \ S).card * (∑ v ∈ P \ S, tiltCoefficient p L β v) -
      tiltConstant P p L β =
    ((1 + p) * k / S.card - p) * (∑ v ∈ S, β v) / Real.sqrt (p * L) +
      ((1 + p) * l / (P \ S).card - p) *
        (∑ v ∈ P \ S, β v) / Real.sqrt (p * L) := by
  rw [sum_tiltCoefficient, sum_tiltCoefficient]
  unfold tiltConstant
  rw [sqrt_div_eq hp hL]
  have hs := Finset.sum_sdiff hSP (f := β)
  rw [← hs]
  ring

end MajorityDynamics.Probability.HypergeometricTiltTail
