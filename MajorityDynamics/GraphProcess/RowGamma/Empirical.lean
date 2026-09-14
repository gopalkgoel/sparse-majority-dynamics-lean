import MajorityDynamics.GraphProcess.RowArray.Statistics
import MajorityDynamics.Probability.DegreeConcentration.Cut

/-! Empirical centering for the literal ordered-total Gamma statistic. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace MajorityDynamics.GraphProcess.RowGamma
open Universal
variable {V : Type*} [Fintype V] {n : ℕ}

def normalizedSquare (p : ℝ) (π : V → History (n + 1)) (v : V)
    (t : History (n + 1)) (d : RowArray.Ambient π) : ℝ :=
  ((RowArray.values d v t : ℝ) - p * Local.partSizes π t)^2 /
    (p * Fintype.card V)

theorem empirical_sum_le (π : V → History (n + 1)) (d : RowArray.Ambient π)
    (s t : History (n + 1)) (a : ℝ) :
    (∑ v ∈ History.block π s,
      ((RowArray.values d v t : ℝ) - (RowArray.totals d s t : ℝ) /
        (Local.partSizes π s : ℝ))^2) ≤
    ∑ v ∈ History.block π s, ((RowArray.values d v t : ℝ) - a)^2 := by
  classical
  let S := History.block π s
  let f := fun v => (RowArray.values d v t : ℝ)
  have hmean : (RowArray.totals d s t : ℝ) = ∑ v ∈ S, f v := by
    simp only [RowArray.totals, History.edgeTotals, Int.cast_sum, S, f]
  rw [hmean, ← History.block_card_partSizes]
  change (∑ v ∈ S, (f v - (∑ v ∈ S, f v) / (S.card : ℝ))^2) ≤
    ∑ v ∈ S, (f v - a)^2
  by_cases hz : S.card = 0
  · have : S = ∅ := Finset.card_eq_zero.mp hz
    simp [this]
  let m := (∑ v ∈ S, f v) / (S.card : ℝ)
  have hcard : (S.card : ℝ) ≠ 0 := by exact_mod_cast hz
  have hsum : ∑ v ∈ S, f v = (S.card : ℝ) * m := by
    dsimp [m]
    rw [mul_div_cancel₀ _ hcard]
  have key : (∑ v ∈ S, (f v - a)^2) - (∑ v ∈ S, (f v - m)^2) =
      (S.card : ℝ) * (m - a)^2 := by
    rw [← Finset.sum_sub_distrib]
    have h1 : ∀ v, (f v - a)^2 - (f v - m)^2 =
        (m-a)*(2*f v) - (m-a)*(a+m) := fun _ => by ring
    simp_rw [h1]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul, hsum]
    ring
  nlinarith [mul_nonneg (Nat.cast_nonneg S.card) (sq_nonneg (m-a))]

theorem gamma_of_normalized_sums (π : V → History (n + 1))
    (d : RowArray.Ambient π) {p C : ℝ} (hp : 0 < p)
    (hN : 0 < Fintype.card V)
    (h : ∀ s t, ∑ v ∈ History.block π s, normalizedSquare p π v t d ≤
      C * Fintype.card V) :
    RowArray.Gamma π (RowArray.totals d) C p d := by
  have hNr : (0 : ℝ) < Fintype.card V := by exact_mod_cast hN
  intro s t
  have he := empirical_sum_le π d s t (p * Local.partSizes π t)
  have hs := h s t
  simp only [normalizedSquare, ← Finset.sum_div] at hs
  have hs' := (div_le_iff₀ (mul_pos hp hNr)).mp hs
  rw [one_div, ← div_eq_inv_mul]
  apply (div_le_iff₀ (by positivity : 0 < p * (Fintype.card V : ℝ)^2)).mpr
  nlinarith

theorem normalizedSquare_nonneg {p : ℝ} (hp : 0 ≤ p)
    (π : V → History (n + 1)) (v : V) (t : History (n + 1))
    (d : RowArray.Ambient π) : 0 ≤ normalizedSquare p π v t d :=
  div_nonneg (sq_nonneg _) (mul_nonneg hp (Nat.cast_nonneg _))

end MajorityDynamics.GraphProcess.RowGamma

/-- info: 'MajorityDynamics.GraphProcess.RowGamma.empirical_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.RowGamma.empirical_sum_le

/-- info: 'MajorityDynamics.GraphProcess.RowGamma.gamma_of_normalized_sums' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.GraphProcess.RowGamma.gamma_of_normalized_sums
