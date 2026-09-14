import MajorityDynamics.GraphProcess.GoodArrays.Construction
import MajorityDynamics.Combinatorics.ZeroSumCounting.Main

noncomputable section
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.GoodArrays
open Universal Combinatorics.ZeroSumCounting
variable {V : Type*} [Fintype V] {n : ℕ}

/-- Every vertex contributes one coordinate for each target history. -/
theorem ordered_size_sum (y : Local.CoarseData V n) :
    ∑ s, ∑ _t : Universal.History (n+1), y.sizes s =
      labelCount n * Fintype.card V := by
  simp_rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, history_card]
  rw [← Finset.mul_sum, y.sum_sizes]
  rfl

/-- The exponential loss depends only on the fixed history length and size constant. -/
def countingRate (n : ℕ) (T : ℝ) : ℝ :=
  zeroSumRate T (radiusCoefficient n T) * (labelCount n : ℝ)

theorem countingRate_pos (n : ℕ) {T : ℝ} (hT : 1 < T) :
    0 < countingRate n T := by
  exact mul_pos (zeroSumRate_pos hT (radiusCoefficient_pos n hT))
    (by exact_mod_cast labelCount_pos n)

private theorem prod_exp_pow {ι : Type*} (S : Finset ι) (m : ι → ℕ) (K x : ℝ) :
    (∏ i ∈ S, Real.exp (-K * m i) * x ^ m i) =
      Real.exp (-K * (∑ i ∈ S, m i)) * x ^ (∑ i ∈ S, m i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
    push_cast
    rw [mul_add, Real.exp_add, pow_add]
    ring

/-- A.11 applied independently to every ordered cell, followed by the actual injection. -/
theorem card_E0_sqrt (y : Local.CoarseData V n) (T p : ℝ)
    (hT : 1 < T) (hreg : Regime y T p) :
    Real.exp (-countingRate n T * Fintype.card V) *
      (Real.sqrt (p * Fintype.card V)) ^ (labelCount n * Fintype.card V) ≤
        ((E0 y T p).card : ℝ) := by
  let K := zeroSumRate T (radiusCoefficient n T)
  let x := Real.sqrt (p * Fintype.card V)
  have hcell (s : Universal.History (n+1)) :
      Real.exp (-K * y.sizes s) * x ^ y.sizes s ≤
        ((zeroSumVectors (y.sizes s) (radiusCoefficient n T * x)).card : ℝ) := by
    exact zero_sum_counting_fixed_radius hT (radiusCoefficient_pos n hT)
      (y.sizes s) (by
        have hs : 0 < y.sizes s := by exact_mod_cast hreg.size_pos s
        omega)
      x (Real.sqrt_nonneg _) (hreg.sqrt_size s)
  have hprod := Finset.prod_le_prod
    (s := Finset.univ)
    (f := fun s : Universal.History (n+1) =>
      ∏ _t : Universal.History (n+1), Real.exp (-K * y.sizes s) * x ^ y.sizes s)
    (g := fun s : Universal.History (n+1) =>
      ∏ _t : Universal.History (n+1),
        ((zeroSumVectors (y.sizes s) (radiusCoefficient n T * x)).card : ℝ))
    (fun s _ => Finset.prod_nonneg fun _ _ =>
      mul_nonneg (Real.exp_pos _).le (pow_nonneg (Real.sqrt_nonneg _) _))
    (fun s _ => Finset.prod_le_prod
      (fun _ _ => mul_nonneg (Real.exp_pos _).le (pow_nonneg (Real.sqrt_nonneg _) _))
      (fun _ _ => hcell s))
  have hid :
      (∏ s : Universal.History (n+1), ∏ _t : Universal.History (n+1),
        Real.exp (-K * y.sizes s) * x ^ y.sizes s) =
      Real.exp (-countingRate n T * Fintype.card V) *
        x ^ (labelCount n * Fintype.card V) := by
    simp_rw [prod_exp_pow]
    rw [ordered_size_sum]
    congr 2
    simp only [Nat.cast_mul, countingRate, K]
    ring
  rw [hid] at hprod
  exact hprod.trans (by exact_mod_cast product_card_le_E0 y T p hreg)

theorem sqrt_pow_eq_rpow (x : ℝ) (hx : 0 ≤ x) (m : ℕ) :
    (Real.sqrt x) ^ m = x ^ ((m : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hx]
  congr 1
  ring

/-- The literal real-division exponent in `eq:E0-count`. -/
theorem card_E0 (y : Local.CoarseData V n) (T p : ℝ)
    (hT : 1 < T) (hreg : Regime y T p) :
    Real.exp (-countingRate n T * Fintype.card V) *
      (p * Fintype.card V) ^ (((labelCount n * Fintype.card V : ℕ) : ℝ) / 2) ≤
        ((E0 y T p).card : ℝ) := by
  have h := card_E0_sqrt y T p hT hreg
  rwa [sqrt_pow_eq_rpow _ (mul_nonneg hreg.density_pos.le hreg.card_pos.le)] at h

end MajorityDynamics.GraphProcess.GoodArrays
