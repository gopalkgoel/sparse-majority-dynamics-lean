import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Explicit polynomial variation on a unit lattice cell -/

namespace MajorityDynamics.Analysis
open scoped BigOperators

private theorem pow_error (x y R ε : ℝ) (n : ℕ) (hR : 0 < R)
    (hx : |x| ≤ R) (hy : |y| ≤ R) (hε : |x - y| ≤ ε) :
    |x ^ n - y ^ n| ≤ ε * n * R ^ n / R := by
  cases n with
  | zero => simp
  | succ n =>
    have he : 0 ≤ ε := (abs_nonneg _).trans hε
    calc
      _ ≤ |x - y| * (n + 1 : ℕ) * max |x| |y| ^ ((n + 1) - 1) := abs_pow_sub_pow_le ..
      _ ≤ ε * (n + 1 : ℕ) * R ^ n := by
        rw [Nat.add_sub_cancel]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _))
          (pow_le_pow_left₀ (le_trans (abs_nonneg _) (le_max_left _ _)) (max_le hx hy) _)
          (by positivity) (by positivity)
      _ = _ := by rw [pow_succ]; field_simp

/-- Finite monomials vary by at most degree times the coordinate error,
with the expected one-power saving. The division form also covers degree zero. -/
theorem prod_monomial_error {ι : Type*} (S : Finset ι) (e : ι → ℕ) (x y : ι → ℝ)
    (R ε : ℝ) (hR : 0 < R) (hε : 0 ≤ ε)
    (hx : ∀ i ∈ S, |x i| ≤ R) (hy : ∀ i ∈ S, |y i| ≤ R)
    (hxy : ∀ i ∈ S, |x i - y i| ≤ ε) :
    |(∏ i ∈ S, x i ^ e i) - ∏ i ∈ S, y i ^ e i| ≤
      ε * (∑ i ∈ S, (e i : ℝ)) * R ^ (∑ i ∈ S, e i) / R := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hxS : ∀ j ∈ S, |x j| ≤ R := fun j hj => hx j (Finset.mem_insert_of_mem hj)
    have hyS : ∀ j ∈ S, |y j| ≤ R := fun j hj => hy j (Finset.mem_insert_of_mem hj)
    have hxyS : ∀ j ∈ S, |x j - y j| ≤ ε := fun j hj => hxy j (Finset.mem_insert_of_mem hj)
    have hrest := ih hxS hyS hxyS
    have hxi := hx i (Finset.mem_insert_self _ _)
    have hyi := hy i (Finset.mem_insert_self _ _)
    have hdi := hxy i (Finset.mem_insert_self _ _)
    have hpY : |∏ j ∈ S, y j ^ e j| ≤ R ^ (∑ j ∈ S, e j) := by
      rw [Finset.abs_prod, ← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun j hj => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hyS j hj) _)
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi, Finset.sum_insert hi]
    calc
      _ = |x i ^ e i * ((∏ j ∈ S, x j ^ e j) - ∏ j ∈ S, y j ^ e j) +
          (x i ^ e i - y i ^ e i) * ∏ j ∈ S, y j ^ e j| := by congr 1; ring
      _ ≤ |x i ^ e i| * |(∏ j ∈ S, x j ^ e j) - ∏ j ∈ S, y j ^ e j| +
          |x i ^ e i - y i ^ e i| * |∏ j ∈ S, y j ^ e j| := by
        simpa only [abs_mul] using abs_add_le
          (x i ^ e i * ((∏ j ∈ S, x j ^ e j) - ∏ j ∈ S, y j ^ e j))
          ((x i ^ e i - y i ^ e i) * ∏ j ∈ S, y j ^ e j)
      _ ≤ R ^ e i * (ε * (∑ j ∈ S, (e j : ℝ)) * R ^ (∑ j ∈ S, e j) / R) +
          (ε * e i * R ^ e i / R) * R ^ (∑ j ∈ S, e j) := by
        apply add_le_add
        · apply mul_le_mul _ hrest (abs_nonneg _) (by positivity)
          rw [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) hxi _
        · exact mul_le_mul (pow_error _ _ R ε (e i) hR hxi hyi hdi) hpY (abs_nonneg _) (by positivity)
      _ = _ := by rw [pow_add]; ring

end MajorityDynamics.Analysis
