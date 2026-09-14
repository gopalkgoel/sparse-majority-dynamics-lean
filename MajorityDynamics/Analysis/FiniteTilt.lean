import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Identifying a finite exponential-family parameter

An elementary finite-sum proof of the injectivity step in Appendix E.1.
For positive probability weights, `(p-q)(log p-log q)` is nonnegative,
with equality only when `p=q`. Equal means and an affine log-likelihood
ratio make its sum zero. Full affine support then identifies the parameter.
This avoids differentiating a partition function; no analytic input is assumed.
-/

noncomputable section
open scoped BigOperators

namespace MajorityDynamics.Analysis.FiniteTilt

variable {α ι : Type*} [Fintype ι]

/-- The finite support is contained in no affine hyperplane of the coordinate space. -/
def FullAffineSupport (S : Finset α) (x : α → ι → ℝ) : Prop :=
  ∀ (u : ι → ℝ) (c : ℝ), (∀ a ∈ S, ∑ i, u i * x a i = c) → u = 0

theorem FullAffineSupport.nonempty [Nonempty ι] {S : Finset α} {x : α → ι → ℝ}
    (h : FullAffineSupport S x) : S.Nonempty := by
  by_contra he
  have hz := h (fun _ => 1) 0 (by simp [Finset.not_nonempty_iff_eq_empty.mp he])
  obtain ⟨i⟩ := ‹Nonempty ι›
  have := congrFun hz i
  norm_num at this

/-- Normalized positive weights with the same means identify any affine
log-likelihood parameter, provided the support spans the whole affine space. -/
theorem parameter_eq_zero (S : Finset α) (x : α → ι → ℝ)
    (hspan : FullAffineSupport S x) (p q : α → ℝ)
    (hp : ∀ a ∈ S, 0 < p a) (hq : ∀ a ∈ S, 0 < q a)
    (hp1 : ∑ a ∈ S, p a = 1) (hq1 : ∑ a ∈ S, q a = 1)
    (hmean : ∀ i, ∑ a ∈ S, p a * x a i = ∑ a ∈ S, q a * x a i)
    (u : ι → ℝ) (c : ℝ)
    (hlog : ∀ a ∈ S, Real.log (p a) - Real.log (q a) = c + ∑ i, u i * x a i) :
    u = 0 := by
  have hpos : ∀ a ∈ S, 0 ≤ (p a - q a) * (Real.log (p a) - Real.log (q a)) := by
    intro a ha
    by_cases h : q a ≤ p a
    · exact mul_nonneg (sub_nonneg.mpr h)
        (sub_nonneg.mpr (Real.log_le_log (hq a ha) h))
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (le_of_not_ge h))
        (sub_nonpos.mpr (Real.log_le_log (hp a ha) (le_of_not_ge h)))
  have hsum : ∑ a ∈ S, (p a - q a) * (Real.log (p a) - Real.log (q a)) = 0 := by
    calc
      _ = ∑ a ∈ S, (p a - q a) * (c + ∑ i, u i * x a i) :=
        Finset.sum_congr rfl (fun a ha => by rw [hlog a ha])
      _ = c * ((∑ a ∈ S, p a) - ∑ a ∈ S, q a) +
          ∑ i, u i * ((∑ a ∈ S, p a * x a i) - ∑ a ∈ S, q a * x a i) := by
        simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_sub,
          Finset.sum_sub_distrib]
        rw [Finset.sum_comm]
        congr 1
        · simp [Finset.mul_sum, mul_comm, mul_sub, Finset.sum_sub_distrib]
        · simp [Finset.mul_sum, sub_mul, mul_sub, Finset.sum_sub_distrib,
            mul_left_comm]
      _ = 0 := by simp [hp1, hq1, hmean]
  have heq : ∀ a ∈ S, p a = q a := by
    intro a ha
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hpos).mp hsum a ha
    rcases mul_eq_zero.mp hz with hz | hz
    · exact sub_eq_zero.mp hz
    · exact (Real.log_injOn_pos (hp a ha) (hq a ha)) (sub_eq_zero.mp hz)
  apply hspan u (-c)
  intro a ha
  have h := hlog a ha
  rw [heq a ha, sub_self] at h
  linarith

end MajorityDynamics.Analysis.FiniteTilt
