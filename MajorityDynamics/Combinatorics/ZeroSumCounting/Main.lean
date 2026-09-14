import MajorityDynamics.Combinatorics.ZeroSumCounting.Fiber
import MajorityDynamics.Combinatorics.ZeroSumCounting.Growth

/-!
# Lemma A.11 (`lem:basic_counting`): the public endpoint

`zero_sum_counting : ZeroSumCountingTheorem`. The constant is
`K = zeroSumRate T C = 5 + 3 log(2CT+1) + |log C|` (it depends on `T`, `C` only) and the
threshold is `n₀ = 1`: the counting bound `card_boxZeroSum_ge` is exact for every `n`, and the
analytic bridge `exp_bound` absorbs every loss into `Kn` for every `n ≥ 1`. The density
interval is used only to get `√(np) ≤ T n` (from `p < T n^{-θ} ≤ T`) and `np ≥ 0`.

`zero_sum_counting_fixed_radius` is the reusable fixed-radius form: for every `n ≥ 1` and
every real `x ∈ [0, T n]`, `exp(-K n) xⁿ ≤ |Z(n, C x)|`.
-/

noncomputable section

namespace MajorityDynamics.Combinatorics.ZeroSumCounting

/-- The fixed-radius helper: for every `n ≥ 1` and every `0 ≤ x ≤ T n`,
`exp(-K(T,C) n) xⁿ ≤ |{y : Fin n → ℤ | ∀ i, |yᵢ| ≤ C x, ∑ y = 0}|`. -/
theorem zero_sum_counting_fixed_radius {T C : ℝ} (hT : 1 < T) (hC : 0 < C) (n : ℕ) (hn : 1 ≤ n)
    (x : ℝ) (hx0 : 0 ≤ x) (hxT : x ≤ T * n) :
    Real.exp (-zeroSumRate T C * n) * x ^ n ≤ ((zeroSumVectors n (C * x)).card : ℝ) := by
  rw [zeroSumVectors_eq_boxZeroSum n (mul_nonneg hC.le hx0)]
  exact (exp_bound hT hC n hn x hx0 hxT).trans (card_boxZeroSum_ge n ⌊C * x⌋₊)

/-- `√(np) ≤ T n` throughout the density interval, for `n ≥ 1`. -/
theorem sqrt_le_of_density {θ T : ℝ} (hθ : 0 ≤ θ) (hT : 1 < T) (n : ℕ) (hn : 1 ≤ n) (p : ℝ)
    (hp2 : p < T * (n : ℝ) ^ (-θ)) : Real.sqrt ((n : ℝ) * p) ≤ T * n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ (-θ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  have hTn : 1 ≤ T * n := by nlinarith
  have hp : p ≤ T := by
    have : T * (n : ℝ) ^ (-θ) ≤ T * 1 := mul_le_mul_of_nonneg_left hpow (by linarith)
    linarith
  have hnp : (n : ℝ) * p ≤ (T * n) ^ 2 := by nlinarith
  rw [Real.sqrt_le_left (by linarith)]
  exact hnp

/-- Lemma A.11 (`lem:basic_counting`). -/
theorem zero_sum_counting : ZeroSumCountingTheorem := by
  intro θ T C hθ _ hT hC
  refine ⟨zeroSumRate T C, zeroSumRate_pos hT hC, 1, fun n hn p hp1 hp2 ↦ ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp0 : 0 ≤ p := by
    have : 0 < T⁻¹ * (n : ℝ) ^ (-θ) :=
      mul_pos (inv_pos.mpr (by linarith)) (Real.rpow_pos_of_pos (by linarith) _)
    linarith
  exact zero_sum_counting_fixed_radius hT hC n hn _ (Real.sqrt_nonneg _)
    (sqrt_le_of_density (by linarith) hT n hn p hp2)

end MajorityDynamics.Combinatorics.ZeroSumCounting
