import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt

/-!
# Lemma A.11 (`lem:basic_counting`): zero-sum lattice counting — contract

This module fixes the finite set counted by Lemma A.11 of `latest/main.tex` and the target
proposition. Nothing here is an axiom; the proof is in `Fiber.lean`, `Growth.lean`, and
`Main.lean`.

## The counted set

`zeroSumVectors n ρ` is the finite set of integer vectors `y : Fin n → ℤ` with

* `|(yᵢ : ℝ)| ≤ ρ` for every coordinate (a real radius, closed inequality), and
* `∑ᵢ yᵢ = 0` exactly, in `ℤ`.

It is a `Finset`: the filter of the bounding box `∏ᵢ Icc (-⌊ρ⌋₊) ⌊ρ⌋₊` by the *real* radius
condition and the sum condition. `mem_zeroSumVectors` shows that membership is exactly the
two displayed conditions, for every real `ρ` (for `ρ < 0` the set is empty, for `ρ ≥ 0` the
box is just a bounding box); the count is always the cardinality of this actual set. The
manuscript's `J = [-C√(np), C√(np)] ∩ ℤ` is the coordinate set at `ρ = C√(np)`.

## The target

`ZeroSumCountingTheorem`: for every `θ ∈ (1/2,1)`, `T > 1`, `C > 0` there exist `K > 0` and
`n₀` such that for every natural `n ≥ n₀` and every real `p ∈ (T⁻¹ n^{-θ}, T n^{-θ})`,

  `exp(-K n) (√(np))^n ≤ |zeroSumVectors n (C √(np))|`.

`K` and `n₀` are chosen after `θ, T, C` and before `n, p`. There is no parity, integrality,
or `C ≥ 1` assumption, and `p` ranges over the whole open interval.
-/

noncomputable section

open scoped BigOperators

namespace MajorityDynamics.Combinatorics.ZeroSumCounting

/-- The bounding box `∏ᵢ Icc (-R) R` of integer vectors of length `n`. -/
def box (n R : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun _ : Fin n ↦ Finset.Icc (-(R : ℤ)) (R : ℤ)

/-- The finite set `Z(n,ρ) = {y : Fin n → ℤ | ∀ i, |yᵢ| ≤ ρ, ∑ᵢ yᵢ = 0}` of Lemma A.11. -/
def zeroSumVectors (n : ℕ) (ρ : ℝ) : Finset (Fin n → ℤ) :=
  (box n ⌊ρ⌋₊).filter fun y ↦ (∀ i, |(y i : ℝ)| ≤ ρ) ∧ ∑ i, y i = 0

/-- Membership in `zeroSumVectors` is exactly the specification: every coordinate is an
integer of absolute value at most `ρ`, and the coordinates sum to zero. -/
theorem mem_zeroSumVectors {n : ℕ} {ρ : ℝ} {y : Fin n → ℤ} :
    y ∈ zeroSumVectors n ρ ↔ (∀ i, |(y i : ℝ)| ≤ ρ) ∧ ∑ i, y i = 0 := by
  unfold zeroSumVectors
  rw [Finset.mem_filter, and_iff_right_iff_imp]
  rintro ⟨hbound, -⟩
  unfold box
  rw [Fintype.mem_piFinset]
  intro i
  have h := hbound i
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans h
  have hnat : (y i).natAbs ≤ ⌊ρ⌋₊ := by
    rw [Nat.le_floor_iff hρ, Nat.cast_natAbs, Int.cast_abs]
    exact h
  rw [Finset.mem_Icc]
  omega

/-- Lemma A.11 (`lem:basic_counting`), with the exact real-density quantifiers. -/
def ZeroSumCountingTheorem : Prop :=
  ∀ θ T C : ℝ, 1 / 2 < θ → θ < 1 → 1 < T → 0 < C →
    ∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ p : ℝ, T⁻¹ * (n : ℝ) ^ (-θ) < p → p < T * (n : ℝ) ^ (-θ) →
        Real.exp (-K * (n : ℝ)) * Real.sqrt ((n : ℝ) * p) ^ n ≤
          ((zeroSumVectors n (C * Real.sqrt ((n : ℝ) * p))).card : ℝ)

end MajorityDynamics.Combinatorics.ZeroSumCounting
