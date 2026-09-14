import MajorityDynamics.Combinatorics.ZeroSumCounting.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

/-!
# The combinatorial core: a pigeonhole lower bound for zero-sum box vectors

For every length `n` and integer radius `R`, with `m = n / 2`,

  `((2R+1)^m / (2mR+1))² ≤ |{y ∈ [-R,R]^n : ∑ y = 0}|`   (`card_boxZeroSum_ge`).

Route: the `(2R+1)^m` vectors of `[-R,R]^m` have sums in `[-mR, mR]`, an interval of
`2mR+1` integers, so by pigeonhole some sum-fiber `F_s` has at least `(2R+1)^m/(2mR+1)`
elements. For `(u, v) ∈ F_s × F_s` the vector `(u, -v, 0, …, 0)` of length `n = m + m + ε`
(`ε = n - 2m ∈ {0,1}`) has all coordinates in `[-R,R]` and sum `s - s = 0`, and the map
`(u,v) ↦ (u,-v,0)` is injective, so `|F_s|² ≤ |Z|`. No parity assumption is needed: the
zero block has length `ε`. This replaces the manuscript's Chebyshev-plus-correction-block
argument by an exact counting argument with the same `(2R+1)^{n}/poly(n,R)` scale.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace MajorityDynamics.Combinatorics.ZeroSumCounting

/-- The zero-sum vectors of the integer box `[-R,R]^n`. -/
def boxZeroSum (n R : ℕ) : Finset (Fin n → ℤ) :=
  (box n R).filter fun y ↦ ∑ i, y i = 0

theorem mem_box {n R : ℕ} {y : Fin n → ℤ} :
    y ∈ box n R ↔ ∀ i, -(R : ℤ) ≤ y i ∧ y i ≤ R := by
  unfold box
  rw [Fintype.mem_piFinset]
  simp only [Finset.mem_Icc]

theorem card_Icc_symm (R : ℕ) : (Finset.Icc (-(R : ℤ)) (R : ℤ)).card = 2 * R + 1 := by
  rw [Int.card_Icc, show (R : ℤ) + 1 - -(R : ℤ) = ((2 * R + 1 : ℕ) : ℤ) by push_cast; ring,
    Int.toNat_natCast]

theorem card_box (n R : ℕ) : (box n R).card = (2 * R + 1) ^ n := by
  rw [box, Fintype.card_piFinset]
  simp only [card_Icc_symm, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem sum_mem_Icc_of_mem_box {n R : ℕ} {y : Fin n → ℤ} (hy : y ∈ box n R) :
    ∑ i, y i ∈ Finset.Icc (-((n : ℤ) * R)) ((n : ℤ) * R) := by
  rw [mem_box] at hy
  rw [Finset.mem_Icc]
  constructor
  · calc -((n : ℤ) * R) = ∑ _i : Fin n, -(R : ℤ) := by simp
      _ ≤ ∑ i, y i := Finset.sum_le_sum fun i _ ↦ (hy i).1
  · calc ∑ i, y i ≤ ∑ _i : Fin n, (R : ℤ) := Finset.sum_le_sum fun i _ ↦ (hy i).2
      _ = (n : ℤ) * R := by simp

theorem card_Icc_sumRange (n R : ℕ) :
    (Finset.Icc (-((n : ℤ) * R)) ((n : ℤ) * R)).card = 2 * n * R + 1 := by
  rw [Int.card_Icc, show (n : ℤ) * R + 1 - -((n : ℤ) * R) = ((2 * n * R + 1 : ℕ) : ℤ) by
    push_cast; ring, Int.toNat_natCast]

/-- The sum-fiber `F_s = {u ∈ [-R,R]^m : ∑ u = s}`. -/
def fiber (m R : ℕ) (s : ℤ) : Finset (Fin m → ℤ) :=
  (box m R).filter fun u ↦ ∑ i, u i = s

/-- Pigeonhole: some sum-fiber of `[-R,R]^m` has at least `(2R+1)^m / (2mR+1)` elements. -/
theorem exists_large_fiber (m R : ℕ) :
    ∃ s : ℤ, (2 * R + 1 : ℝ) ^ m / (2 * m * R + 1) ≤ ((fiber m R s).card : ℝ) := by
  have hne : (Finset.Icc (-((m : ℤ) * R)) ((m : ℤ) * R)).Nonempty :=
    ⟨0, by rw [Finset.mem_Icc]; constructor <;> nlinarith [Int.natCast_nonneg m,
      Int.natCast_nonneg R, mul_nonneg (Int.natCast_nonneg m) (Int.natCast_nonneg R)]⟩
  have hden : (0 : ℝ) < 2 * m * R + 1 := by positivity
  obtain ⟨s, -, hs⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := box m R) (t := Finset.Icc (-((m : ℤ) * R)) ((m : ℤ) * R))
    (f := fun u ↦ ∑ i, u i) (b := (2 * R + 1 : ℝ) ^ m / (2 * m * R + 1))
    (fun u hu ↦ sum_mem_Icc_of_mem_box hu) hne
    (by
      rw [card_Icc_sumRange, card_box, nsmul_eq_mul]
      push_cast
      rw [mul_div_cancel₀ _ hden.ne'])
  exact ⟨s, hs⟩

/-! ### Gluing two fiber vectors into a zero-sum vector -/

variable {m ε n : ℕ}

/-- The vector `(u, -v, 0, …, 0)` of length `n = m + m + ε`. -/
def glue (h : m + m + ε = n) (u v : Fin m → ℤ) : Fin n → ℤ :=
  Fin.append (Fin.append u (-v)) (0 : Fin ε → ℤ) ∘ (finCongr h).symm

theorem glue_apply (h : m + m + ε = n) (u v : Fin m → ℤ) (k : Fin (m + m + ε)) :
    glue h u v (Fin.cast h k) = Fin.append (Fin.append u (-v)) (0 : Fin ε → ℤ) k := by
  simp [glue]

theorem glue_finCongr (h : m + m + ε = n) (u v : Fin m → ℤ) (k : Fin (m + m + ε)) :
    glue h u v (finCongr h k) = Fin.append (Fin.append u (-v)) (0 : Fin ε → ℤ) k :=
  glue_apply h u v k

theorem sum_glue (h : m + m + ε = n) (u v : Fin m → ℤ) :
    ∑ j, glue h u v j = ∑ i, u i - ∑ i, v i := by
  rw [← Fintype.sum_equiv (finCongr h) (fun k ↦ Fin.append (Fin.append u (-v)) (0 : Fin ε → ℤ) k)
    (glue h u v) (fun k ↦ (glue_finCongr h u v k).symm)]
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Pi.neg_apply, Pi.zero_apply,
    Finset.sum_const_zero, add_zero, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem glue_injective (h : m + m + ε = n) :
    Function.Injective fun uv : (Fin m → ℤ) × (Fin m → ℤ) ↦ glue h uv.1 uv.2 := by
  rintro ⟨u, v⟩ ⟨u', v'⟩ heq
  simp only at heq
  have hu : u = u' := by
    funext i
    have := congrFun heq (finCongr h (Fin.castAdd ε (Fin.castAdd m i)))
    rwa [glue_finCongr, glue_finCongr, Fin.append_left, Fin.append_left, Fin.append_left,
      Fin.append_left] at this
  have hv : v = v' := by
    funext i
    have := congrFun heq (finCongr h (Fin.castAdd ε (Fin.natAdd m i)))
    rw [glue_finCongr, glue_finCongr, Fin.append_left, Fin.append_left, Fin.append_right,
      Fin.append_right] at this
    simpa only [Pi.neg_apply, neg_inj] using this
  rw [hu, hv]

theorem glue_mem_box (h : m + m + ε = n) {R : ℕ} {u v : Fin m → ℤ} (hu : u ∈ box m R)
    (hv : v ∈ box m R) : glue h u v ∈ box n R := by
  rw [mem_box] at hu hv ⊢
  intro j
  obtain ⟨k, rfl⟩ := (finCongr h).surjective j
  rw [glue_finCongr]
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) k
  · rw [Fin.append_left]
    refine Fin.addCases (fun i' ↦ ?_) (fun i' ↦ ?_) i
    · rw [Fin.append_left]
      exact hu i'
    · rw [Fin.append_right, Pi.neg_apply]
      have := hv i'
      constructor <;> linarith
  · rw [Fin.append_right, Pi.zero_apply]
    constructor <;> simp

/-- The core counting bound: `((2R+1)^{n/2} / (2 (n/2) R + 1))² ≤ |Z(n,R)|`. -/
theorem card_boxZeroSum_ge (n R : ℕ) :
    ((2 * R + 1 : ℝ) ^ (n / 2) / (2 * ((n / 2 : ℕ) : ℝ) * R + 1)) ^ 2 ≤
      ((boxZeroSum n R).card : ℝ) := by
  set m := n / 2 with hm
  have h : m + m + (n - 2 * m) = n := by omega
  obtain ⟨s, hs⟩ := exists_large_fiber m R
  have himage : ((fiber m R s) ×ˢ (fiber m R s)).image (fun uv ↦ glue h uv.1 uv.2) ⊆
      boxZeroSum n R := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨⟨u, v⟩, huv, rfl⟩ := hy
    rw [Finset.mem_product] at huv
    obtain ⟨hu, hv⟩ := huv
    simp only [fiber, Finset.mem_filter] at hu hv
    rw [boxZeroSum, Finset.mem_filter]
    exact ⟨glue_mem_box h hu.1 hv.1, by rw [sum_glue, hu.2, hv.2, sub_self]⟩
  have hcard : (fiber m R s).card ^ 2 ≤ (boxZeroSum n R).card := by
    calc (fiber m R s).card ^ 2 = ((fiber m R s) ×ˢ (fiber m R s)).card := by
          rw [Finset.card_product, sq]
      _ = (((fiber m R s) ×ˢ (fiber m R s)).image (fun uv ↦ glue h uv.1 uv.2)).card :=
          (Finset.card_image_of_injective _ (glue_injective h)).symm
      _ ≤ _ := Finset.card_le_card himage
  calc ((2 * R + 1 : ℝ) ^ m / (2 * (m : ℝ) * R + 1)) ^ 2 ≤ ((fiber m R s).card : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hs 2
    _ ≤ ((boxZeroSum n R).card : ℝ) := by exact_mod_cast hcard

/-- For a nonnegative real radius, the counted set is the zero-sum box at the floor radius. -/
theorem zeroSumVectors_eq_boxZeroSum (n : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    zeroSumVectors n ρ = boxZeroSum n ⌊ρ⌋₊ := by
  ext y
  rw [mem_zeroSumVectors, boxZeroSum, Finset.mem_filter, mem_box]
  constructor
  · rintro ⟨hbound, hsum⟩
    refine ⟨fun i ↦ ?_, hsum⟩
    have hnat : (y i).natAbs ≤ ⌊ρ⌋₊ := by
      rw [Nat.le_floor_iff hρ, Nat.cast_natAbs, Int.cast_abs]
      exact hbound i
    omega
  · rintro ⟨hbox, hsum⟩
    refine ⟨fun i ↦ ?_, hsum⟩
    have hnat : (y i).natAbs ≤ ⌊ρ⌋₊ := by
      have := hbox i
      omega
    have h1 : ((y i).natAbs : ℝ) ≤ ρ := (Nat.le_floor_iff hρ).mp hnat
    rwa [Nat.cast_natAbs, Int.cast_abs] at h1

end MajorityDynamics.Combinatorics.ZeroSumCounting
