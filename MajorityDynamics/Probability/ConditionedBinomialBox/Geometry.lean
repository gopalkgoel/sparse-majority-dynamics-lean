import MajorityDynamics.Binomial.ApproximationStatements
import MajorityDynamics.Probability.ConditionedBinomialBox.GeometryScalar
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Classical
namespace MajorityDynamics.Probability.ConditionedBinomialBox.Geometry

variable {r d : ℕ}

def box (a : Fin d → ℕ) (L : ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset fun i => Finset.Ico (a i) (a i + L)

@[simp] theorem mem_box (a : Fin d → ℕ) (L : ℕ) (x : Fin d → ℕ) :
    x ∈ box a L ↔ ∀ i, a i ≤ x i ∧ x i < a i + L := by
  simp [box, Fintype.mem_piFinset]

@[simp] theorem card_box (a : Fin d → ℕ) (L : ℕ) :
    (box a L).card = L ^ d := by
  simp [box, Fintype.card_piFinset]

theorem box_nonempty (a : Fin d → ℕ) {L : ℕ} (hL : 1 ≤ L) :
    (box a L).Nonempty := by
  refine ⟨a, (mem_box a L a).2 ?_⟩
  intro i
  constructor <;> omega

def matrixBound (M : Fin r → Fin d → ℤ) : ℝ :=
  1 + ∑ j, ∑ i, |(M j i : ℝ)|

def driftBound (M : Fin r → Fin d → ℤ) (T : ℝ) : ℝ :=
  (T + 2) * matrixBound M

def width (M : Fin r → Fin d → ℤ) : ℝ := 1 / (4 * matrixBound M)

def window (M : Fin r → Fin d → ℤ) (T : ℝ) : ℝ :=
  2 * T * (driftBound M T + T ^ 2 + 2)

theorem matrixBound_one (M : Fin r → Fin d → ℤ) : 1 ≤ matrixBound M := by
  unfold matrixBound
  have : 0 ≤ ∑ j, ∑ i, |(M j i : ℝ)| := by positivity
  linarith

theorem width_pos (M : Fin r → Fin d → ℤ) : 0 < width M := by
  have := matrixBound_one M
  unfold width
  positivity

theorem width_le_one (M : Fin r → Fin d → ℤ) : width M ≤ 1 := by
  have := matrixBound_one M
  unfold width
  rw [div_le_iff₀ (by positivity)]
  linarith

theorem driftBound_pos (M : Fin r → Fin d → ℤ) {T : ℝ} (hT : 1 < T) :
    0 < driftBound M T := by
  have := matrixBound_one M
  unfold driftBound
  positivity

theorem window_pos (M : Fin r → Fin d → ℤ) {T : ℝ} (hT : 1 < T) :
    0 < window M T := by
  have := driftBound_pos M hT
  unfold window
  positivity

theorem row_abs_le (M : Fin r → Fin d → ℤ) (j : Fin r) :
    ∑ i, |(M j i : ℝ)| ≤ matrixBound M := by
  have h := Finset.single_le_sum (f := fun k => ∑ i : Fin d, |(M k i : ℝ)|)
    (fun k (_ : k ∈ Finset.univ) =>
    Finset.sum_nonneg (fun i _ => abs_nonneg (M k i : ℝ))) (Finset.mem_univ j)
  unfold matrixBound
  linarith

theorem column_abs_le (M : Fin r → Fin d → ℤ) (i : Fin d) :
    |∑ j, (M j i : ℝ)| ≤ matrixBound M := by
  calc
    |∑ j, (M j i : ℝ)| ≤ ∑ j, |(M j i : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ∑ k, |(M j k : ℝ)| := Finset.sum_le_sum fun j _ =>
      Finset.single_le_sum (fun k _ => abs_nonneg (M j k : ℝ)) (Finset.mem_univ i)
    _ ≤ matrixBound M := by unfold matrixBound; linarith

theorem row_square_one (M : Fin r → Fin d → ℤ)
    (hM : Binomial.Approximation.OrthogonalRows M) (j : Fin r) :
    1 ≤ ∑ i, (M j i : ℝ)^2 := by
  obtain ⟨i, hi⟩ := hM.1 j
  have hi2 : (1 : ℤ) ≤ (M j i)^2 := by
    have : 0 < (M j i)^2 := sq_pos_of_ne_zero hi
    omega
  have hreal : (1 : ℝ) ≤ (M j i : ℝ)^2 := by exact_mod_cast hi2
  exact hreal.trans (Finset.single_le_sum (fun k _ => sq_nonneg (M j k : ℝ))
    (Finset.mem_univ i))

theorem row_drift (M : Fin r → Fin d → ℤ)
    (hM : Binomial.Approximation.OrthogonalRows M) (j : Fin r) :
    ∑ i, (M j i : ℝ) * (∑ k, (M k i : ℝ)) = ∑ i, (M j i : ℝ)^2 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single j]
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · intro k _ hkj
    have h := hM.2 j k (Ne.symm hkj)
    exact_mod_cast h
  · simp

def center (M : Fin r → Fin d → ℤ) (T p s : ℝ) (η : Fin d → ℕ)
    (i : Fin d) : ℝ := p * η i + s * (T + 2) * ∑ j, (M j i : ℝ)

def starts (M : Fin r → Fin d → ℤ) (T p s : ℝ) (η : Fin d → ℕ) : Fin d → ℕ :=
  fun i => ⌈center M T p s η i⌉₊

def length (M : Fin r → Fin d → ℤ) (s : ℝ) : ℕ := ⌊width M * s⌋₊

theorem center_deviation (M : Fin r → Fin d → ℤ) {T p s : ℝ}
    (hT : 1 < T) (hs : 0 ≤ s) (η : Fin d → ℕ) (i : Fin d) :
    |center M T p s η i - p * η i| ≤ driftBound M T * s := by
  simp only [center, add_sub_cancel_left, abs_mul, abs_of_nonneg hs,
    abs_of_pos (show 0 < T + 2 by linarith)]
  calc
    s * (T + 2) * |∑ j, (M j i : ℝ)| ≤ s * (T + 2) * matrixBound M := by
      gcongr
      exact column_abs_le M i
    _ = driftBound M T * s := by unfold driftBound; ring

theorem width_bounds (M : Fin r → Fin d → ℤ) {s : ℝ}
    (hs : 8 * matrixBound M ≤ s) :
    1 ≤ length M s ∧ width M / 2 * s ≤ (length M s : ℝ) ∧
      (length M s : ℝ) ≤ width M * s := by
  have hB : 0 < matrixBound M := lt_of_lt_of_le zero_lt_one (matrixBound_one M)
  have hw : 0 < width M := by unfold width; positivity
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity : 0 < 8 * matrixBound M) hs
  have hws : 2 ≤ width M * s := by
    unfold width
    rw [one_div_mul_eq_div, le_div_iff₀ (by positivity)]
    linarith
  have hlo := Nat.lt_floor_add_one (width M * s)
  have hhi := Nat.floor_le (show 0 ≤ width M * s by positivity)
  refine ⟨?_, ?_, hhi⟩
  · have : (1 : ℝ) ≤ (length M s : ℝ) := by unfold length; linarith
    exact_mod_cast this
  · unfold length
    nlinarith

theorem rounded_bounds (M : Fin r → Fin d → ℤ) {T p s : ℝ} (η : Fin d → ℕ)
    (hc : ∀ i, 0 ≤ center M T p s η i) {x : Fin d → ℕ}
    (hx : x ∈ box (starts M T p s η) (length M s)) (i : Fin d) :
    0 ≤ (x i : ℝ) - center M T p s η i ∧
    (x i : ℝ) - center M T p s η i ≤ 1 + (length M s : ℝ) := by
  have hmem := (mem_box _ _ _).1 hx i
  have hlo : (starts M T p s η i : ℝ) ≤ (x i : ℝ) := by exact_mod_cast hmem.1
  have hhi : (x i : ℝ) < (starts M T p s η i : ℝ) + length M s := by
    exact_mod_cast hmem.2
  have hceil := Nat.le_ceil (center M T p s η i)
  have hceil' := Nat.ceil_lt_add_one (hc i)
  change center M T p s η i ≤ (starts M T p s η i : ℝ) at hceil
  change (starts M T p s η i : ℝ) < center M T p s η i + 1 at hceil'
  constructor <;> linarith

theorem rounding_row_error (M : Fin r → Fin d → ℤ) {T p s : ℝ}
    (η : Fin d → ℕ) (hs : 8 * matrixBound M ≤ s)
    (hc : ∀ i, 0 ≤ center M T p s η i) {x : Fin d → ℕ}
    (hx : x ∈ box (starts M T p s η) (length M s)) (j : Fin r) :
    |∑ i, (M j i : ℝ) * ((x i : ℝ) - center M T p s η i)| ≤ s := by
  have hB : 0 < matrixBound M := lt_of_lt_of_le zero_lt_one (matrixBound_one M)
  have hL := (width_bounds M hs).2.2
  have hBL : matrixBound M * (length M s : ℝ) ≤ s / 4 := by
    unfold width at hL
    rw [one_div_mul_eq_div, le_div_iff₀ (by positivity)] at hL
    nlinarith
  calc
    _ ≤ ∑ i, |(M j i : ℝ) * ((x i : ℝ) - center M T p s η i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |(M j i : ℝ)| * (1 + (length M s : ℝ)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (rounded_bounds M η hc hx i).1]
      gcongr
      exact (rounded_bounds M η hc hx i).2
    _ = (∑ i, |(M j i : ℝ)|) * (1 + (length M s : ℝ)) :=
      (Finset.sum_mul ..).symm
    _ ≤ matrixBound M * (1 + (length M s : ℝ)) := by
      gcongr
      exact row_abs_le M j
    _ ≤ s := by nlinarith

theorem box_slack (M : Fin r → Fin d → ℤ)
    (hM : Binomial.Approximation.OrthogonalRows M) {T p s N : ℝ}
    (hT : 1 < T) (hp : 0 < p) (hs : 8 * matrixBound M ≤ s)
    (hsq : s ^ 2 = p * N) (η : Fin d → ℕ)
    (hbal : ∀ j, |∑ i, (M j i : ℝ) * η i| ≤ T * N / s)
    (hc : ∀ i, 0 ≤ center M T p s η i) {x : Fin d → ℕ}
    (hx : x ∈ box (starts M T p s η) (length M s)) (j : Fin r) :
    0 < ∑ i, (M j i : ℝ) * (x i : ℝ) := by
  have hB := matrixBound_one M
  have hspos : 0 < s := by linarith
  have hbal' := (le_div_iff₀ hspos).1 (hbal j)
  have hmul := mul_le_mul_of_nonneg_left hbal' hp.le
  have hbase : |p * ∑ i, (M j i : ℝ) * η i| ≤ T * s := by
    rw [abs_mul, abs_of_pos hp]
    nlinarith
  have hrow : ∑ i, (M j i : ℝ) * center M T p s η i =
      p * (∑ i, (M j i : ℝ) * η i) +
        s * (T + 2) * ∑ i, (M j i : ℝ)^2 := by
    simp only [center]
    simp_rw [mul_add (M j _ : ℝ)]
    rw [Finset.sum_add_distrib]
    have h1 : ∑ i, (M j i : ℝ) * (p * η i) = p * ∑ i, (M j i : ℝ) * η i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have h2 : ∑ i, (M j i : ℝ) * (s * (T + 2) * ∑ k, (M k i : ℝ)) =
        s * (T + 2) * ∑ i, (M j i : ℝ) * ∑ k, (M k i : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h1, h2, row_drift M hM j]
  have herror := rounding_row_error M η hs hc hx j
  have hsplit : (∑ i, (M j i : ℝ) * (x i : ℝ)) =
      (∑ i, (M j i : ℝ) * center M T p s η i) +
        ∑ i, (M j i : ℝ) * ((x i : ℝ) - center M T p s η i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsq1 := row_square_one M hM j
  have hmult := mul_le_mul_of_nonneg_left hsq1
    (show 0 ≤ s * (T + 2) by positivity)
  rw [hsplit, hrow]
  have hb := (abs_le.mp hbase).1
  have he := (abs_le.mp herror).1
  nlinarith

theorem event_of_slack (M : Fin r → Fin d → ℤ) (strict : Fin r → Bool)
    (x : Fin d → ℕ) (h : ∀ j, 0 < ∑ i, (M j i : ℝ) * (x i : ℝ)) :
    x ∈ Binomial.inequalityEvent (fun j i => (M j i : ℝ)) strict := by
  intro j
  split_ifs
  · exact h j
  · exact (h j).le

/-- The actual consecutive-coordinate box lies strictly inside all constraints
and uniformly inside a central binomial window. No geometric hypothesis is
hidden: the only finite-regime inputs are scalar largeness and the original
size, tilt, and balance inequalities. -/
theorem construct (M : Fin r → Fin d → ℤ)
    (hM : Binomial.Approximation.OrthogonalRows M) {T p s N : ℝ}
    (hT : 1 < T) (hp : 0 < p)
    (hs : 8 * matrixBound M ≤ s)
    (hslarge : 2 * T * (driftBound M T + 2) ≤ s)
    (hpsmall : p ≤ 1 / (4 * T ^ 2)) (hsq : s ^ 2 = p * N)
    (η : Fin d → ℕ) (q : Fin d → Binomial.Probability)
    (hsize : ∀ i, N / T ≤ (η i : ℝ) ∧ (η i : ℝ) ≤ T * N)
    (htilt : ∀ i, |(q i : ℝ) - p| ≤ T * p / s)
    (hqlo : ∀ i, p / 2 ≤ (q i : ℝ))
    (hbal : ∀ j, |∑ i, (M j i : ℝ) * η i| ≤ T * N / s) :
    1 ≤ length M s ∧
    width M / 2 * s ≤ (length M s : ℝ) ∧
    (length M s : ℝ) ≤ width M * s ∧
    ∀ x ∈ box (starts M T p s η) (length M s),
      (∀ i, x i ≤ η i) ∧
      (∀ j, 0 < ∑ i, (M j i : ℝ) * (x i : ℝ)) ∧
      (∀ i, |(x i : ℝ) - (η i : ℝ) * (q i : ℝ)| ≤
        window M T * Real.sqrt ((η i : ℝ) * (q i : ℝ))) := by
  have hB := matrixBound_one M
  have hspos : 0 < s := by linarith
  have hN : 0 < N := by nlinarith [sq_pos_of_pos hspos]
  have hscalar := fun i => GeometryScalar.coordinate_bounds hT (driftBound_pos M hT).le
    hp hN hspos hsq hslarge hpsmall (hsize i).1 (hsize i).2
    (center_deviation M hT hspos.le η i) (htilt i) (hqlo i)
  have hc : ∀ i, 0 ≤ center M T p s η i := fun i => (hscalar i).1.le
  obtain ⟨hLpos, hLlo, hLhi⟩ := width_bounds M hs
  refine ⟨hLpos, hLlo, hLhi, ?_⟩
  intro x hx
  have hLsmall : (length M s : ℝ) ≤ s :=
    hLhi.trans (by nlinarith [mul_le_mul_of_nonneg_right (width_le_one M) hspos.le])
  have hpoint : ∀ i, center M T p s η i ≤ (x i : ℝ) ∧
      (x i : ℝ) ≤ center M T p s η i + 1 + s := by
    intro i
    have hh := rounded_bounds M η hc hx i
    constructor <;> linarith
  refine ⟨?_, box_slack M hM hT hp hs hsq η hbal hc hx, ?_⟩
  · intro i
    have hh := (hpoint i).2.trans (hscalar i).2.1
    exact_mod_cast hh
  · intro i
    exact (hscalar i).2.2 (x i : ℝ) (hpoint i).1 (hpoint i).2

end MajorityDynamics.Probability.ConditionedBinomialBox.Geometry
