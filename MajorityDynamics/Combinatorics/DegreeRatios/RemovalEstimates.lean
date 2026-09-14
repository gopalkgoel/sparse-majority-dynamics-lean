import MajorityDynamics.Combinatorics.DegreeRatios.FiniteProducts
import MajorityDynamics.Combinatorics.DegreeRatios.WindowBounds

noncomputable section

namespace MajorityDynamics.Combinatorics.DegreeRatios

def removalRatio (N m h d : ℕ) : ℝ :=
  (N.choose m : ℝ) / ((N - h).choose (m - d) : ℝ)

theorem removalRatio_pos {N m h d : ℕ}
    (hm : m ≤ N) (hdm : d ≤ m) (hdh : d ≤ h) (hh : h ≤ N)
    (hr : h - d ≤ N - m) : 0 < removalRatio N m h d := by
  have hres : m - d ≤ N - h := by omega
  exact div_pos (by exact_mod_cast Nat.choose_pos hm)
    (by exact_mod_cast Nat.choose_pos hres)

theorem removalRatio_error {T n p : ℝ} {N m h d : ℕ}
    (b : RemovalBounds T n p N m h d) :
    |Real.log (removalRatio N m h d) - removalMain N m h d| ≤ 28 * T := by
  have hm : 0 < m := by exact_mod_cast b.count_pos
  have hmN : m < N := by exact_mod_cast b.count_lt
  have hdh : d ≤ h := by exact_mod_cast b.degree_le
  have hh : 2 * h ≤ N := by exact_mod_cast b.capacity_room
  have hd : 2 * d ≤ m := by exact_mod_cast b.count_room
  have hr : 2 * (h - d) ≤ N - m := by
    have he := b.complement_room
    exact_mod_cast (show 2 * ((h - d : ℕ) : ℝ) ≤ (N - m : ℕ) by
      simpa only [Nat.cast_sub hdh, Nat.cast_sub hmN.le] using he)
  have he := log_choose_removal_error hm hmN hdh hh hd hr
  change |Real.log (removalRatio N m h d) - removalMain N m h d| ≤ _ at he
  apply he.trans
  have h1 := b.capacity_error
  have h2 := b.count_error
  have h3 := b.complement_error
  rw [Nat.cast_sub hdh, Nat.cast_sub hmN.le]
  simp only [mul_div_assoc]
  linarith

theorem removalRatio_double_error {T n p : ℝ} {N m h d : ℕ}
    (b : RemovalBounds T n p N m h d) :
    |Real.log (removalRatio (2 * N) (2 * m) (2 * h) (2 * d)) -
      2 * removalMain N m h d| ≤ 56 * T := by
  have hm : 0 < m := by exact_mod_cast b.count_pos
  have hmN : m < N := by exact_mod_cast b.count_lt
  have hdh : d ≤ h := by exact_mod_cast b.degree_le
  have hh : 2 * h ≤ N := by exact_mod_cast b.capacity_room
  have hd : 2 * d ≤ m := by exact_mod_cast b.count_room
  have hr : 2 * (h - d) ≤ N - m := by
    have he := b.complement_room
    exact_mod_cast (show 2 * ((h - d : ℕ) : ℝ) ≤ (N - m : ℕ) by
      simpa only [Nat.cast_sub hdh, Nat.cast_sub hmN.le] using he)
  have he := log_choose_removal_error
    (by omega : 0 < 2 * m) (by omega : 2 * m < 2 * N) (by omega : 2 * d ≤ 2 * h)
    (by omega : 2 * (2 * h) ≤ 2 * N) (by omega : 2 * (2 * d) ≤ 2 * m)
    (by omega : 2 * (2 * h - 2 * d) ≤ 2 * N - 2 * m)
  rw [removalMain_double hm hmN] at he
  change |Real.log (removalRatio (2 * N) (2 * m) (2 * h) (2 * d)) -
    2 * removalMain N m h d| ≤ _ at he
  apply he.trans
  have h1 := b.capacity_error
  have h2 := b.count_error
  have h3 := b.complement_error
  have hN : (N : ℝ) ≠ 0 := ne_of_gt b.capacity_pos
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt b.count_pos
  have hr0 : (N : ℝ) - m ≠ 0 := ne_of_gt (sub_pos.mpr b.count_lt)
  have htwoR : 2 * (N : ℝ) - 2 * m ≠ 0 := by nlinarith [b.count_lt]
  rw [Nat.cast_sub (by omega : 2 * d ≤ 2 * h), Nat.cast_sub (by omega : 2 * m ≤ 2 * N)]
  push_cast
  have hid : 2 * (2 * (h : ℝ)) ^ 2 / (2 * N) +
      2 * (2 * (d : ℝ)) ^ 2 / (2 * m) +
      2 * (2 * (h : ℝ) - 2 * d) ^ 2 / (2 * (N : ℝ) - 2 * m) =
      4 * ((h : ℝ) ^ 2 / N + (d : ℝ) ^ 2 / m +
        ((h : ℝ) - d) ^ 2 / ((N : ℝ) - m)) := by
    field_simp
    ring
  rw [hid]
  linarith

theorem removalMain_error {T n p : ℝ} {N m h d : ℕ}
    (b : RemovalBounds T n p N m h d) :
    |removalMain N m h d + (d : ℝ) * Real.log p - p * n| ≤
      (relativeConstant T + 4 * relativeConstant T ^ 2 + 10) * Real.log n := by
  have hm : 0 < m := by exact_mod_cast b.count_pos
  have hmN : m < N := by exact_mod_cast b.count_lt
  simpa only [removalMain_density hm hmN] using b.density_error

theorem removal_estimate {T n p : ℝ} {N m h d : ℕ}
    (hT : 0 ≤ T) (hlog : 1 ≤ Real.log n)
    (b : RemovalBounds T n p N m h d) :
    |Real.log (removalRatio N m h d) + (d : ℝ) * Real.log p - p * n| ≤
      errorConstant T * Real.log n := by
  have h1 := removalRatio_error b
  have h2 := removalMain_error b
  have hid : Real.log (removalRatio N m h d) + (d : ℝ) * Real.log p - p * n =
      (Real.log (removalRatio N m h d) - removalMain N m h d) +
      (removalMain N m h d + (d : ℝ) * Real.log p - p * n) := by ring
  rw [hid]
  apply ((abs_add_le _ _).trans (add_le_add h1 h2)).trans
  have hh := mul_le_mul_of_nonneg_left hlog hT
  dsimp [errorConstant]
  nlinarith

theorem graph_removal_estimate {T n p : ℝ} {N m h d : ℕ}
    (hT : 0 ≤ T) (hlog : 1 ≤ Real.log n)
    (b : RemovalBounds T n p N m h d) :
    |(Real.log (removalRatio (2 * N) (2 * m) (2 * h) (2 * d)) -
        Real.log (removalRatio N m h d)) + (d : ℝ) * Real.log p - p * n| ≤
      errorConstant T * Real.log n := by
  have h1 := removalRatio_error b
  have h2 := removalRatio_double_error b
  have h3 := removalMain_error b
  have hid : (Real.log (removalRatio (2 * N) (2 * m) (2 * h) (2 * d)) -
      Real.log (removalRatio N m h d)) + (d : ℝ) * Real.log p - p * n =
      (Real.log (removalRatio (2 * N) (2 * m) (2 * h) (2 * d)) - 2 * removalMain N m h d) -
      (Real.log (removalRatio N m h d) - removalMain N m h d) +
      (removalMain N m h d + (d : ℝ) * Real.log p - p * n) := by ring
  rw [hid]
  apply ((abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add h2 h1)) h3)).trans
  have hh := mul_le_mul_of_nonneg_left hlog hT
  dsimp [errorConstant]
  nlinarith

end MajorityDynamics.Combinatorics.DegreeRatios
