import MajorityDynamics.Combinatorics.DegreeRatios.RemovalEstimates
import Mathlib.Algebra.Group.Nat.Even

noncomputable section

namespace MajorityDynamics.Combinatorics.DegreeRatios

theorem edgeCapacity_double (n : ℕ) : 2 * edgeCapacity n = n * (n - 1) := by
  exact Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd

theorem edgeCapacity_cast {n : ℕ} (hn : 1 ≤ n) :
    (edgeCapacity n : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  have hh : (2 : ℝ) * edgeCapacity n = (n : ℝ) * (n - 1 : ℕ) := by
    exact_mod_cast edgeCapacity_double n
  rw [Nat.cast_sub hn, Nat.cast_one] at hh
  linarith

theorem edgeCapacity_pred {n : ℕ} (hn : 3 ≤ n) :
    edgeCapacity (n - 1) = edgeCapacity n - (n - 1) := by
  have h1 := edgeCapacity_cast (n := n) (by omega)
  have h2 := edgeCapacity_cast (n := n - 1) (by omega)
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at h2
  have hh : (edgeCapacity (n - 1) : ℝ) + (n - 1 : ℕ) = edgeCapacity n := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    nlinarith
  have hh' : edgeCapacity (n - 1) + (n - 1) = edgeCapacity n := by exact_mod_cast hh
  omega

theorem int_toNat_cast {z : ℤ} (hz : 0 ≤ z) : (z.toNat : ℝ) = z := by
  exact_mod_cast Int.toNat_of_nonneg hz

structure NaturalDomain (N m h d : ℕ) : Prop where
  count_le : m ≤ N
  removed_le : h ≤ N
  degree_count_le : d ≤ m
  degree_removed_le : d ≤ h
  residual_le : m - d ≤ N - h
  complement_le : h - d ≤ N - m

theorem natural_domain {T n p : ℝ} {N m h d : ℕ}
    (b : RemovalBounds T n p N m h d) : NaturalDomain N m h d := by
  have hm : m < N := by exact_mod_cast b.count_lt
  have hh : 2 * h ≤ N := by exact_mod_cast b.capacity_room
  have hd : 2 * d ≤ m := by exact_mod_cast b.count_room
  have hdh : d ≤ h := by exact_mod_cast b.degree_le
  have hr : 2 * (h - d) ≤ N - m := by
    have he := b.complement_room
    exact_mod_cast (show 2 * ((h - d : ℕ) : ℝ) ≤ (N - m : ℕ) by
      simpa only [Nat.cast_sub hdh, Nat.cast_sub hm.le] using he)
  constructor <;> omega

theorem NaturalDomain.double {N m h d : ℕ} (b : NaturalDomain N m h d) :
    NaturalDomain (2 * N) (2 * m) (2 * h) (2 * d) := by
  rcases b with ⟨hm, hh, hdm, hdh, hr, hc⟩
  constructor <;> omega

theorem NaturalDomain.ratio_pos {N m h d : ℕ} (b : NaturalDomain N m h d) :
    0 < removalRatio N m h d :=
  removalRatio_pos b.count_le b.degree_count_le b.degree_removed_le b.removed_le b.complement_le

theorem graphRatio_bridge {n : ℕ} {m d : ℤ} (hn : 3 ≤ n) (hm : 0 ≤ m) (hd : 0 ≤ d) :
    graphRatio n m d =
      removalRatio (2 * edgeCapacity n) (2 * m.toNat) (2 * (n - 1)) (2 * d.toNat) /
        removalRatio (edgeCapacity n) m.toNat (n - 1) d.toNat := by
  have hsub : (m - d).toNat = m.toNat - d.toNat := Int.toNat_sub'' hm hd
  have htwo : (2 * m).toNat = 2 * m.toNat := by omega
  have htwosub : (2 * m - 2 * d).toNat = 2 * m.toNat - 2 * d.toNat := by omega
  have hpred : (n - 1) * (n - 2) = 2 * (edgeCapacity n - (n - 1)) := by
    rw [← edgeCapacity_pred hn, edgeCapacity_double]
    congr 1
  have hcap : n * (n - 1) = 2 * edgeCapacity n := (edgeCapacity_double n).symm
  have hnat : 2 * edgeCapacity n - 2 * (n - 1) = 2 * (edgeCapacity n - (n - 1)) := by omega
  dsimp [graphRatio, removalRatio]
  rw [hsub, htwo, htwosub, edgeCapacity_pred hn, hpred, hcap, hnat]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

end MajorityDynamics.Combinatorics.DegreeRatios
