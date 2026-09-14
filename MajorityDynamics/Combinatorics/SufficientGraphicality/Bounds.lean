import MajorityDynamics.Combinatorics.SufficientGraphicality.Basic

/-! The numerical arguments of A.8/A.9, without sorting or external criteria.
Multiplication replaces division, so zero degrees cause no domain issue. -/
namespace MajorityDynamics.Combinatorics.SufficientGraphicality
open Finset

lemma sum_le_card_mul {n : ℕ} (d : Fin n → ℕ) (s : Finset (Fin n)) :
    ∑ i ∈ s, d i ≤ s.card * maxDegree d := by
  simpa using sum_le_sum (s := s) (fun i _ => le_maxDegree d i)

lemma mul_le_max_mul_min {r D x : ℕ} (hr : r ≤ D) (hx : x ≤ D) :
    r * x ≤ D * min r x := by
  rcases le_total r x with h | h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h]; exact Nat.mul_le_mul_right x hr

/-- Erdős–Gallai's inequality holds for every subset, hence in particular each prefix. -/
theorem graphical_subset_bound {n : ℕ} (d : Fin n → ℕ)
    (h : maxDegree d * (maxDegree d + 1) ≤ total d) (s : Finset (Fin n)) :
    ∑ i ∈ s, d i ≤ s.card * (s.card - 1) + ∑ i ∈ sᶜ, min s.card (d i) := by
  classical
  let D := maxDegree d
  let r := s.card
  have hP := sum_le_card_mul d s
  change (∑ i ∈ s, d i) ≤ r * D at hP
  by_cases hr0 : r = 0
  · have hs : s = ∅ := card_eq_zero.mp hr0
    simp [hs]
  by_cases hr : r ≤ D
  · have hD : 0 < D := by omega
    have hT : r * (∑ i ∈ sᶜ, d i) ≤ D * (∑ i ∈ sᶜ, min r (d i)) := by
      simp only [mul_sum]
      exact sum_le_sum fun i _ => mul_le_max_mul_min hr (le_maxDegree d i)
    have htotal : (∑ i ∈ s, d i) + (∑ i ∈ sᶜ, d i) = total d :=
      sum_add_sum_compl s d
    have h1 := Nat.mul_le_mul_left (D + r) hP
    have h2 := Nat.mul_le_mul_left r h
    have hrsub : r - 1 + 1 = r := by omega
    change (∑ i ∈ s, d i) ≤ r * (r - 1) + ∑ i ∈ sᶜ, min r (d i)
    have hsub := congrArg (fun x => D * r * x) hrsub
    have htotr := congrArg (fun x => r * x) htotal
    have hscaled : D * (∑ i ∈ s, d i) ≤
        D * (r * (r - 1) + ∑ i ∈ sᶜ, min r (d i)) := by
      dsimp [D] at *
      nlinarith only [h1, h2, hT, hsub, htotr]
    exact (mul_le_mul_iff_right₀ hD).mp hscaled
  · have hDr : D ≤ r - 1 := by omega
    have hlarge := Nat.mul_le_mul_left r hDr
    exact le_trans hP (le_trans hlarge (Nat.le_add_right _ _))

/-- Gale–Ryser's inequality holds for every left subset. -/
theorem bipartite_subset_bound {l n : ℕ} (a : Fin l → ℕ) (b : Fin n → ℕ)
    (heq : total a = total b) (h : maxDegree a * maxDegree b ≤ total a)
    (s : Finset (Fin l)) : ∑ i ∈ s, a i ≤ ∑ j, min s.card (b j) := by
  classical
  by_cases hr : maxDegree b ≤ s.card
  · have hb : ∀ j, min s.card (b j) = b j :=
      fun j => min_eq_right ((le_maxDegree b j).trans hr)
    simp only [hb]
    calc
      ∑ i ∈ s, a i ≤ total a := sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
      _ = total b := heq
  · have hD : 0 < maxDegree b := by omega
    have hmin : s.card * total b ≤ maxDegree b * ∑ j, min s.card (b j) := by
      simp only [total, mul_sum]
      exact sum_le_sum fun j _ => mul_le_max_mul_min (by omega) (le_maxDegree b j)
    have hP := Nat.mul_le_mul_left (maxDegree b) (sum_le_card_mul a s)
    have hM := Nat.mul_le_mul_left s.card h
    rw [heq] at hM
    nlinarith

end MajorityDynamics.Combinatorics.SufficientGraphicality
