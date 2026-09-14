import MajorityDynamics.Literature.LWFormal.Concentration

set_option autoImplicit true

/-!
# Second moment of `F(d) = ∑ᵢ (dᵢ - d̄)²` under `ℬ_m(n)`, and (6.8)

The mean and variance of `F` are computed exactly from the binomial moments of the
multivariate hypergeometric distribution (`sum_choose_inter_mul`); together with the
Lipschitz bound for `x ↦ exp((1 - x²)/4)` this gives `E_{ℬ_m} H̃ = 1 + O(n^{-1/2})`.
-/

namespace LW

open Finset Real

variable {n : ℕ}

/-- `(N)ⱼ · C(N-j, k-j) = C(N,k) · (k)ⱼ` for `j ≤ k ≤ N`. -/
theorem descFactorial_mul_choose (N k : ℕ) (hk : k ≤ N) :
    ∀ j ≤ k, N.descFactorial j * (N - j).choose (k - j) = N.choose k * k.descFactorial j := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have h := Nat.add_one_mul_choose_eq (N - j - 1) (k - j - 1)
    rw [show N - j - 1 + 1 = N - j by omega, show k - j - 1 + 1 = k - j by omega] at h
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, ← Nat.sub_sub, ← Nat.sub_sub]
    calc (N - j) * N.descFactorial j * (N - j - 1).choose (k - j - 1)
        = N.descFactorial j * ((N - j) * (N - j - 1).choose (k - j - 1)) := by ring
      _ = N.descFactorial j * (N - j).choose (k - j) * (k - j) := by rw [h]; ring
      _ = N.choose k * k.descFactorial j * (k - j) := by rw [ih (by omega)]
      _ = _ := by ring

theorem choose_div_choose (N k j : ℕ) (hk : k ≤ N) (hj : j ≤ k) :
    ((N - j).choose (k - j) : ℝ) / N.choose k =
      (k.descFactorial j : ℝ) / N.descFactorial j := by
  have h := descFactorial_mul_choose N k hk j hj
  have h1 : (0 : ℝ) < N.choose k := by exact_mod_cast Nat.choose_pos hk
  have h2 : (0 : ℝ) < N.descFactorial j := by
    exact_mod_cast Nat.descFactorial_pos.2 (hj.trans hk)
  rw [div_eq_div_iff h1.ne' h2.ne']
  exact_mod_cast (by rw [mul_comm, h, mul_comm] : (N - j).choose (k - j) * N.descFactorial j
    = k.descFactorial j * N.choose k)

theorem cast_descFactorial_of_le {x j : ℕ} (h : j ≤ x) :
    (x.descFactorial j : ℝ) = ∏ i ∈ range j, ((x : ℝ) - i) := by
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  exact prod_congr rfl fun i hi => Nat.cast_sub (by have := mem_range.1 hi; omega)

theorem cast_choose_three (d : ℕ) : (d.choose 3 : ℝ) = d * (d - 1) * (d - 2) / 6 := by
  rcases lt_or_ge d 3 with h | h
  · interval_cases d <;> norm_num [Nat.choose]
  · have := cast_descFactorial_of_le (x := d) (j := 3) h
    rw [Nat.descFactorial_eq_factorial_mul_choose] at this
    simp only [prod_range_succ, prod_range_zero, Nat.factorial, Nat.cast_mul] at this
    push_cast at this
    linarith

theorem cast_choose_four (d : ℕ) : (d.choose 4 : ℝ) = d * (d - 1) * (d - 2) * (d - 3) / 24 := by
  rcases lt_or_ge d 4 with h | h
  · interval_cases d <;> norm_num [Nat.choose]
  · have := cast_descFactorial_of_le (x := d) (j := 4) h
    rw [Nat.descFactorial_eq_factorial_mul_choose] at this
    simp only [prod_range_succ, prod_range_zero, Nat.factorial, Nat.cast_mul] at this
    push_cast at this
    linarith

theorem sq_eq_choose (d : ℕ) : ((d : ℝ)) ^ 2 = 2 * (d.choose 2 : ℝ) + d := by
  rw [Nat.cast_choose_two]; ring

theorem pow_four_eq_choose (d : ℕ) :
    ((d : ℝ)) ^ 4 = 24 * (d.choose 4 : ℝ) + 36 * d.choose 3 + 14 * d.choose 2 + d := by
  rw [cast_choose_four, cast_choose_three, Nat.cast_choose_two]; ring

theorem starP_disjoint {i j : Fin n} (h : i ≠ j) : Disjoint (starP n i) (starP n j) := by
  rw [disjoint_left]
  intro p hp hq
  simp only [starP, mem_filter] at hp hq
  exact h (hp.2.symm.trans hq.2)

theorem mem_Bm {m : ℕ} {S : Finset (Fin n × Fin n)} :
    S ∈ Bm n m ↔ S ⊆ allPairs n ∧ S.card = 2 * m := by
  rw [Bm, mem_powersetCard]

theorem sum_choose_pairDeg (n m : ℕ) (i : Fin n) (a : ℕ) (ha : a ≤ 2 * m) :
    ∑ S ∈ Bm n m, (pairDeg S i).choose a =
      (n - 1).choose a * (n * (n - 1) - a).choose (2 * m - a) := by
  have := sum_choose_inter_mul (allPairs n) (starP n i) ∅ (filter_subset _ _) (empty_subset _)
    (disjoint_empty_right _) a 0 (2 * m) (by omega)
  simp only [card_empty, Nat.choose_zero_right, mul_one, add_zero, card_starP, card_allPairs]
    at this
  rw [← this]
  exact sum_congr rfl fun S hS => by rw [pairDeg_eq_card_inter (mem_Bm.1 hS).1]

theorem sum_choose_pairDeg_mul (n m : ℕ) {i j : Fin n} (hij : i ≠ j) (a b : ℕ)
    (hab : a + b ≤ 2 * m) :
    ∑ S ∈ Bm n m, (pairDeg S i).choose a * (pairDeg S j).choose b =
      (n - 1).choose a * (n - 1).choose b *
        (n * (n - 1) - (a + b)).choose (2 * m - (a + b)) := by
  have := sum_choose_inter_mul (allPairs n) (starP n i) (starP n j) (filter_subset _ _)
    (filter_subset _ _) (starP_disjoint hij) a b (2 * m) hab
  simp only [card_starP, card_allPairs] at this
  rw [← this]
  exact sum_congr rfl fun S hS => by
    rw [pairDeg_eq_card_inter (mem_Bm.1 hS).1, pairDeg_eq_card_inter (mem_Bm.1 hS).1]

/-- `F(d) = ∑ᵢ (dᵢ - 2m/n)²`. -/
noncomputable def Fd (n m : ℕ) (d : Fin n → ℕ) : ℝ := ∑ i, ((d i : ℝ) - 2 * m / n) ^ 2

/-- `c = μ(1-μ)(n-1)² = k(N-k)/n²` where `N = n(n-1)`. -/
noncomputable def cF (x k : ℝ) : ℝ := k * (x * (x - 1) - k) / x ^ 2

/-- `E (F - c)²` under `ℬ_m` (exact). -/
noncomputable def varF (x k : ℝ) : ℝ :=
  2 * k * (k - 1) * (x - 1) ^ 2 * (x * (x - 1) - k) * (x * (x - 1) - k - 1) /
      ((x + 1) * (x * (x - 1) - 3) * (x * (x - 1) - 1) ^ 2) +
    k ^ 2 * (x * (x - 1) - k) ^ 2 / (x ^ 4 * (x * (x - 1) - 1) ^ 2)

theorem sum_Fd_sub_sq (n m : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m) (hmN : 2 * m ≤ n * (n - 1)) :
    ∑ S ∈ Bm n m, (Fd n m (pairDeg S) - cF n (2 * m)) ^ 2 = (Bm n m).card * varF n (2 * m) := by
  set x : ℝ := (n : ℝ) with hx
  set k : ℝ := 2 * (m : ℝ) with hk
  set T : ℝ := (((n * (n - 1)).choose (2 * m) : ℕ) : ℝ) with hT
  set A : ℕ → ℝ := fun a => (((n - 1).choose a : ℕ) : ℝ) with hA
  set Q : ℕ → ℝ := fun j => (((n * (n - 1) - j).choose (2 * m - j) : ℕ) : ℝ) with hQ
  have hxpos : (0 : ℝ) < x := by rw [hx]; exact_mod_cast (by omega : 0 < n)
  have hcard : ((Bm n m).card : ℝ) = T := by rw [card_Bm]
  have hM : ∀ (i : Fin n) (a : ℕ), a ≤ 4 →
      ∑ S ∈ Bm n m, ((pairDeg S i).choose a : ℝ) = A a * Q a := by
    intro i a ha
    simp only [hA, hQ]
    exact_mod_cast sum_choose_pairDeg n m i a (by omega)
  have hM1 : ∀ i : Fin n, ∑ S ∈ Bm n m, ((pairDeg S i : ℝ)) = A 1 * Q 1 := by
    intro i; rw [← hM i 1 (by norm_num)]; simp
  have hMM : ∀ (i j : Fin n), i ≠ j → ∀ a b : ℕ, a + b ≤ 4 →
      ∑ S ∈ Bm n m, ((pairDeg S i).choose a : ℝ) * (pairDeg S j).choose b =
        A a * A b * Q (a + b) := by
    intro i j hij a b hab
    simp only [hA, hQ]
    exact_mod_cast sum_choose_pairDeg_mul n m hij a b (by omega)
  set β : ℝ := k ^ 2 / x + cF x k with hβ
  have hG : ∀ S ∈ Bm n m,
      Fd n m (pairDeg S) - cF x k = (∑ i, ((pairDeg S i : ℝ)) ^ 2) - β := by
    intro S hS
    have hsum : ∑ i, ((pairDeg S i : ℝ)) = k := by
      rw [hk]; exact_mod_cast ((card_eq_sum_pairDeg S).symm.trans (mem_Bm.1 hS).2)
    simp only [Fd, sub_sq, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum, sum_const,
      card_univ, Fintype.card_fin, hβ]
    rw [hsum, nsmul_eq_mul, ← hx, ← hk]
    field_simp
    ring
  rw [sum_congr rfl fun S hS => by rw [hG S hS]]
  have hexp : ∑ S ∈ Bm n m, ((∑ i, ((pairDeg S i : ℝ)) ^ 2) - β) ^ 2 =
      ∑ S ∈ Bm n m, (∑ i, ((pairDeg S i : ℝ)) ^ 2) ^ 2 -
        2 * β * ∑ S ∈ Bm n m, ∑ i, ((pairDeg S i : ℝ)) ^ 2 + (Bm n m).card * β ^ 2 := by
    simp only [sub_sq, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum, sum_const]
    ring
  have hi2 : ∀ i : Fin n, ∑ S ∈ Bm n m, ((pairDeg S i : ℝ)) ^ 2 = 2 * (A 2 * Q 2) + A 1 * Q 1 := by
    intro i
    rw [← hM i 2 (by norm_num), ← hM1 i, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun S _ => sq_eq_choose _
  have h1 : ∑ S ∈ Bm n m, ∑ i, ((pairDeg S i : ℝ)) ^ 2 = n * (2 * (A 2 * Q 2) + A 1 * Q 1) := by
    rw [sum_comm, sum_congr rfl fun i _ => hi2 i]
    simp [sum_const, card_univ]; ring
  have hdiag : ∀ i : Fin n, ∑ S ∈ Bm n m, ((pairDeg S i : ℝ)) ^ 2 * ((pairDeg S i : ℝ)) ^ 2 =
      24 * (A 4 * Q 4) + 36 * (A 3 * Q 3) + 14 * (A 2 * Q 2) + A 1 * Q 1 := by
    intro i
    rw [← hM i 4 (by norm_num), ← hM i 3 (by norm_num), ← hM i 2 (by norm_num), ← hM1 i,
      mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun S _ => by rw [← pow_four_eq_choose]; ring
  have hoff : ∀ i j : Fin n, i ≠ j →
      ∑ S ∈ Bm n m, ((pairDeg S i : ℝ)) ^ 2 * ((pairDeg S j : ℝ)) ^ 2 =
        4 * (A 2 * A 2 * Q 4) + 2 * (A 2 * A 1 * Q 3) + 2 * (A 1 * A 2 * Q 3) +
          A 1 * A 1 * Q 2 := by
    intro i j hij
    rw [← hMM i j hij 2 2 (by norm_num), ← hMM i j hij 2 1 (by norm_num),
      ← hMM i j hij 1 2 (by norm_num), ← hMM i j hij 1 1 (by norm_num),
      mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun S _ => ?_
    rw [sq_eq_choose, sq_eq_choose]
    simp only [Nat.choose_one_right]
    ring
  have h2 : ∑ S ∈ Bm n m, (∑ i, ((pairDeg S i : ℝ)) ^ 2) ^ 2 =
      n * (24 * (A 4 * Q 4) + 36 * (A 3 * Q 3) + 14 * (A 2 * Q 2) + A 1 * Q 1) +
        n * (n - 1 : ℝ) * (4 * (A 2 * A 2 * Q 4) + 2 * (A 2 * A 1 * Q 3) +
          2 * (A 1 * A 2 * Q 3) + A 1 * A 1 * Q 2) := by
    have hsq : ∀ S : Finset (Fin n × Fin n), (∑ i, ((pairDeg S i : ℝ)) ^ 2) ^ 2 =
        ∑ i, ∑ j, ((pairDeg S i : ℝ)) ^ 2 * ((pairDeg S j : ℝ)) ^ 2 := fun S => by
      rw [sq, sum_mul_sum]
    rw [sum_congr rfl fun S _ => hsq S, sum_comm, sum_congr rfl fun i _ => sum_comm]
    have hi : ∀ i : Fin n, ∑ j, ∑ S ∈ Bm n m, ((pairDeg S i : ℝ)) ^ 2 * ((pairDeg S j : ℝ)) ^ 2 =
        (24 * (A 4 * Q 4) + 36 * (A 3 * Q 3) + 14 * (A 2 * Q 2) + A 1 * Q 1) +
          (n - 1 : ℝ) * (4 * (A 2 * A 2 * Q 4) + 2 * (A 2 * A 1 * Q 3) +
            2 * (A 1 * A 2 * Q 3) + A 1 * A 1 * Q 2) := by
      intro i
      rw [← add_sum_erase univ _ (mem_univ i), hdiag i,
        sum_congr rfl fun j hj => hoff i j (ne_of_mem_erase hj).symm, sum_const,
        card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_sub (by omega), Nat.cast_one]
    rw [sum_congr rfl fun i _ => hi i]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hexp, h1, h2, hcard]
  -- closed forms
  have hn1 : ((n - 1 : ℕ) : ℝ) = x - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hA1 : A 1 = x - 1 := by simp [hA, hn1]
  have hA2 : A 2 = (x - 1) * (x - 2) / 2 := by
    simp only [hA]; rw [Nat.cast_choose_two, hn1]; ring
  have hA3 : A 3 = (x - 1) * (x - 2) * (x - 3) / 6 := by
    simp only [hA]; rw [cast_choose_three, hn1]; ring
  have hA4 : A 4 = (x - 1) * (x - 2) * (x - 3) * (x - 4) / 24 := by
    simp only [hA]; rw [cast_choose_four, hn1]; ring
  have hN : ((n * (n - 1) : ℕ) : ℝ) = x * (x - 1) := by push_cast [hn1]; rfl
  have hTpos : 0 < T := by rw [hT]; exact_mod_cast Nat.choose_pos hmN
  have hQj : ∀ j ≤ 4, Q j = T * ((∏ i ∈ range j, (k - i)) / ∏ i ∈ range j, (x * (x - 1) - i)) := by
    intro j hj
    have := choose_div_choose (n * (n - 1)) (2 * m) j hmN (by omega)
    rw [cast_descFactorial_of_le (by omega), cast_descFactorial_of_le (by omega), hN] at this
    push_cast at this
    rw [← hk, ← hT] at this
    simp only [hQ]
    rw [← this]
    field_simp
  rw [hQj 1 (by norm_num), hQj 2 (by norm_num), hQj 3 (by norm_num), hQj 4 (by norm_num),
    hA1, hA2, hA3, hA4]
  simp only [prod_range_succ, prod_range_zero, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat,
    sub_zero, one_mul]
  have hx3 : (3 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hn
  have hN3' : 3 < x * (x - 1) := by nlinarith
  have hN0 : x * (x - 1) ≠ 0 := by linarith
  have hN1 : x * (x - 1) - 1 ≠ 0 := by linarith
  have hN2 : x * (x - 1) - 2 ≠ 0 := by linarith
  have hN3 : x * (x - 1) - 3 ≠ 0 := by linarith
  have hx1 : x + 1 ≠ 0 := by linarith
  have hx0 : x ≠ 0 := by linarith
  have hxm1 : x - 1 ≠ 0 := by linarith
  simp only [hβ, cF, varF, ← hx]
  field_simp
  ring

/-- `Var F ≤ 25 c² / n`: the relative standard deviation of `F` is `O(n^{-1/2})`. -/
theorem varF_le {x k : ℝ} (hx : 3 ≤ x) (hk : 1 ≤ k) (hkN : k + 1 ≤ x * (x - 1)) :
    varF x k ≤ 25 * cF x k ^ 2 / x := by
  unfold varF cF
  set N := x * (x - 1) with hN
  have hN3 : x ^ 2 / 3 ≤ N - 3 := by rw [hN]; nlinarith
  have hN1 : x ^ 2 / 2 ≤ N - 1 := by rw [hN]; nlinarith
  have hNx : x ≤ (N - 1) ^ 2 := by nlinarith
  have hx0 : 0 < x := by linarith
  have hNk : 0 < N - k := by linarith
  have hN3' : 0 < N - 3 := by nlinarith
  have hN1' : 0 < N - 1 := by nlinarith
  have hden : 0 < (x + 1) * (N - 3) * (N - 1) ^ 2 :=
    mul_pos (mul_pos (by linarith) hN3') (pow_pos hN1' 2)
  have h1 : 2 * k * (k - 1) * (x - 1) ^ 2 * (N - k) * (N - k - 1) / ((x + 1) * (N - 3) * (N - 1) ^ 2)
      ≤ 24 * (k * (N - k) / x ^ 2) ^ 2 / x := by
    rw [div_le_div_iff₀ hden hx0]
    have hb : (k - 1) * (x - 1) ^ 2 * (N - k - 1) ≤ k * x ^ 2 * (N - k) :=
      mul_le_mul (mul_le_mul (by linarith) (pow_le_pow_left₀ (by linarith) (by linarith) 2)
        (by positivity) (by linarith)) (by linarith) (by linarith) (by positivity)
    have hd : x * (x ^ 2 / 3) * (x ^ 2 / 2) ^ 2 ≤ (x + 1) * (N - 3) * (N - 1) ^ 2 :=
      mul_le_mul (mul_le_mul (by linarith) hN3 (by positivity) (by linarith))
        (pow_le_pow_left₀ (by positivity) hN1 2) (by positivity) (by positivity)
    have hc : 0 ≤ 2 * k * (N - k) * x := by positivity
    calc 2 * k * (k - 1) * (x - 1) ^ 2 * (N - k) * (N - k - 1) * x
        = 2 * k * (N - k) * x * ((k - 1) * (x - 1) ^ 2 * (N - k - 1)) := by ring
      _ ≤ 2 * k * (N - k) * x * (k * x ^ 2 * (N - k)) := mul_le_mul_of_nonneg_left hb hc
      _ = 24 * (k * (N - k) / x ^ 2) ^ 2 * (x * (x ^ 2 / 3) * (x ^ 2 / 2) ^ 2) := by
          field_simp; ring
      _ ≤ 24 * (k * (N - k) / x ^ 2) ^ 2 * ((x + 1) * (N - 3) * (N - 1) ^ 2) :=
          mul_le_mul_of_nonneg_left hd (by positivity)
  have h2 : k ^ 2 * (N - k) ^ 2 / (x ^ 4 * (N - 1) ^ 2) ≤ (k * (N - k) / x ^ 2) ^ 2 / x := by
    rw [show (k * (N - k) / x ^ 2) ^ 2 / x = k ^ 2 * (N - k) ^ 2 / (x ^ 4 * x) by
      field_simp]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hNx (by positivity))
  calc _ ≤ 24 * (k * (N - k) / x ^ 2) ^ 2 / x + (k * (N - k) / x ^ 2) ^ 2 / x := add_le_add h1 h2
    _ = _ := by ring

/-- `H̃(d) = exp((1 - (F/c)²)/4)` on `ℬ_m(n)`. -/
theorem expFactor_pairDeg {m : ℕ} (hn : 2 ≤ n) (hm : 1 ≤ m) (hmN : 2 * m < n * (n - 1))
    {S : Finset (Fin n × Fin n)} (hS : S ∈ Bm n m) :
    expFactor (pairDeg S) = exp ((1 - (Fd n m (pairDeg S) / cF n (2 * m)) ^ 2) / 4) := by
  have hsum : ∑ i, ((pairDeg S i : ℝ)) = 2 * m := by
    exact_mod_cast ((card_eq_sum_pairDeg S).symm.trans (mem_Bm.1 hS).2)
  have hx : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hN : (2 * m : ℝ) < n * (n - 1) := by
    have := Nat.cast_lt (α := ℝ).2 hmN
    push_cast [Nat.cast_sub (by omega : 1 ≤ n)] at this; exact this
  unfold expFactor gamma2 density avgDeg Fd cF
  rw [hsum]
  set F := ∑ i, ((pairDeg S i : ℝ) - 2 * m / n) ^ 2
  congr 1
  have h1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (n : ℝ) * (n - 1) - 2 * m ≠ 0 := by linarith
  have h3 : (1 : ℝ) - 2 * m / n / (n - 1) ≠ 0 := by
    have : 2 * (m : ℝ) / n / (n - 1) < 1 := by
      rw [div_div, div_lt_one (mul_pos (by linarith) (by linarith))]; exact hN
    exact sub_ne_zero.2 (ne_of_gt this)
  field_simp

/-- `|exp((1 - t²)/4) - 1| ≤ |t - 1| + (t - 1)²/2` for `t ≥ 0`. -/
theorem abs_expF_sub_one_le {t : ℝ} (ht : 0 ≤ t) :
    |exp ((1 - t ^ 2) / 4) - 1| ≤ |t - 1| + (t - 1) ^ 2 / 2 := by
  set y := (1 - t ^ 2) / 4 with hy
  have hy1 : |1 - t ^ 2| ≤ 2 * |t - 1| + (t - 1) ^ 2 := by
    have : 1 - t ^ 2 = -(t - 1) * (2 + (t - 1)) := by ring
    rw [this, abs_mul, abs_neg, abs_of_nonneg (by linarith [abs_nonneg (t - 1)] : 0 ≤ 2 + (t - 1))]
    have h1 : |t - 1| * (t - 1) ≤ |t - 1| * |t - 1| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (abs_nonneg _)
    have h2 : |t - 1| * |t - 1| = (t - 1) ^ 2 := by rw [abs_mul_abs_self]; ring
    nlinarith [h1, h2]
  have key : |exp y - 1| ≤ 2 * |y| := by
    rcases le_or_gt y 0 with h | h
    · rw [abs_of_nonpos (by linarith [exp_le_one_iff.2 h] : exp y - 1 ≤ 0), abs_of_nonpos h]
      linarith [add_one_le_exp y]
    · have hy4 : y ≤ 1 / 4 := by rw [hy]; nlinarith
      exact abs_exp_sub_one_le (by rw [abs_of_pos h]; linarith)
  calc |exp y - 1| ≤ 2 * |y| := key
    _ = |1 - t ^ 2| / 2 := by rw [hy, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]; ring
    _ ≤ _ := by linarith

/-- (6.8) in explicit form: `|E_{ℬ_m} H̃ - 1| ≤ 18 / √n`. -/
theorem abs_expect_expFactor_sub_one_le (n m : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m)
    (hmN : 2 * m + 1 < n * (n - 1)) :
    |∑ S ∈ Bm n m, expFactor (pairDeg S) / (Bm n m).card - 1| ≤ 18 / √n := by
  set T : ℝ := ((Bm n m).card : ℝ) with hT
  have hTpos : 0 < T := by
    rw [hT, card_Bm]; exact_mod_cast Nat.choose_pos (by omega)
  have hx : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hk : (1 : ℝ) ≤ 2 * m := by linarith
  have hkN : 2 * (m : ℝ) + 1 ≤ n * (n - 1) := by
    have := Nat.cast_le (α := ℝ).2 hmN.le
    push_cast [Nat.cast_sub (by omega : 1 ≤ n)] at this; linarith
  have hc : 0 < cF n (2 * m) := by
    unfold cF; apply div_pos (mul_pos (by linarith) (by linarith)); positivity
  set ρ : Finset (Fin n × Fin n) → ℝ := fun S => Fd n m (pairDeg S) / cF n (2 * m) - 1 with hρ
  -- second moment of `ρ`
  have hρ2 : ∑ S ∈ Bm n m, ρ S ^ 2 ≤ 25 * T / n := by
    have : ∑ S ∈ Bm n m, ρ S ^ 2 =
        (∑ S ∈ Bm n m, (Fd n m (pairDeg S) - cF n (2 * m)) ^ 2) / cF n (2 * m) ^ 2 := by
      rw [sum_div]
      exact sum_congr rfl fun S _ => by rw [hρ]; field_simp
    rw [this, sum_Fd_sub_sq n m hn hm (by omega), ← hT, div_le_iff₀ (by positivity)]
    have := varF_le hx hk hkN
    calc T * varF n (2 * m) ≤ T * (25 * cF n (2 * m) ^ 2 / n) := by gcongr
      _ = _ := by field_simp
  have hρ1 : ∑ S ∈ Bm n m, |ρ S| ≤ 5 * T / √n := by
    have hsq' := sum_mul_sq_le_sq_mul_sq (R := ℝ) (Bm n m)
      (fun _ => 1) (fun S => |ρ S|)
    have hsq : (∑ S ∈ Bm n m, |ρ S|) ^ 2 ≤
        ((Bm n m).card : ℝ) * ∑ S ∈ Bm n m, |ρ S| ^ 2 := by
      simpa using hsq'
    simp only [sq_abs] at hsq
    rw [← hT] at hsq
    have h25 : (∑ S ∈ Bm n m, |ρ S|) ^ 2 ≤ (5 * T / √n) ^ 2 := by
      calc (∑ S ∈ Bm n m, |ρ S|) ^ 2 ≤ T * ∑ S ∈ Bm n m, ρ S ^ 2 := hsq
        _ ≤ T * (25 * T / n) := by gcongr
        _ = (5 * T / √n) ^ 2 := by
            rw [div_pow, mul_pow, sq_sqrt (by positivity)]; ring
    exact le_of_sq_le_sq h25 (by positivity)
  -- pointwise bound
  have hpt : ∀ S ∈ Bm n m, |expFactor (pairDeg S) - 1| ≤ |ρ S| + ρ S ^ 2 / 2 := by
    intro S hS
    rw [expFactor_pairDeg (by omega) (by omega) (by omega) hS]
    exact abs_expF_sub_one_le (div_nonneg (sum_nonneg fun i _ => sq_nonneg _) hc.le)
  have hsn : 0 < √(n : ℝ) := sqrt_pos.2 (by linarith)
  have hsn1 : 1 ≤ √(n : ℝ) := by rw [le_sqrt (by norm_num) (by linarith)]; linarith
  have hn_sqrt : 1 / (n : ℝ) ≤ 1 / √n := by
    rw [div_le_div_iff₀ (by linarith) hsn]
    have : √(n : ℝ) ≤ n := by rw [sqrt_le_left (by linarith)]; nlinarith
    linarith
  calc |∑ S ∈ Bm n m, expFactor (pairDeg S) / T - 1|
      = |∑ S ∈ Bm n m, (expFactor (pairDeg S) - 1)| / T := by
        rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, ← hT,
          show |∑ S ∈ Bm n m, expFactor (pairDeg S) - T| / T =
            |(∑ S ∈ Bm n m, expFactor (pairDeg S) - T) / T| by rw [abs_div, abs_of_pos hTpos],
          sub_div, div_self hTpos.ne', sum_div]
    _ ≤ (∑ S ∈ Bm n m, (|ρ S| + ρ S ^ 2 / 2)) / T := by
        gcongr
        exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum hpt)
    _ ≤ (5 * T / √n + 25 * T / n / 2) / T := by
        rw [sum_add_distrib, ← sum_div]
        gcongr
    _ = 5 * (1 / √n) + 25 / 2 * (1 / n) := by field_simp
    _ ≤ 5 * (1 / √n) + 25 / 2 * (1 / √n) := by gcongr
    _ = 18 / √n - 1 / 2 * (1 / √n) := by ring
    _ ≤ 18 / √n := by linarith [one_div_nonneg.2 hsn.le]

end LW
