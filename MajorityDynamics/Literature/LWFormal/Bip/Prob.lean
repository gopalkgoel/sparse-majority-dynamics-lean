import MajorityDynamics.Literature.LWFormal.Assembly
import MajorityDynamics.Literature.LWFormal.Bip.Defs

set_option autoImplicit true

/-!
# Probability layer for `𝒢(ℓ,n,m)`: degree tails and the second moment of `∑ (sₐ - s̄)²`
-/

namespace LW.Bip

open Finset Real

variable {ℓ n : ℕ}

/-- The pairs with left endpoint `a`. -/
def row (a : Fin ℓ) : Finset (Fin ℓ × Fin n) := univ.filter (·.1 = a)

theorem card_row (a : Fin ℓ) : (row (n := n) a).card = n := by
  have : row (n := n) a = univ.map ⟨fun v : Fin n => (a, v), fun x y h => (Prod.mk.inj h).2⟩ := by
    ext ⟨b, w⟩
    simp only [row, mem_filter, mem_univ, true_and, mem_map]
    constructor
    · rintro rfl; exact ⟨w, rfl⟩
    · rintro ⟨_, h⟩; exact (Prod.mk.inj h).1.symm
  rw [this, card_map, card_univ, Fintype.card_fin]

theorem ldeg_eq_card_inter (E : BGraph ℓ n) (a : Fin ℓ) : ldeg E a = (E ∩ row a).card := by
  unfold ldeg; congr 1; ext p; simp [row]

theorem row_disjoint {a b : Fin ℓ} (h : a ≠ b) : Disjoint (row (n := n) a) (row b) := by
  rw [disjoint_left]
  intro p hp hq
  simp only [row, mem_filter] at hp hq
  exact h (hp.2.symm.trans hq.2)

theorem mem_Gm {m : ℕ} {E : BGraph ℓ n} : E ∈ Gm ℓ n m ↔ E.card = m := by
  simp [Gm, mem_powersetCard]

theorem card_Gm (ℓ n m : ℕ) : (Gm ℓ n m).card = (ℓ * n).choose m := by
  rw [Gm, card_powersetCard, card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

theorem sum_ldeg (E : BGraph ℓ n) : ∑ a, ldeg E a = E.card :=
  (card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) fun _ _ => mem_univ _).symm

theorem sum_rdeg (E : BGraph ℓ n) : ∑ v, rdeg E v = E.card :=
  (card_eq_sum_card_fiberwise (f := Prod.snd) (t := univ) fun _ _ => mem_univ _).symm

theorem ldeg_le (E : BGraph ℓ n) (a : Fin ℓ) : ldeg E a ≤ n := by
  rw [ldeg_eq_card_inter]; exact (card_le_card inter_subset_right).trans (card_row a).le

/-- Transposition `(a, v) ↦ (v, a)`. -/
def tr : BGraph ℓ n ≃ BGraph n ℓ := (Equiv.prodComm (Fin ℓ) (Fin n)).finsetCongr

theorem ldeg_tr (E : BGraph ℓ n) (v : Fin n) : ldeg (tr E) v = rdeg E v := by
  unfold ldeg rdeg tr
  rw [Equiv.finsetCongr_apply, filter_map, card_map]
  congr 1

theorem rdeg_tr (E : BGraph ℓ n) (a : Fin ℓ) : rdeg (tr E) a = ldeg E a := by
  unfold ldeg rdeg tr
  rw [Equiv.finsetCongr_apply, filter_map, card_map]
  congr 1

theorem rdeg_le (E : BGraph ℓ n) (v : Fin n) : rdeg E v ≤ ℓ := by
  rw [← ldeg_tr]; exact ldeg_le _ _

theorem tr_mem_Gm {m : ℕ} {E : BGraph ℓ n} : tr E ∈ Gm n ℓ m ↔ E ∈ Gm ℓ n m := by
  simp [mem_Gm, tr, Equiv.finsetCongr_apply]

theorem sum_tr {m : ℕ} (f : BGraph n ℓ → ℝ) :
    ∑ E ∈ Gm ℓ n m, f (tr E) = ∑ F ∈ Gm n ℓ m, f F :=
  sum_equiv tr (fun _ => tr_mem_Gm.symm) fun _ _ => rfl

theorem prob_tr {m : ℕ} (A : BGraph n ℓ → Prop) [DecidablePred A] :
    prob (Gm ℓ n m) (fun E => A (tr E)) = prob (Gm n ℓ m) A := by
  have : ((Gm ℓ n m).filter fun E => A (tr E)).card = ((Gm n ℓ m).filter A).card :=
    card_equiv tr fun E => by simp [tr_mem_Gm]
  unfold prob
  rw [card_Gm, card_Gm, mul_comm ℓ n, this]

/-! ### Degree tails -/

theorem ldeg_tail (ℓ n m : ℕ) (hℓ : 2 ≤ ℓ) (hn : 1 ≤ n) (hm : 2 * m ≤ ℓ * n) (a : Fin ℓ) {t : ℝ}
    (ht : 6 ≤ t) (htμ : t ≤ m / ℓ) :
    prob (Gm ℓ n m) (fun E => t < |(ldeg E a : ℝ) - m / ℓ|) ≤
      2 * (m / ℓ + 1) * exp (-t ^ 2 / (32 * (m / ℓ))) := by
  have hk : (row (n := n) a).card + m ≤ (univ : Finset (Fin ℓ × Fin n)).card := by
    rw [card_row, card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    have := Nat.mul_le_mul_right n hℓ; omega
  have hμ : (m / ℓ : ℝ) = (row (n := n) a).card * m / (univ : Finset (Fin ℓ × Fin n)).card := by
    rw [card_row, card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (by omega : ℓ ≠ 0)
    push_cast; field_simp
  refine le_trans (prob_mono _ fun E _ h => ?_) (hyp_tail' univ (row a) m (subset_univ _) hk hμ ht htμ)
  rwa [← ldeg_eq_card_inter]

theorem rdeg_tail (ℓ n m : ℕ) (hn : 2 ≤ n) (hℓ : 1 ≤ ℓ) (hm : 2 * m ≤ ℓ * n) (v : Fin n) {t : ℝ}
    (ht : 6 ≤ t) (htμ : t ≤ m / n) :
    prob (Gm ℓ n m) (fun E => t < |(rdeg E v : ℝ) - m / n|) ≤
      2 * (m / n + 1) * exp (-t ^ 2 / (32 * (m / n))) := by
  have := ldeg_tail n ℓ m hn hℓ (by rw [Nat.mul_comm n ℓ]; exact hm) v ht htμ
  rw [← prob_tr (fun F : BGraph n ℓ => t < |(ldeg F v : ℝ) - m / n|)] at this
  simpa only [ldeg_tr] using this

/-! ### Second moment of `F(s) = ∑ₐ (sₐ - m/ℓ)²` -/

theorem sum_choose_ldeg (ℓ n m : ℕ) (a : Fin ℓ) (j : ℕ) (hj : j ≤ m) :
    ∑ E ∈ Gm ℓ n m, (ldeg E a).choose j = n.choose j * (ℓ * n - j).choose (m - j) := by
  have := sum_choose_inter_mul (univ : Finset (Fin ℓ × Fin n)) (row a) ∅ (subset_univ _)
    (empty_subset _) (disjoint_empty_right _) j 0 m (by omega)
  simp only [card_empty, Nat.choose_zero_right, mul_one, add_zero, card_row, card_univ,
    Fintype.card_prod, Fintype.card_fin] at this
  rw [← this]
  exact sum_congr rfl fun E _ => by rw [ldeg_eq_card_inter]

theorem sum_choose_ldeg_mul (ℓ n m : ℕ) {a b : Fin ℓ} (hab : a ≠ b) (i j : ℕ) (hij : i + j ≤ m) :
    ∑ E ∈ Gm ℓ n m, (ldeg E a).choose i * (ldeg E b).choose j =
      n.choose i * n.choose j * (ℓ * n - (i + j)).choose (m - (i + j)) := by
  have := sum_choose_inter_mul (univ : Finset (Fin ℓ × Fin n)) (row a) (row b) (subset_univ _)
    (subset_univ _) (row_disjoint hab) i j m hij
  simp only [card_row, card_univ, Fintype.card_prod, Fintype.card_fin] at this
  rw [← this]
  exact sum_congr rfl fun E _ => by rw [ldeg_eq_card_inter, ldeg_eq_card_inter]

/-- `F(s) = ∑ₐ (sₐ - m/ℓ)²`. -/
noncomputable def FS (ℓ m : ℕ) (s : Fin ℓ → ℕ) : ℝ := ∑ a, ((s a : ℝ) - m / ℓ) ^ 2

/-- `E F` under `𝒢(ℓ,n,m)` (`x = ℓ`, `q = n`, `k = m`). -/
noncomputable def cB (x q k : ℝ) : ℝ := k * (x - 1) * (x * q - k) / (x * (x * q - 1))

/-- `E (F - E F)²` under `𝒢(ℓ,n,m)` (exact). -/
noncomputable def varB (x q k : ℝ) : ℝ :=
  2 * k * q * (x - 1) * (k - 1) * (q - 1) * (x * q - k) * (x * q - k - 1) /
    ((x * q - 3) * (x * q - 2) * (x * q - 1) ^ 2)

theorem sum_FS_sub_sq (ℓ n m : ℕ) (hℓ : 1 ≤ ℓ) (hN : 4 ≤ ℓ * n) (hm : 4 ≤ m) (hmN : m ≤ ℓ * n) :
    ∑ E ∈ Gm ℓ n m, (FS ℓ m (ldeg E) - cB ℓ n m) ^ 2 = (Gm ℓ n m).card * varB ℓ n m := by
  set x : ℝ := (ℓ : ℝ) with hx
  set q : ℝ := (n : ℝ) with hq
  set k : ℝ := (m : ℝ) with hk
  set T : ℝ := (((ℓ * n).choose m : ℕ) : ℝ) with hT
  set A : ℕ → ℝ := fun j => ((n.choose j : ℕ) : ℝ) with hA
  set Q : ℕ → ℝ := fun j => (((ℓ * n - j).choose (m - j) : ℕ) : ℝ) with hQ
  have hxpos : (0 : ℝ) < x := by rw [hx]; exact_mod_cast hℓ
  have hcard : ((Gm ℓ n m).card : ℝ) = T := by rw [card_Gm]
  have hM : ∀ (a : Fin ℓ) (j : ℕ), j ≤ 4 →
      ∑ E ∈ Gm ℓ n m, ((ldeg E a).choose j : ℝ) = A j * Q j := by
    intro a j hj
    simp only [hA, hQ]
    exact_mod_cast sum_choose_ldeg ℓ n m a j (by omega)
  have hM1 : ∀ a : Fin ℓ, ∑ E ∈ Gm ℓ n m, ((ldeg E a : ℝ)) = A 1 * Q 1 := by
    intro a; rw [← hM a 1 (by norm_num)]; simp
  have hMM : ∀ (a b : Fin ℓ), a ≠ b → ∀ i j : ℕ, i + j ≤ 4 →
      ∑ E ∈ Gm ℓ n m, ((ldeg E a).choose i : ℝ) * (ldeg E b).choose j = A i * A j * Q (i + j) := by
    intro a b hab i j hij
    simp only [hA, hQ]
    exact_mod_cast sum_choose_ldeg_mul ℓ n m hab i j (by omega)
  set β : ℝ := k ^ 2 / x + cB x q k with hβ
  have hG : ∀ E ∈ Gm ℓ n m, FS ℓ m (ldeg E) - cB x q k = (∑ a, ((ldeg E a : ℝ)) ^ 2) - β := by
    intro E hE
    have hsum : ∑ a, ((ldeg E a : ℝ)) = k := by
      rw [hk]; exact_mod_cast (sum_ldeg E).trans (mem_Gm.1 hE)
    simp only [FS, sub_sq, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum, sum_const,
      card_univ, Fintype.card_fin, hβ]
    rw [hsum, nsmul_eq_mul, ← hx, ← hk]
    field_simp
    ring
  rw [sum_congr rfl fun E hE => by rw [hG E hE]]
  have hexp : ∑ E ∈ Gm ℓ n m, ((∑ a, ((ldeg E a : ℝ)) ^ 2) - β) ^ 2 =
      ∑ E ∈ Gm ℓ n m, (∑ a, ((ldeg E a : ℝ)) ^ 2) ^ 2 -
        2 * β * ∑ E ∈ Gm ℓ n m, ∑ a, ((ldeg E a : ℝ)) ^ 2 + (Gm ℓ n m).card * β ^ 2 := by
    simp only [sub_sq, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum, sum_const]
    ring
  have hi2 : ∀ a : Fin ℓ, ∑ E ∈ Gm ℓ n m, ((ldeg E a : ℝ)) ^ 2 = 2 * (A 2 * Q 2) + A 1 * Q 1 := by
    intro a
    rw [← hM a 2 (by norm_num), ← hM1 a, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun E _ => sq_eq_choose _
  have h1 : ∑ E ∈ Gm ℓ n m, ∑ a, ((ldeg E a : ℝ)) ^ 2 = ℓ * (2 * (A 2 * Q 2) + A 1 * Q 1) := by
    rw [sum_comm, sum_congr rfl fun a _ => hi2 a]
    simp [sum_const, card_univ]; ring
  have hdiag : ∀ a : Fin ℓ, ∑ E ∈ Gm ℓ n m, ((ldeg E a : ℝ)) ^ 2 * ((ldeg E a : ℝ)) ^ 2 =
      24 * (A 4 * Q 4) + 36 * (A 3 * Q 3) + 14 * (A 2 * Q 2) + A 1 * Q 1 := by
    intro a
    rw [← hM a 4 (by norm_num), ← hM a 3 (by norm_num), ← hM a 2 (by norm_num), ← hM1 a,
      mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun E _ => by rw [← pow_four_eq_choose]; ring
  have hoff : ∀ a b : Fin ℓ, a ≠ b →
      ∑ E ∈ Gm ℓ n m, ((ldeg E a : ℝ)) ^ 2 * ((ldeg E b : ℝ)) ^ 2 =
        4 * (A 2 * A 2 * Q 4) + 2 * (A 2 * A 1 * Q 3) + 2 * (A 1 * A 2 * Q 3) +
          A 1 * A 1 * Q 2 := by
    intro a b hab
    rw [← hMM a b hab 2 2 (by norm_num), ← hMM a b hab 2 1 (by norm_num),
      ← hMM a b hab 1 2 (by norm_num), ← hMM a b hab 1 1 (by norm_num),
      mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun E _ => ?_
    rw [sq_eq_choose, sq_eq_choose]
    simp only [Nat.choose_one_right]
    ring
  have h2 : ∑ E ∈ Gm ℓ n m, (∑ a, ((ldeg E a : ℝ)) ^ 2) ^ 2 =
      ℓ * (24 * (A 4 * Q 4) + 36 * (A 3 * Q 3) + 14 * (A 2 * Q 2) + A 1 * Q 1) +
        ℓ * (ℓ - 1 : ℝ) * (4 * (A 2 * A 2 * Q 4) + 2 * (A 2 * A 1 * Q 3) +
          2 * (A 1 * A 2 * Q 3) + A 1 * A 1 * Q 2) := by
    have hsq : ∀ E : BGraph ℓ n, (∑ a, ((ldeg E a : ℝ)) ^ 2) ^ 2 =
        ∑ a, ∑ b, ((ldeg E a : ℝ)) ^ 2 * ((ldeg E b : ℝ)) ^ 2 := fun E => by
      rw [sq, sum_mul_sum]
    rw [sum_congr rfl fun E _ => hsq E, sum_comm, sum_congr rfl fun a _ => sum_comm]
    have hi : ∀ a : Fin ℓ, ∑ b, ∑ E ∈ Gm ℓ n m, ((ldeg E a : ℝ)) ^ 2 * ((ldeg E b : ℝ)) ^ 2 =
        (24 * (A 4 * Q 4) + 36 * (A 3 * Q 3) + 14 * (A 2 * Q 2) + A 1 * Q 1) +
          (ℓ - 1 : ℝ) * (4 * (A 2 * A 2 * Q 4) + 2 * (A 2 * A 1 * Q 3) +
            2 * (A 1 * A 2 * Q 3) + A 1 * A 1 * Q 2) := by
      intro a
      rw [← add_sum_erase univ _ (mem_univ a), hdiag a,
        sum_congr rfl fun b hb => hoff a b (ne_of_mem_erase hb).symm, sum_const,
        card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_sub hℓ, Nat.cast_one]
    rw [sum_congr rfl fun a _ => hi a]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hexp, h1, h2, hcard]
  -- closed forms
  have hA1 : A 1 = q := by simp only [hA, Nat.choose_one_right]; rfl
  have hA2 : A 2 = q * (q - 1) / 2 := by simp only [hA]; rw [Nat.cast_choose_two]
  have hA3 : A 3 = q * (q - 1) * (q - 2) / 6 := by simp only [hA]; rw [cast_choose_three]
  have hA4 : A 4 = q * (q - 1) * (q - 2) * (q - 3) / 24 := by
    simp only [hA]; rw [cast_choose_four]
  have hNc : ((ℓ * n : ℕ) : ℝ) = x * q := by push_cast; rfl
  have hTpos : 0 < T := by rw [hT]; exact_mod_cast Nat.choose_pos hmN
  have hQj : ∀ j ≤ 4, Q j = T * ((∏ i ∈ range j, (k - i)) / ∏ i ∈ range j, (x * q - i)) := by
    intro j hj
    have := choose_div_choose (ℓ * n) m j hmN (by omega)
    rw [cast_descFactorial_of_le (by omega), cast_descFactorial_of_le (by omega), hNc] at this

    rw [← hk, ← hT] at this
    simp only [hQ]
    rw [← this]
    field_simp
  rw [hQj 1 (by norm_num), hQj 2 (by norm_num), hQj 3 (by norm_num), hQj 4 (by norm_num),
    hA1, hA2, hA3, hA4]
  simp only [prod_range_succ, prod_range_zero, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat,
    sub_zero, one_mul]
  have hN4 : (4 : ℝ) ≤ x * q := by rw [← hNc]; exact_mod_cast hN
  have hN0 : x * q ≠ 0 := by linarith
  have hN1 : x * q - 1 ≠ 0 := by linarith
  have hN2 : x * q - 2 ≠ 0 := by linarith
  have hN3 : x * q - 3 ≠ 0 := by linarith
  have hx0 : x ≠ 0 := hxpos.ne'
  have hq0 : q ≠ 0 := by
    have : n ≠ 0 := fun h => by subst h; simp at hN
    rw [hq]; exact_mod_cast this
  simp only [hβ, cB, varB, ← hx]
  field_simp
  ring

/-- `Var F ≤ 8 (E F)² / ℓ`. -/
theorem varB_le {x q k : ℝ} (hx : 2 ≤ x) (hq : 1 ≤ q) (hk : 1 ≤ k) (hkN : k + 1 ≤ x * q)
    (hN : 6 ≤ x * q) : varB x q k ≤ 8 * cB x q k ^ 2 / x := by
  unfold varB cB
  set N := x * q with hN'
  have hx0 : 0 < x := by linarith
  have hxq : x * (q - 1) = N - x := by rw [hN']; ring
  have hxN : x ≤ N := by rw [hN']; nlinarith
  have hN3 : 0 ≤ N - 3 := by linarith
  have hN2 : 0 ≤ N - 2 := by linarith
  have hx1 : 0 ≤ x - 1 := by linarith
  have hNk : 0 ≤ N - k := by linarith
  have hxq0 : 0 ≤ x * (q - 1) := by rw [hxq]; linarith
  have hden : 0 < (N - 3) * (N - 2) * (N - 1) ^ 2 :=
    mul_pos (mul_pos (by linarith) (by linarith)) (pow_pos (by linarith) 2)
  have hden' : 0 < x ^ 3 * (N - 1) ^ 2 := mul_pos (pow_pos hx0 3) (pow_pos (by linarith) 2)
  rw [show 8 * (k * (x - 1) * (N - k) / (x * (N - 1))) ^ 2 / x =
      8 * k ^ 2 * (x - 1) ^ 2 * (N - k) ^ 2 / (x ^ 3 * (N - 1) ^ 2) by
    field_simp, div_le_div_iff₀ hden hden']
  have c1 : (k - 1) * (N - k - 1) ≤ k * (N - k) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have c2 : N * (x * (q - 1)) * x ≤ 2 * (N - 3) * (N - 2) * (2 * (x - 1)) :=
    mul_le_mul (mul_le_mul (by linarith) (by linarith) hxq0 (by linarith))
      (by linarith) hx0.le (by positivity)
  have hpre : 0 ≤ k * (x - 1) * (N - k) * (N - 1) ^ 2 := by positivity
  calc 2 * k * q * (x - 1) * (k - 1) * (q - 1) * (N - k) * (N - k - 1) * (x ^ 3 * (N - 1) ^ 2)
      = k * (x - 1) * (N - k) * (N - 1) ^ 2 *
          (2 * ((k - 1) * (N - k - 1)) * (N * (x * (q - 1)) * x)) := by rw [hN']; ring
    _ ≤ k * (x - 1) * (N - k) * (N - 1) ^ 2 *
          (2 * (k * (N - k)) * (2 * (N - 3) * (N - 2) * (2 * (x - 1)))) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left c1 (by norm_num))
          c2 (by positivity) (by positivity)) hpre
    _ = 8 * k ^ 2 * (x - 1) ^ 2 * (N - k) ^ 2 * ((N - 3) * (N - 2) * (N - 1) ^ 2) := by ring

/-- The relative deviation `ρ = F / E F - 1`: `E ρ² ≤ 8/ℓ` and `E |ρ| ≤ 3/√ℓ`. -/
theorem rho_moments (ℓ n m : ℕ) (hℓ : 2 ≤ ℓ) (hn : 1 ≤ n) (hm : 4 ≤ m) (hN : 6 ≤ ℓ * n)
    (hmN : m + 1 ≤ ℓ * n) :
    0 < cB ℓ n m ∧
      ∑ E ∈ Gm ℓ n m, (FS ℓ m (ldeg E) / cB ℓ n m - 1) ^ 2 ≤ 8 * ((Gm ℓ n m).card : ℝ) / ℓ ∧
      ∑ E ∈ Gm ℓ n m, |FS ℓ m (ldeg E) / cB ℓ n m - 1| ≤ 3 * ((Gm ℓ n m).card : ℝ) / √ℓ := by
  set T : ℝ := ((Gm ℓ n m).card : ℝ) with hT
  have hTpos : 0 < T := by
    rw [hT, card_Gm]; exact_mod_cast Nat.choose_pos (by omega)
  have hx : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hq : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hk : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hkN : (m : ℝ) + 1 ≤ ℓ * n := by exact_mod_cast hmN
  have hN' : (6 : ℝ) ≤ ℓ * n := by exact_mod_cast hN
  have hc : 0 < cB ℓ n m := by
    unfold cB
    exact div_pos (mul_pos (mul_pos (by linarith) (by linarith)) (by linarith))
      (mul_pos (by linarith) (by linarith))
  set ρ : BGraph ℓ n → ℝ := fun E => FS ℓ m (ldeg E) / cB ℓ n m - 1 with hρ
  have hρ2 : ∑ E ∈ Gm ℓ n m, ρ E ^ 2 ≤ 8 * T / ℓ := by
    have : ∑ E ∈ Gm ℓ n m, ρ E ^ 2 =
        (∑ E ∈ Gm ℓ n m, (FS ℓ m (ldeg E) - cB ℓ n m) ^ 2) / cB ℓ n m ^ 2 := by
      rw [sum_div]
      exact sum_congr rfl fun E _ => by rw [hρ]; field_simp
    rw [this, sum_FS_sub_sq ℓ n m (by omega) (by omega) hm (by omega), ← hT,
      div_le_iff₀ (by positivity)]
    have := varB_le hx hq hk hkN hN'
    calc T * varB ℓ n m ≤ T * (8 * cB ℓ n m ^ 2 / ℓ) := by gcongr
      _ = _ := by field_simp
  refine ⟨hc, hρ2, ?_⟩
  have hsq' := sum_mul_sq_le_sq_mul_sq (R := ℝ) (Gm ℓ n m)
    (fun _ => 1) (fun E => |ρ E|)
  have hsq : (∑ E ∈ Gm ℓ n m, |ρ E|) ^ 2 ≤
      ((Gm ℓ n m).card : ℝ) * ∑ E ∈ Gm ℓ n m, |ρ E| ^ 2 := by
    simpa using hsq'
  simp only [sq_abs] at hsq
  rw [← hT] at hsq
  have h9 : (∑ E ∈ Gm ℓ n m, |ρ E|) ^ 2 ≤ (3 * T / √ℓ) ^ 2 := by
    calc (∑ E ∈ Gm ℓ n m, |ρ E|) ^ 2 ≤ T * ∑ E ∈ Gm ℓ n m, ρ E ^ 2 := hsq
      _ ≤ T * (8 * T / ℓ) := by gcongr
      _ ≤ (3 * T / √ℓ) ^ 2 := by
          rw [div_pow, mul_pow, sq_sqrt (by positivity), mul_div_assoc']
          exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg T]) (by positivity)
  exact le_of_sq_le_sq h9 (by positivity)

end LW.Bip
