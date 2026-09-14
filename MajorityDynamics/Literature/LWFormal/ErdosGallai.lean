import MajorityDynamics.Literature.LWFormal.Defs

set_option autoImplicit true

/-!
# Erdős–Gallai theorem (Koren's form)

An even nonnegative sequence satisfying `∑_{S} dᵢ - ∑_{T} dⱼ ≤ |S|(n-1-|T|)` for all disjoint
`S, T` is graphical. Proof by induction on `∑ d`: reduce a maximum entry `x` and a minimum
positive entry `y` by one (Choudum's reduction), check the condition is preserved, then rebuild
a realisation of `d` from one of `d - e_x - e_y` by adding `xy` or a two-edge switching.
-/

namespace LW

open Finset

variable {n : ℕ}

/-- Koren's form of the Erdős–Gallai condition. -/
def Koren (d : Fin n → ℤ) : Prop :=
  ∀ S T : Finset (Fin n), Disjoint S T →
    ∑ i ∈ S, d i - ∑ j ∈ T, d j ≤ S.card * (n - 1 - T.card : ℤ)

theorem sum_sub_single (d : Fin n → ℤ) (x : Fin n) (A : Finset (Fin n)) :
    ∑ i ∈ A, (d - Pi.single x 1 : Fin n → ℤ) i = ∑ i ∈ A, d i - if x ∈ A then 1 else 0 := by
  simp [sum_sub_distrib, Pi.single_apply]

theorem card_add_card_le {S T : Finset (Fin n)} (h : Disjoint S T) : S.card + T.card ≤ n := by
  have := card_le_univ (S ∪ T); rwa [card_union_of_disjoint h, Fintype.card_fin] at this

/-- The reduction step preserves Koren's condition. -/
theorem Koren.sub {d : Fin n → ℤ} (hK : Koren d) (h0 : ∀ i, 0 ≤ d i) (hev : Even (∑ i, d i))
    {x y : Fin n} (hxy : x ≠ y) (hx : ∀ v, d v ≤ d x) (hx1 : 1 ≤ d x) (hy1 : 1 ≤ d y) :
    Koren (d - Pi.single x 1 - Pi.single y 1 : Fin n → ℤ) := by
  intro S T hST
  simp only [sum_sub_single]
  have hK0 := hK S T hST
  have hcard := card_add_card_le hST
  have hs0 : (0 : ℤ) ≤ S.card := by positivity
  have hS : ∑ i ∈ S, d i ≤ S.card * d x := by
    have := sum_le_card_nsmul S d (d x) fun i _ => hx i; simpa using this
  have F1 : x ∈ T →
      d x ≤ S.card * (n - 1 - T.card : ℤ) - ∑ i ∈ S, d i + ∑ j ∈ T, d j + S.card := by
    intro hxT
    have h := hK S (T.erase x) (hST.mono_right (erase_subset _ _))
    rw [sum_erase_eq_sub hxT] at h
    have hc := card_erase_add_one hxT
    have : ((T.erase x).card : ℤ) = T.card - 1 := by omega
    rw [this] at h
    linarith
  have F2 : x ∉ S → x ∉ T →
      d x ≤ S.card * (n - 1 - T.card : ℤ) - ∑ i ∈ S, d i + ∑ j ∈ T, d j + (n - 1 - T.card) := by
    intro hxS hxT
    have h := hK (insert x S) T (disjoint_insert_left.2 ⟨hxT, hST⟩)
    rw [sum_insert hxS, card_insert_of_notMem hxS] at h
    push_cast at h
    linarith
  by_cases hxT : x ∈ T
  · have hxS : x ∉ S := disjoint_right.1 hST hxT
    have hTx : d x ≤ ∑ j ∈ T, d j := single_le_sum (fun i _ => h0 i) hxT
    have h1 := F1 hxT
    by_cases hyS : y ∈ S
    · simp only [hxT, hxS, hyS, disjoint_left.1 hST hyS, if_true, if_false]; linarith
    · by_cases hyT : y ∈ T
      · simp only [hxT, hxS, hyS, hyT, if_true, if_false]
        have hTxy : d x + d y ≤ ∑ j ∈ T, d j := by
          have := sum_le_sum_of_subset_of_nonneg (s := {x, y}) (t := T) (f := d)
            (by simp [insert_subset_iff, hxT, hyT]) fun i _ _ => h0 i
          rwa [sum_pair hxy] at this
        by_cases hu : S.card + T.card = n
        · have hU : S ∪ T = univ :=
            eq_univ_of_card _ (by rw [card_union_of_disjoint hST, hu, Fintype.card_fin])
          have hsum : ∑ i ∈ S, d i + ∑ j ∈ T, d j = ∑ i, d i := by rw [← sum_union hST, hU]
          have hn : (n : ℤ) = S.card + T.card := by exact_mod_cast hu.symm
          rw [hn] at h1 hK0 ⊢
          obtain ⟨k, hk⟩ := hev
          obtain ⟨j, hj⟩ : Even (S.card * (S.card - 1 : ℤ) - ∑ i ∈ S, d i + ∑ j ∈ T, d j) := by
            have : S.card * (S.card - 1 : ℤ) - ∑ i ∈ S, d i + ∑ j ∈ T, d j =
                S.card * (S.card - 1) + (k + k) - 2 * ∑ i ∈ S, d i := by
              rw [← hk, ← hsum]; ring
            rw [this]
            exact ((Int.even_mul_pred_self _).add ⟨k, rfl⟩).sub (even_two_mul _)
          by_contra hcon
          have hK1 : S.card * (S.card - 1 : ℤ) - ∑ i ∈ S, d i + ∑ j ∈ T, d j = 0 := by
            have : (S.card : ℤ) * (S.card + T.card - 1 - T.card) = S.card * (S.card - 1) := by ring
            rw [this] at h1 hK0 hcon
            have h2 : j + j < 2 := by linarith
            have h3 : 0 ≤ j + j := by linarith
            have h4 : j = 0 := by omega
            rw [h4] at hj; linarith
          have hfs : d x ≤ S.card := by
            have : (S.card : ℤ) * (S.card + T.card - 1 - T.card) = S.card * (S.card - 1) := by ring
            rw [this] at h1; linarith
          have hprod : 0 ≤ ((S.card : ℤ) - 1) * (S.card - d x) := by
            rcases Nat.eq_zero_or_pos S.card with h | h
            · simp only [h, Nat.cast_zero]; nlinarith
            · exact mul_nonneg (by omega) (by linarith)
          nlinarith
        · have hu' : (S.card : ℤ) + T.card + 1 ≤ n := by omega
          have hprod : 0 ≤ (S.card : ℤ) * (n - 1 - T.card - S.card) :=
            mul_nonneg hs0 (by linarith)
          by_contra hcon
          rcases le_or_gt (d x) S.card with hfs | hfs
          · nlinarith [mul_nonneg hs0 (sub_nonneg.2 hfs)]
          · have : 0 ≤ (S.card : ℤ) * (S.card + 1 - d x) := mul_nonneg hs0 (by linarith)
            nlinarith
      · simp only [hxT, hxS, hyS, hyT, if_true, if_false]
        have hu' : (S.card : ℤ) + T.card + 1 ≤ n := by
          have := card_add_card_le (disjoint_insert_left.2 ⟨hyT, hST⟩)
          rw [card_insert_of_notMem hyS] at this; omega
        have hprod : 0 ≤ (S.card : ℤ) * (n - 1 - T.card - S.card) :=
          mul_nonneg hs0 (by linarith)
        by_contra hcon
        have hfs : d x ≤ S.card := by linarith
        nlinarith [mul_nonneg hs0 (sub_nonneg.2 hfs)]
  · by_cases hyT : y ∈ T
    · have hyS : y ∉ S := disjoint_right.1 hST hyT
      have hTy : d y ≤ ∑ j ∈ T, d j := single_le_sum (fun i _ => h0 i) hyT
      by_cases hxS : x ∈ S
      · simp only [hxT, hxS, hyS, hyT, if_true, if_false]; linarith
      · simp only [hxT, hxS, hyS, hyT, if_true, if_false]
        have h2 := F2 hxS hxT
        by_contra hcon
        have hf : d x ≤ n - 1 - T.card := by linarith
        nlinarith [mul_nonneg hs0 (sub_nonneg.2 hf)]
    · simp only [hxT, hyT, if_false]
      split_ifs <;> linarith

theorem notMem_nbrs_self {G : Graph n} (hs : IsSimple G) (x : Fin n) : x ∉ nbrs G x :=
  fun h => hs _ (mem_filter.1 h).2 (by simp)

/-- Rebuild a realisation of `d` from one of `d - e_x - e_y`, where `y` has minimum positive
entry and `d x + #{d = 0} ≤ n - 1`. -/
theorem exists_realization_of_sub {d : Fin n → ℤ} (h0 : ∀ i, 0 ≤ d i) {x y : Fin n} (hxy : x ≠ y)
    (hy : ∀ v, 1 ≤ d v → d y ≤ d v)
    (hz : d x + ((univ.filter fun v => d v = 0).card : ℤ) ≤ n - 1)
    {G : Graph n} (hG : HasDegSeq G (d - Pi.single x 1 - Pi.single y 1 : Fin n → ℤ)) :
    ∃ G', HasDegSeq G' d := by
  obtain ⟨hs, hd⟩ := hG
  have hdeg : ∀ v, (deg G v : ℤ) = d v - (if v = x then 1 else 0) - if v = y then 1 else 0 := by
    intro v; rw [hd v]; simp [Pi.single_apply]
  by_cases hxyG : s(x, y) ∈ G
  · obtain ⟨z, hz1, hz2⟩ : ∃ z, z ∈ univ \ insert x (nbrs G x) ∧
        z ∉ univ.filter fun v => d v = 0 := by
      apply exists_mem_notMem_of_card_lt_card
      have h1 : (univ \ insert x (nbrs G x)).card = n - (deg G x + 1) := by
        rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin,
          card_insert_of_notMem (notMem_nbrs_self hs x), card_nbrs hs]
      have h2 := hdeg x
      simp only [if_true, hxy, if_false, sub_zero] at h2
      have h3 : deg G x + 1 ≤ n := by
        have := card_le_univ (insert x (nbrs G x))
        rwa [card_insert_of_notMem (notMem_nbrs_self hs x), card_nbrs hs, Fintype.card_fin] at this
      omega
    simp only [mem_sdiff, mem_univ, true_and, mem_insert, nbrs, mem_filter, not_or] at hz1 hz2
    obtain ⟨hzx, hxz⟩ := hz1
    have hz1 : 1 ≤ d z := by have := h0 z; omega
    have hzy : z ≠ y := fun h => hxz (h ▸ hxyG)
    have hxz' : x ∉ nbrs G z := by simp [nbrs, Sym2.eq_swap, hxz]
    obtain ⟨w, hw1, hw2⟩ : ∃ w, w ∈ nbrs G z ∧ w ∉ insert y ((nbrs G y).erase x) := by
      apply exists_mem_notMem_of_card_lt_card
      have hxy' : x ∈ nbrs G y := by simp [nbrs, Sym2.eq_swap, hxyG]
      have h1 := card_insert_le y ((nbrs G y).erase x)
      have h2 := card_erase_add_one hxy'
      rw [card_nbrs hs] at h2
      rw [card_nbrs hs]
      have h3 := hdeg y
      have h4 := hdeg z
      simp only [if_true, hxy.symm, hzx, hzy, if_false, sub_zero] at h3 h4
      have := hy z hz1
      omega
    simp only [nbrs, mem_filter, mem_univ, true_and, mem_insert, mem_erase, not_or, not_and]
      at hw1 hw2
    obtain ⟨hwy, hw2⟩ := hw2
    have hwx : w ≠ x := fun h => by simp [h, Sym2.eq_swap, hxz] at hw1
    have hyw : s(y, w) ∉ G := hw2 hwx
    have hzw : z ≠ w := fun h => hs _ hw1 (by simp [h])
    have hyw' : s(y, w) ∉ G.erase s(z, w) := fun h => hyw (mem_of_mem_erase h)
    have hxz'' : s(x, z) ∉ insert s(y, w) (G.erase s(z, w)) := by
      rw [mem_insert, not_or]
      refine ⟨fun h => ?_, fun h => hxz (mem_of_mem_erase h)⟩
      rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hxy h1
      · exact hwx h1.symm
    refine ⟨insert s(x, z) (insert s(y, w) (G.erase s(z, w))), fun f hf => ?_, fun v => ?_⟩
    · rcases mem_insert.1 hf with rfl | hf
      · simpa [Sym2.mk_isDiag_iff] using Ne.symm hzx
      rcases mem_insert.1 hf with rfl | hf
      · simpa [Sym2.mk_isDiag_iff] using Ne.symm hwy
      · exact hs _ (mem_of_mem_erase hf)
    · rw [deg_insert _ hxz'', deg_insert _ hyw', deg_erase _ hw1, hdeg, ite_mem_sym2 hzw,
        ite_mem_sym2 (Ne.symm hwy), ite_mem_sym2 (Ne.symm hzx)]
      ring
  · refine ⟨insert s(x, y) G, fun f hf => ?_, fun v => ?_⟩
    · rcases mem_insert.1 hf with rfl | hf
      · simpa [Sym2.mk_isDiag_iff] using hxy
      · exact hs _ hf
    · rw [deg_insert _ hxyG, hdeg, ite_mem_sym2 hxy]; ring

theorem exists_max_pos {d : Fin n → ℤ} (h : ∃ i, d i ≠ 0) (h0 : ∀ i, 0 ≤ d i) :
    ∃ x, (∀ v, d v ≤ d x) ∧ 1 ≤ d x := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨x, -, hx⟩ := exists_max_image univ d ⟨i, mem_univ i⟩
  exact ⟨x, fun v => hx v (mem_univ v), by have := hx i (mem_univ i); have := h0 i; omega⟩

/-- Erdős–Gallai sufficiency: Koren's condition, evenness and nonnegativity give a realisation. -/
theorem Koren.exists_realization {d : Fin n → ℤ} (hK : Koren d) (h0 : ∀ i, 0 ≤ d i)
    (hev : Even (∑ i, d i)) : ∃ G, HasDegSeq G d := by
  induction' hm : (∑ i, d i).toNat using Nat.strong_induction_on with m ih generalizing d
  by_cases hd : ∀ i, d i = 0
  · refine ⟨∅, fun f hf => absurd hf (notMem_empty _), fun v => ?_⟩
    simp [deg, hd]
  push Not at hd
  obtain ⟨x, hx, hx1⟩ := exists_max_pos hd h0
  have hn : 1 ≤ n := x.pos
  have hK1 := hK {x} (univ.erase x) (disjoint_singleton_left.2 (notMem_erase x univ))
  rw [sum_singleton, card_singleton, card_erase_of_mem (mem_univ x), card_univ,
    Fintype.card_fin] at hK1
  have hsum : (2 : ℤ) ≤ ∑ i, d i := by
    rw [sum_erase_eq_sub (mem_univ x)] at hK1
    push_cast [Nat.cast_sub hn] at hK1
    omega
  have hpos : (univ.filter fun v => v ≠ x ∧ 1 ≤ d v).Nonempty := by
    by_contra hcon
    rw [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at hcon
    have : ∑ i ∈ univ.erase x, d i = 0 := by
      refine sum_eq_zero fun i hi => ?_
      have := hcon (mem_univ i); have := h0 i
      simp only [mem_erase] at hi
      omega
    rw [this] at hK1
    push_cast [Nat.cast_sub hn] at hK1
    omega
  obtain ⟨y, hy, hymin⟩ := exists_min_image _ d hpos
  simp only [mem_filter, mem_univ, true_and] at hy hymin
  obtain ⟨hyx, hy1⟩ := hy
  have hxy : x ≠ y := hyx.symm
  have hy' : ∀ v, 1 ≤ d v → d y ≤ d v := by
    intro v hv
    by_cases hvx : v = x
    · subst hvx; exact hx y
    · exact hymin v ⟨hvx, hv⟩
  set d' : Fin n → ℤ := d - Pi.single x 1 - Pi.single y 1 with hd'
  have h0' : ∀ i, 0 ≤ d' i := by
    intro i; simp only [hd', Pi.sub_apply, Pi.single_apply]
    have := h0 i
    by_cases hix : i = x
    · subst hix; simp [hxy]; omega
    · by_cases hiy : i = y
      · subst hiy; simp [hix]; omega
      · simp [hix, hiy]; omega
  have hsum' : ∑ i, d' i = ∑ i, d i - 2 := by
    simp only [hd', sum_sub_single, mem_univ, if_true]; ring
  have hev' : Even (∑ i, d' i) := by
    rw [hsum']; exact hev.sub even_two
  obtain ⟨G, hG⟩ := ih ((∑ i, d' i).toNat) (by rw [hsum']; omega)
    (hK.sub h0 hev hxy hx hx1 hy1) h0' hev' rfl
  refine exists_realization_of_sub h0 hxy hy' ?_ hG
  have := hK {x} (univ.filter fun v => d v = 0) ?_
  · rw [sum_singleton, card_singleton] at this
    have h1 : ∑ j ∈ univ.filter (fun v => d v = 0), d j = 0 :=
      sum_eq_zero fun j hj => (mem_filter.1 hj).2
    rw [h1] at this
    push_cast at this
    linarith
  · rw [disjoint_singleton_left, mem_filter]; omega

end LW
