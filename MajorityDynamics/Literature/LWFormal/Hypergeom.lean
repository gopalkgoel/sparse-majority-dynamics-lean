import MajorityDynamics.Literature.LWFormal.Defs

set_option autoImplicit true

/-!
# Hypergeometric tail bounds

For a uniform `k`-subset `S` of `U` and `A ⊆ U`, the law of `X = |S ∩ A|` is hypergeometric with
mean `μ = |A| k / |U|`. Its point probabilities satisfy the Poisson-like ratio bounds
`p_{j+1} ≤ (μ/(j+1)) p_j` for `j ≥ μ` and `p_{j-1} ≤ (j/μ) p_j` for `j ≤ μ`; summing the
resulting geometric series gives `P(|X - μ| ≥ 2L+1) ≤ 2(μ+1) exp(-L²/(2μ))`.
-/

namespace LW

open Finset Real

section prob

variable {X : Type*} (Ω : Finset X)

theorem prob_nonneg (A : X → Prop) [DecidablePred A] : 0 ≤ prob Ω A := by
  unfold prob; positivity

theorem prob_le_one (A : X → Prop) [DecidablePred A] : prob Ω A ≤ 1 := by
  unfold prob
  rcases (Ω.card).eq_zero_or_pos with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]; exact_mod_cast card_filter_le _ _

theorem prob_mono {A B : X → Prop} [DecidablePred A] [DecidablePred B]
    (h : ∀ x ∈ Ω, A x → B x) : prob Ω A ≤ prob Ω B := by
  unfold prob
  rcases (Ω.card).eq_zero_or_pos with h0 | h0
  · simp [h0]
  · have : (Ω.filter A).card ≤ (Ω.filter B).card := card_le_card fun x hx => by
      rw [mem_filter] at hx ⊢; exact ⟨hx.1, h x hx.1 hx.2⟩
    exact div_le_div_of_nonneg_right (by exact_mod_cast this) (by positivity)

theorem prob_or_le [DecidableEq X] (A B : X → Prop) [DecidablePred A] [DecidablePred B] :
    prob Ω (fun x => A x ∨ B x) ≤ prob Ω A + prob Ω B := by
  unfold prob
  rw [← add_div, filter_or]
  exact div_le_div_of_nonneg_right (by exact_mod_cast card_union_le _ _) (by positivity)

theorem prob_not [DecidableEq X] (A : X → Prop) [DecidablePred A] (hΩ : Ω.Nonempty) :
    prob Ω (fun x => ¬ A x) = 1 - prob Ω A := by
  unfold prob
  have h0 : (0 : ℝ) < Ω.card := by exact_mod_cast card_pos.2 hΩ
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq h0.ne', filter_not, ← Nat.cast_add,
    card_sdiff_add_card_eq_card (filter_subset _ _)]

/-- Union bound. -/
theorem prob_exists_le [DecidableEq X] {ι : Type*} (s : Finset ι) (A : ι → X → Prop)
    [∀ i, DecidablePred (A i)] [DecidablePred fun x => ∃ i ∈ s, A i x] :
    prob Ω (fun x => ∃ i ∈ s, A i x) ≤ ∑ i ∈ s, prob Ω (A i) := by
  unfold prob
  rw [← sum_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rw [← Nat.cast_sum]
  have : Ω.filter (fun x => ∃ i ∈ s, A i x) = s.biUnion fun i => Ω.filter (A i) := by
    ext x; simp only [mem_filter, mem_biUnion]; tauto
  rw [this]; exact_mod_cast card_biUnion_le

/-- Decomposing an event on the value of `f` into fibres. -/
theorem prob_mem_eq_sum {Y : Type*} [DecidableEq Y] (f : X → Y) (T : Finset Y) :
    prob Ω (fun x => f x ∈ T) = ∑ t ∈ T, prob Ω (f · = t) := by
  unfold prob
  rw [← sum_div, ← Nat.cast_sum, card_eq_sum_card_fiberwise (f := f) (t := T)
    (s := Ω.filter fun x => f x ∈ T) fun x hx => (mem_filter.1 hx).2]
  congr 1
  congr 1
  refine sum_congr rfl fun t ht => ?_
  congr 1
  ext x; simp only [mem_filter]
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ ‹t ∈ T›⟩, h2⟩

end prob

variable {ι : Type*} [DecidableEq ι]

/-- `C(K,j) C(M,k-j)`: the number of `k`-subsets of a `(K+M)`-set meeting a fixed `K`-subset in
exactly `j` points (for `j ≤ k`). -/
def hp (K M k j : ℕ) : ℝ := (K.choose j : ℝ) * (M.choose (k - j) : ℝ)

theorem hp_nonneg (K M k j : ℕ) : 0 ≤ hp K M k j := by unfold hp; positivity

theorem card_hypFiber (U A : Finset ι) (hA : A ⊆ U) {k j : ℕ} (hj : j ≤ k) :
    (((U.powersetCard k).filter fun S => (S ∩ A).card = j).card : ℝ) =
      hp A.card (U \ A).card k j := by
  unfold hp
  rw [← Nat.cast_mul, ← card_powersetCard, ← card_powersetCard, ← card_product]
  congr 1
  refine card_bij' (fun S _ => (S ∩ A, S \ A)) (fun P _ => P.1 ∪ P.2) ?_ ?_ ?_ ?_
  · intro S hS
    simp only [mem_filter, mem_powersetCard] at hS
    obtain ⟨⟨hSU, hSk⟩, hj'⟩ := hS
    simp only [mem_product, mem_powersetCard]
    refine ⟨⟨inter_subset_right, hj'⟩, sdiff_subset_sdiff hSU le_rfl, ?_⟩
    rw [card_sdiff, hSk, inter_comm, hj']
  · intro P hP
    simp only [mem_product, mem_powersetCard] at hP
    obtain ⟨⟨h1A, h1⟩, h2U, h2⟩ := hP
    have h2A : Disjoint P.2 A := disjoint_of_subset_left h2U sdiff_disjoint
    simp only [mem_filter, mem_powersetCard]
    refine ⟨⟨union_subset (h1A.trans hA) (h2U.trans sdiff_subset), ?_⟩, ?_⟩
    · rw [card_union_of_disjoint (disjoint_of_subset_left h1A h2A.symm), h1, h2]; omega
    · rw [union_inter_distrib_right, inter_eq_left.2 h1A, disjoint_iff_inter_eq_empty.1 h2A,
        union_empty, h1]
  · intro S _; rw [union_comm]; exact sdiff_union_inter S A
  · intro P hP
    simp only [mem_product, mem_powersetCard] at hP
    obtain ⟨⟨h1A, -⟩, h2U, -⟩ := hP
    have h2A : Disjoint P.2 A := disjoint_of_subset_left h2U sdiff_disjoint
    refine Prod.ext ?_ ?_
    · simp only; rw [union_inter_distrib_right, inter_eq_left.2 h1A,
        disjoint_iff_inter_eq_empty.1 h2A, union_empty]
    · simp only; rw [union_sdiff_distrib, sdiff_eq_empty_iff_subset.2 h1A, empty_union,
        Finset.sdiff_eq_self_iff_disjoint.2 h2A]

section ratio

variable {K M k : ℕ} {μ : ℝ}

theorem hp_succ_le (hkM : k ≤ M) (hμ : μ * (K + M) = K * k) (hμ0 : 0 ≤ μ) {j : ℕ} (hj : μ ≤ j)
    (hjk : j + 1 ≤ k) : hp K M k (j + 1) ≤ μ / (j + 1) * hp K M k j := by
  unfold hp
  rcases lt_or_ge K (j + 1) with hK | hK
  · rw [Nat.choose_eq_zero_of_lt hK]
    simp only [Nat.cast_zero, zero_mul]; positivity
  have e1 : (K.choose (j + 1) : ℝ) * (j + 1) = K.choose j * ((K : ℝ) - j) := by
    have h := Nat.choose_succ_right_eq K j
    have h' : ((K.choose (j + 1) * (j + 1) : ℕ) : ℝ) = ((K.choose j * (K - j) : ℕ) : ℝ) := by
      rw [h]
    push_cast [Nat.cast_sub (by omega : j ≤ K)] at h'
    exact h'
  have e2 : (M.choose (k - j) : ℝ) * ((k : ℝ) - j) =
      M.choose (k - (j + 1)) * ((M : ℝ) - ((k : ℝ) - j - 1)) := by
    have h := Nat.choose_succ_right_eq M (k - (j + 1))
    rw [show k - (j + 1) + 1 = k - j by omega] at h
    have h' : ((M.choose (k - j) * (k - j) : ℕ) : ℝ) =
        ((M.choose (k - (j + 1)) * (M - (k - (j + 1))) : ℕ) : ℝ) := by rw [h]
    push_cast [Nat.cast_sub (by omega : j ≤ K), Nat.cast_sub (by omega : j ≤ k),
      Nat.cast_sub (by omega : j + 1 ≤ k), Nat.cast_sub (by omega : k - (j + 1) ≤ M)] at h'
    rw [h']; ring
  have key : ((K : ℝ) - j) * ((k : ℝ) - j) ≤ μ * ((M : ℝ) - ((k : ℝ) - j - 1)) := by
    have hKkj : (0 : ℝ) ≤ (K : ℝ) + k - j := by
      have : (j : ℝ) ≤ K := by exact_mod_cast (by omega : j ≤ K)
      have : (j : ℝ) ≤ k := by exact_mod_cast (by omega : j ≤ k)
      linarith
    nlinarith [mul_nonneg (sub_nonneg.2 hj) hKkj]
  have hden : (0 : ℝ) < (M : ℝ) - ((k : ℝ) - j - 1) := by
    have : ((k : ℝ)) ≤ M := by exact_mod_cast hkM
    linarith
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hj1]
  refine le_of_mul_le_mul_right ?_ hden
  calc (K.choose (j + 1) : ℝ) * (M.choose (k - (j + 1)) : ℝ) * (j + 1) *
        ((M : ℝ) - ((k : ℝ) - j - 1))
      = ((K.choose (j + 1) : ℝ) * (j + 1)) *
          ((M.choose (k - (j + 1)) : ℝ) * ((M : ℝ) - ((k : ℝ) - j - 1))) := by ring
    _ = (K.choose j : ℝ) * (M.choose (k - j) : ℝ) * (((K : ℝ) - j) * ((k : ℝ) - j)) := by
        rw [e1, ← e2]; ring
    _ ≤ (K.choose j : ℝ) * (M.choose (k - j) : ℝ) * (μ * ((M : ℝ) - ((k : ℝ) - j - 1))) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = _ := by ring

theorem hp_pred_le (hkM : k ≤ M) (hμ : μ * (K + M) = K * k) (hN : (0 : ℝ) < K + M) {j : ℕ}
    (hj1 : 1 ≤ j) (hj : (j : ℝ) ≤ μ) : hp K M k (j - 1) ≤ j / μ * hp K M k j := by
  unfold hp
  have hμ0 : 0 < μ := lt_of_lt_of_le (by exact_mod_cast hj1) hj
  have hjK : (j : ℝ) ≤ K := by
    by_contra h; push Not at h
    have : (k : ℝ) ≤ K + M := by
      have : (k : ℝ) ≤ M := by exact_mod_cast hkM
      linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
    nlinarith
  have hjk : (j : ℝ) ≤ k := by
    by_contra h; push Not at h
    have : (K : ℝ) ≤ K + M := by linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
    nlinarith
  have hjK' : j ≤ K := by exact_mod_cast hjK
  have hjk' : j ≤ k := by exact_mod_cast hjk
  have e1 : (K.choose j : ℝ) * j = K.choose (j - 1) * ((K : ℝ) - j + 1) := by
    have h := Nat.choose_succ_right_eq K (j - 1)
    rw [show j - 1 + 1 = j by omega] at h
    have h' : ((K.choose j * j : ℕ) : ℝ) = ((K.choose (j - 1) * (K - (j - 1)) : ℕ) : ℝ) := by
      rw [h]
    push_cast [Nat.cast_sub (by omega : j - 1 ≤ K), Nat.cast_sub hj1] at h'
    rw [h']; ring
  have e2 : (M.choose (k - (j - 1)) : ℝ) * ((k : ℝ) - j + 1) =
      M.choose (k - j) * ((M : ℝ) - ((k : ℝ) - j)) := by
    have h := Nat.choose_succ_right_eq M (k - j)
    rw [show k - j + 1 = k - (j - 1) by omega] at h
    have h' : ((M.choose (k - (j - 1)) * (k - (j - 1)) : ℕ) : ℝ) =
        ((M.choose (k - j) * (M - (k - j)) : ℕ) : ℝ) := by rw [h]
    push_cast [Nat.cast_sub (by omega : j - 1 ≤ k), Nat.cast_sub hj1, Nat.cast_sub hjk',
      Nat.cast_sub (by omega : k - j ≤ M)] at h'
    rw [← h']; ring
  have key : μ * ((M : ℝ) - ((k : ℝ) - j)) ≤ ((K : ℝ) - j + 1) * ((k : ℝ) - j + 1) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hj) (by linarith : (0 : ℝ) ≤ (K : ℝ) + k - j)]
  have hden : (0 : ℝ) < ((K : ℝ) - j + 1) * ((k : ℝ) - j + 1) := by
    apply mul_pos <;> linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hμ0]
  refine le_of_mul_le_mul_right ?_ hden
  calc (K.choose (j - 1) : ℝ) * (M.choose (k - (j - 1)) : ℝ) * μ *
        (((K : ℝ) - j + 1) * ((k : ℝ) - j + 1))
      = μ * (((K.choose (j - 1) : ℝ) * ((K : ℝ) - j + 1)) *
          ((M.choose (k - (j - 1)) : ℝ) * ((k : ℝ) - j + 1))) := by ring
    _ = (K.choose j : ℝ) * (M.choose (k - j) : ℝ) * j * (μ * ((M : ℝ) - ((k : ℝ) - j))) := by
        rw [← e1, e2]; ring
    _ ≤ (K.choose j : ℝ) * (M.choose (k - j) : ℝ) * j *
          (((K : ℝ) - j + 1) * ((k : ℝ) - j + 1)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = _ := by ring

theorem hp_add_le (hkM : k ≤ M) (hμ : μ * (K + M) = K * k) (hμ0 : 0 ≤ μ) {J : ℕ} (hJ : μ ≤ J) :
    ∀ i, J + i ≤ k → hp K M k (J + i) ≤ (μ / (J + 1)) ^ i * hp K M k J := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have h1 := hp_succ_le hkM hμ hμ0 (j := J + i) (by push_cast; linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)])
      (by omega)
    have h2 : μ / ((J + i : ℕ) + 1 : ℝ) ≤ μ / (J + 1) :=
      div_le_div_of_nonneg_left hμ0 (by positivity) (by push_cast; linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)])
    calc hp K M k (J + (i + 1)) = hp K M k (J + i + 1) := by rw [Nat.add_assoc]
      _ ≤ μ / ((J + i : ℕ) + 1 : ℝ) * hp K M k (J + i) := h1
      _ ≤ μ / (J + 1) * ((μ / (J + 1)) ^ i * hp K M k J) :=
          mul_le_mul h2 (ih (by omega)) (hp_nonneg _ _ _ _) (by positivity)
      _ = _ := by ring

theorem hp_sub_le (hkM : k ≤ M) (hμ : μ * (K + M) = K * k) (hN : (0 : ℝ) < K + M) {J : ℕ}
    (hJ : (J : ℝ) ≤ μ)
    (hμ0 : 0 < μ) : ∀ i ≤ J, hp K M k (J - i) ≤ (J / μ) ^ i * hp K M k J := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have h1 := hp_pred_le hkM hμ hN (j := J - i) (by omega)
      (by rw [Nat.cast_sub (by omega)]; linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)])
    have h2 : ((J - i : ℕ) : ℝ) / μ ≤ J / μ :=
      div_le_div_of_nonneg_right (by exact_mod_cast Nat.sub_le J i) hμ0.le
    calc hp K M k (J - (i + 1)) = hp K M k (J - i - 1) := by rw [Nat.sub_sub]
      _ ≤ ((J - i : ℕ) : ℝ) / μ * hp K M k (J - i) := h1
      _ ≤ J / μ * ((J / μ) ^ i * hp K M k J) :=
          mul_le_mul h2 (ih (by omega)) (hp_nonneg _ _ _ _) (by positivity)
      _ = _ := by ring

/-- `(1 - x)^L ≤ exp(-L x)`. -/
theorem one_sub_pow_le_exp {x : ℝ} (hx : x ≤ 1) (L : ℕ) : (1 - x) ^ L ≤ exp (-(L : ℝ) * x) := by
  have h : 1 - x ≤ exp (-x) := by linarith [add_one_le_exp (-x)]
  calc (1 - x) ^ L ≤ exp (-x) ^ L := pow_le_pow_left₀ (by linarith) h L
    _ = exp (-(L : ℝ) * x) := by rw [← exp_nat_mul]; ring_nf

/-- Head bound for the upper tail: `hp(J + 2L) ≤ (μ/(μ+L))^L hp J`. -/
theorem hp_head_upper (hkM : k ≤ M) (hμ : μ * (K + M) = K * k) (hμ0 : 0 ≤ μ) {J : ℕ}
    (hJ : μ ≤ J) (L : ℕ) (hL : J + 2 * L ≤ k) :
    hp K M k (J + 2 * L) ≤ (μ / (μ + L)) ^ L * hp K M k J := by
  have hJL : μ ≤ ((J + L : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg L : (0:ℝ) ≤ L)]
  have h1 := hp_add_le hkM hμ hμ0 hJL L (by omega)
  have h2 := hp_add_le hkM hμ hμ0 hJ L (by omega)
  have hr : μ / (J + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have h3 : hp K M k (J + L) ≤ hp K M k J :=
    h2.trans (by
      calc (μ / (J + 1)) ^ L * hp K M k J ≤ 1 ^ L * hp K M k J :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hr L) (hp_nonneg _ _ _ _)
        _ = _ := by simp)
  have h4 : μ / (((J + L : ℕ) : ℝ) + 1) ≤ μ / (μ + L) := by
    rcases hμ0.lt_or_eq with h | h
    · exact div_le_div_of_nonneg_left hμ0 (by positivity) (by push_cast; linarith)
    · rw [← h]; simp
  calc hp K M k (J + 2 * L) = hp K M k (J + L + L) := by rw [Nat.add_assoc, two_mul]
    _ ≤ (μ / (((J + L : ℕ) : ℝ) + 1)) ^ L * hp K M k (J + L) := h1
    _ ≤ (μ / (μ + L)) ^ L * hp K M k J :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) h4 L) h3 (hp_nonneg _ _ _ _) (by positivity)

/-- Head bound for the lower tail: `hp(J - 2L) ≤ (1 - L/μ)^L hp J`. -/
theorem hp_head_lower (hkM : k ≤ M) (hμ : μ * (K + M) = K * k) (hN : (0 : ℝ) < K + M)
    (hμ0 : 0 < μ) {J : ℕ}
    (hJ : (J : ℝ) ≤ μ) (L : ℕ) (hL : 2 * L ≤ J) :
    hp K M k (J - 2 * L) ≤ (1 - L / μ) ^ L * hp K M k J := by
  have hJL : ((J - L : ℕ) : ℝ) ≤ μ := by
    rw [Nat.cast_sub (by omega)]; linarith [(Nat.cast_nonneg L : (0:ℝ) ≤ L)]
  have h1 := hp_sub_le hkM hμ hN hJL hμ0 L (by omega)
  have h2 := hp_sub_le hkM hμ hN hJ hμ0 L (by omega)
  have hr : (J : ℝ) / μ ≤ 1 := by rw [div_le_one hμ0]; exact hJ
  have h3 : hp K M k (J - L) ≤ hp K M k J :=
    h2.trans (by
      calc ((J : ℝ) / μ) ^ L * hp K M k J ≤ 1 ^ L * hp K M k J :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hr L) (hp_nonneg _ _ _ _)
        _ = _ := by simp)
  have h4 : ((J - L : ℕ) : ℝ) / μ ≤ 1 - L / μ := by
    rw [Nat.cast_sub (by omega), sub_div]; linarith
  have h5 : (0 : ℝ) ≤ 1 - L / μ := by
    have : (L : ℝ) ≤ μ := by
      have : ((L : ℝ)) ≤ J := by exact_mod_cast (by omega : L ≤ J)
      linarith
    rw [sub_nonneg, div_le_one hμ0]; exact this
  calc hp K M k (J - 2 * L) = hp K M k (J - L - L) := by rw [Nat.sub_sub, two_mul]
    _ ≤ (((J - L : ℕ) : ℝ) / μ) ^ L * hp K M k (J - L) := h1
    _ ≤ (1 - L / μ) ^ L * hp K M k J :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) h4 L) h3 (hp_nonneg _ _ _ _) (by positivity)

end ratio

section tail

variable (U A : Finset ι) (k : ℕ)

/-- Hypergeometric tail bound: `P(|X - μ| ≥ 2L+1) ≤ 2(μ+1) exp(-L²/(2μ))`, `μ = |A| k / |U|`. -/
theorem hyp_tail (hA : A ⊆ U) (hk : A.card + k ≤ U.card) {μ : ℝ}
    (hμdef : μ = A.card * k / U.card) (L : ℕ) (hL : 1 ≤ L) (hμ : (2 * L + 1 : ℝ) ≤ μ) :
    prob (U.powersetCard k) (fun S => (2 * L + 1 : ℝ) ≤ |((S ∩ A).card : ℝ) - μ|) ≤
      2 * (μ + 1) * exp (-(L : ℝ) ^ 2 / (2 * μ)) := by
  set K := A.card
  set M := (U \ A).card
  set Ω := U.powersetCard k
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hN : U.card = K + M := by rw [add_comm]; exact (card_sdiff_add_card_eq_card hA).symm
  have hkM : k ≤ M := by omega
  have hNpos : (0 : ℝ) < K + M := by
    have : 0 < U.card := by
      rcases Nat.eq_zero_or_pos U.card with h | h
      · rw [hμdef, h, Nat.cast_zero, div_zero] at hμ; linarith
      · exact h
    rw [hN] at this; exact_mod_cast this
  have hμeq : μ * (K + M) = K * k := by
    rw [hμdef, hN]; push_cast; field_simp
  have hμpos : 0 < μ := by linarith
  have hμk : μ ≤ k := by nlinarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M), (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hD : (0 : ℝ) < Ω.card := by
    rw [card_powersetCard]; exact_mod_cast Nat.choose_pos (by omega)
  have hpt : ∀ j ≤ k, prob Ω (fun S => (S ∩ A).card = j) = hp K M k j / Ω.card := by
    intro j hj; rw [prob, card_hypFiber U A hA hj]
  have hle1 : ∀ j ≤ k, hp K M k j ≤ Ω.card := fun j hj => by
    have := prob_le_one Ω (fun S => (S ∩ A).card = j)
    rwa [hpt j hj, div_le_one hD] at this
  have hXk : ∀ S ∈ Ω, (S ∩ A).card ≤ k := fun S hS => by
    rw [← (mem_powersetCard.1 hS).2]; exact card_le_card inter_subset_left
  set Jp := ⌈μ⌉₊
  set Jm := ⌊μ⌋₊
  have hJp : μ ≤ Jp := Nat.le_ceil μ
  have hJp' : (Jp : ℝ) < μ + 1 := Nat.ceil_lt_add_one hμpos.le
  have hJm : (Jm : ℝ) ≤ μ := Nat.floor_le hμpos.le
  have hJm' : μ < Jm + 1 := Nat.lt_floor_add_one μ
  have h2L : 2 * L ≤ Jm := by
    have : (2 * L : ℝ) ≤ Jm := by linarith
    exact_mod_cast this
  have hJmk : Jm ≤ k := by exact_mod_cast hJm.trans hμk
  have hsplit : prob Ω (fun S => (2 * L + 1 : ℝ) ≤ |((S ∩ A).card : ℝ) - μ|) ≤
      prob Ω (fun S => Jp + 2 * L ≤ (S ∩ A).card) +
        prob Ω (fun S => (S ∩ A).card ≤ Jm - 2 * L) := by
    refine (prob_mono Ω ?_).trans (prob_or_le Ω _ _)
    intro S _ h
    rcases le_abs.1 h with h | h
    · left
      have : ((Jp + 2 * L : ℕ) : ℝ) < (S ∩ A).card := by push_cast; linarith
      exact_mod_cast this.le
    · right
      have : ((S ∩ A).card : ℝ) < ((Jm - 2 * L : ℕ) : ℝ) := by
        rw [Nat.cast_sub h2L]; push_cast; linarith
      exact_mod_cast this.le
  have hup : prob Ω (fun S => Jp + 2 * L ≤ (S ∩ A).card) ≤ (μ + 1) * (μ / (μ + L)) ^ L := by
    rcases lt_or_ge k (Jp + 2 * L) with hk' | hk'
    · have : prob Ω (fun S => Jp + 2 * L ≤ (S ∩ A).card) = 0 := by
        rw [prob, div_eq_zero_iff]; left; norm_cast; rw [card_eq_zero, filter_eq_empty_iff]
        intro S hS h; have := hXk S hS; omega
      rw [this]; positivity
    set j₀ := Jp + 2 * L with hj₀
    have h1 : prob Ω (fun S => j₀ ≤ (S ∩ A).card) =
        prob Ω (fun S => (S ∩ A).card ∈ Ico j₀ (k + 1)) := by
      unfold prob; congr 3; apply filter_congr; intro S hS; rw [mem_Ico]; have := hXk S hS; omega
    rw [h1, prob_mem_eq_sum Ω (fun S => (S ∩ A).card) (Ico j₀ (k + 1)),
      sum_congr rfl fun j hj => hpt j (by rw [mem_Ico] at hj; omega), ← sum_div,
      sum_Ico_eq_sum_range]
    set r := μ / ((j₀ : ℝ) + 1) with hr
    have hr0 : 0 ≤ r := by positivity
    have hj₀μ : μ ≤ (j₀ : ℝ) := by rw [hj₀]; push_cast; linarith
    have hr1 : r < 1 := by rw [hr, div_lt_one (by positivity)]; linarith
    have hsum : ∑ i ∈ range (k + 1 - j₀), hp K M k (j₀ + i) ≤ hp K M k j₀ / (1 - r) := by
      calc ∑ i ∈ range (k + 1 - j₀), hp K M k (j₀ + i)
          ≤ ∑ i ∈ range (k + 1 - j₀), r ^ i * hp K M k j₀ :=
            sum_le_sum fun i hi => hp_add_le hkM hμeq hμpos.le hj₀μ i (by rw [mem_range] at hi; omega)
        _ = (∑ i ∈ range (k + 1 - j₀), r ^ i) * hp K M k j₀ := by rw [sum_mul]
        _ ≤ 1 / (1 - r) * hp K M k j₀ := by
            refine mul_le_mul_of_nonneg_right ?_ (hp_nonneg _ _ _ _)
            have := geom_sum_Ico_le_of_lt_one hr0 hr1 (m := 0) (n := k + 1 - j₀)
            rw [pow_zero] at this; rwa [range_eq_Ico]
        _ = hp K M k j₀ / (1 - r) := by ring
    have hinv : 1 / (1 - r) ≤ μ + 1 := by
      have hj₀1 : (0 : ℝ) < j₀ + 1 := by positivity
      have h1r : 1 - r = ((j₀ : ℝ) + 1 - μ) / (j₀ + 1) := by rw [hr]; field_simp
      rw [h1r, one_div_div, div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg hμpos.le (sub_nonneg.2 hj₀μ)]
    calc (∑ i ∈ range (k + 1 - j₀), hp K M k (j₀ + i)) / Ω.card
        ≤ (hp K M k j₀ / (1 - r)) / Ω.card := div_le_div_of_nonneg_right hsum hD.le
      _ = (1 / (1 - r)) * (hp K M k j₀ / Ω.card) := by ring
      _ ≤ (μ + 1) * ((μ / (μ + L)) ^ L * 1) := by
          refine mul_le_mul hinv ?_ (div_nonneg (hp_nonneg _ _ _ _) hD.le) (by positivity)
          rw [div_le_iff₀ hD, mul_one]
          calc hp K M k j₀ ≤ (μ / (μ + L)) ^ L * hp K M k Jp :=
                hp_head_upper hkM hμeq hμpos.le hJp L hk'
            _ ≤ (μ / (μ + L)) ^ L * Ω.card :=
                mul_le_mul_of_nonneg_left (hle1 Jp (by omega)) (by positivity)
      _ = _ := by ring
  have hLμ : (L : ℝ) ≤ μ := by linarith
  have h5 : (0 : ℝ) ≤ 1 - L / μ := by rw [sub_nonneg, div_le_one hμpos]; exact hLμ
  have hlow : prob Ω (fun S => (S ∩ A).card ≤ Jm - 2 * L) ≤ μ / 2 * (1 - L / μ) ^ L := by
    set j₀ := Jm - 2 * L with hj₀
    have hj₀μ : (j₀ : ℝ) ≤ μ - 2 * L := by rw [hj₀, Nat.cast_sub h2L]; push_cast; linarith
    have h1 : prob Ω (fun S => (S ∩ A).card ≤ j₀) =
        prob Ω (fun S => (S ∩ A).card ∈ range (j₀ + 1)) := by
      unfold prob; congr 3; apply filter_congr; intro S _; rw [mem_range]; omega
    rw [h1, prob_mem_eq_sum Ω (fun S => (S ∩ A).card) (range (j₀ + 1)),
      sum_congr rfl fun j hj => hpt j (by rw [mem_range] at hj; omega), ← sum_div,
      ← sum_range_reflect]
    simp only [Nat.add_sub_cancel]
    set r := (j₀ : ℝ) / μ with hr
    have hr0 : 0 ≤ r := by positivity
    have hr1 : r < 1 := by rw [hr, div_lt_one hμpos]; linarith
    have hsum : ∑ i ∈ range (j₀ + 1), hp K M k (j₀ - i) ≤ hp K M k j₀ / (1 - r) := by
      calc ∑ i ∈ range (j₀ + 1), hp K M k (j₀ - i)
          ≤ ∑ i ∈ range (j₀ + 1), r ^ i * hp K M k j₀ :=
            sum_le_sum fun i hi => hp_sub_le hkM hμeq hNpos (by linarith) hμpos i
              (by rw [mem_range] at hi; omega)
        _ = (∑ i ∈ range (j₀ + 1), r ^ i) * hp K M k j₀ := by rw [sum_mul]
        _ ≤ 1 / (1 - r) * hp K M k j₀ := by
            refine mul_le_mul_of_nonneg_right ?_ (hp_nonneg _ _ _ _)
            have := geom_sum_Ico_le_of_lt_one hr0 hr1 (m := 0) (n := j₀ + 1)
            rw [pow_zero] at this; rwa [range_eq_Ico]
        _ = hp K M k j₀ / (1 - r) := by ring
    have hinv : 1 / (1 - r) ≤ μ / 2 := by
      have h1r : 1 - r = (μ - j₀) / μ := by rw [hr]; field_simp
      rw [h1r, one_div_div]
      exact div_le_div_of_nonneg_left hμpos.le (by norm_num) (by linarith)
    calc (∑ i ∈ range (j₀ + 1), hp K M k (j₀ - i)) / Ω.card
        ≤ (hp K M k j₀ / (1 - r)) / Ω.card := div_le_div_of_nonneg_right hsum hD.le
      _ = (1 / (1 - r)) * (hp K M k j₀ / Ω.card) := by ring
      _ ≤ μ / 2 * ((1 - L / μ) ^ L * 1) := by
          refine mul_le_mul hinv ?_ (div_nonneg (hp_nonneg _ _ _ _) hD.le) (by positivity)
          rw [div_le_iff₀ hD, mul_one]
          calc hp K M k j₀ ≤ (1 - L / μ) ^ L * hp K M k Jm :=
                hp_head_lower hkM hμeq hNpos hμpos hJm L h2L
            _ ≤ (1 - L / μ) ^ L * Ω.card :=
                mul_le_mul_of_nonneg_left (hle1 Jm hJmk) (pow_nonneg h5 L)
      _ = _ := by ring
  have hE1 : (μ / (μ + L)) ^ L ≤ exp (-(L : ℝ) ^ 2 / (2 * μ)) := by
    have hμL : (0 : ℝ) < μ + L := by linarith
    have : μ / (μ + L) = 1 - L / (μ + L) := by
      rw [eq_sub_iff_add_eq, ← add_div, div_self hμL.ne']
    rw [this]
    refine (one_sub_pow_le_exp (by rw [div_le_one (by positivity)]; linarith) L).trans
      (exp_le_exp.2 ?_)
    have : (L : ℝ) ^ 2 / (2 * μ) ≤ L * (L / (μ + L)) := by
      rw [show (L : ℝ) * (L / (μ + L)) = L ^ 2 / (μ + L) by ring]
      exact div_le_div_of_nonneg_left (by positivity) hμL (by linarith)
    rw [neg_mul, neg_div]; exact neg_le_neg this
  have hE2 : (1 - L / μ) ^ L ≤ exp (-(L : ℝ) ^ 2 / (2 * μ)) := by
    refine (one_sub_pow_le_exp (by rw [div_le_one hμpos]; exact hLμ) L).trans (exp_le_exp.2 ?_)
    have : (L : ℝ) ^ 2 / (2 * μ) ≤ L * (L / μ) := by
      rw [show (L : ℝ) * (L / μ) = L ^ 2 / μ by ring]
      exact div_le_div_of_nonneg_left (by positivity) hμpos (by linarith)
    rw [neg_mul, neg_div]; exact neg_le_neg this
  have hE := exp_pos (-(L : ℝ) ^ 2 / (2 * μ))
  calc prob Ω (fun S => (2 * L + 1 : ℝ) ≤ |((S ∩ A).card : ℝ) - μ|)
      ≤ _ := hsplit
    _ ≤ (μ + 1) * (μ / (μ + L)) ^ L + μ / 2 * (1 - L / μ) ^ L := add_le_add hup hlow
    _ ≤ (μ + 1) * exp (-(L : ℝ) ^ 2 / (2 * μ)) + μ / 2 * exp (-(L : ℝ) ^ 2 / (2 * μ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hE1 (by positivity))
          (mul_le_mul_of_nonneg_left hE2 (by positivity))
    _ ≤ 2 * (μ + 1) * exp (-(L : ℝ) ^ 2 / (2 * μ)) := by
        have := mul_pos hμpos hE; linarith

/-- Tail bound in terms of a real threshold `t ≥ 6`: `P(|X - μ| > t) ≤ 2(μ+1) exp(-t²/(32μ))`. -/
theorem hyp_tail' (hA : A ⊆ U) (hk : A.card + k ≤ U.card) {μ : ℝ}
    (hμdef : μ = A.card * k / U.card) {t : ℝ} (ht : 6 ≤ t) (htμ : t ≤ μ) :
    prob (U.powersetCard k) (fun S => t < |((S ∩ A).card : ℝ) - μ|) ≤
      2 * (μ + 1) * exp (-t ^ 2 / (32 * μ)) := by
  set L := ⌊(t - 1) / 2⌋₊
  have hL1 : (L : ℝ) ≤ (t - 1) / 2 := Nat.floor_le (by linarith)
  have hL2 : (t - 1) / 2 < L + 1 := Nat.lt_floor_add_one _
  have hL : 1 ≤ L := by
    have : (1 : ℝ) < L := by linarith
    exact_mod_cast this.le
  have h2L : (2 * L + 1 : ℝ) ≤ t := by linarith
  have hμpos : 0 < μ := by linarith
  refine (prob_mono _ fun S _ h => h2L.trans h.le).trans
    ((hyp_tail U A k hA hk hμdef L hL (h2L.trans htμ)).trans ?_)
  refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (by linarith)
  have h4 : t ≤ 4 * L := by linarith
  have := pow_le_pow_left₀ (by linarith) h4 2
  rw [neg_div, neg_div, neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

end tail

/-- Union bound: if each coordinate deviates by more than `t` with probability `≤ δ`, all `n`
coordinates are within `t` with probability `≥ 1 - nδ`. -/
theorem prob_forall_ge {X : Type*} [DecidableEq X] (Ω : Finset X) (hΩ : Ω.Nonempty) {n : ℕ}
    (f : X → Fin n → ℕ) (μ t δ : ℝ)
    (h : ∀ i, prob Ω (fun x => t < |(f x i : ℝ) - μ|) ≤ δ) :
    1 - n * δ ≤ prob Ω (fun x => ∀ i, |(f x i : ℝ) - μ| ≤ t) := by
  have h1 := prob_not Ω (fun x => ∀ i, |(f x i : ℝ) - μ| ≤ t) hΩ
  have h2 : prob Ω (fun x => ¬ ∀ i, |(f x i : ℝ) - μ| ≤ t) ≤ n * δ := by
    refine ((prob_mono Ω ?_).trans
      (prob_exists_le Ω univ (fun i x => t < |(f x i : ℝ) - μ|))).trans ?_
    · intro x _ hx
      push Not at hx; obtain ⟨i, hi⟩ := hx; exact ⟨i, mem_univ _, hi⟩
    · calc ∑ i ∈ univ, prob Ω (fun x => t < |(f x i : ℝ) - μ|)
          ≤ ∑ _i ∈ (univ : Finset (Fin n)), δ := sum_le_sum fun i _ => h i
        _ = n * δ := by simp
  linarith

/-- The numeric core of Theorem 6.3(a): for `D ≥ (log n)^{2/(2α-1)}`, `t = D^α` is an admissible
threshold and `n · 2(D+1) e^{-t²/(32 D)} ≤ n⁻²`. -/
theorem tail_numeric {α : ℝ} (hα₁ : 1 / 2 < α) (hα₂ : α ≤ 1) {n : ℕ} (hn : 4 ≤ n)
    (hlog : 192 ≤ log n) {D : ℝ} (h1 : log n ^ (2 / (2 * α - 1)) ≤ D) (h2 : D ≤ (n : ℝ) ^ 2) :
    6 ≤ D ^ α ∧ D ^ α ≤ D ∧
      n * (2 * (D + 1) * exp (-(D ^ α) ^ 2 / (32 * D))) ≤ 1 / (n : ℝ) ^ 2 := by
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog1 : 1 ≤ log n := by linarith
  have hexp : 1 ≤ 2 / (2 * α - 1) := by rw [le_div_iff₀ (by linarith)]; linarith
  have hd : 192 ≤ D := by
    have := rpow_le_rpow_of_exponent_le hlog1 hexp
    rw [rpow_one] at this; linarith
  have hd1 : 1 ≤ D := by linarith
  have hd0 : 0 < D := by linarith
  have ht6 : 6 ≤ D ^ α := by
    have h6 : (6 : ℝ) ≤ √D := by
      rw [show (6 : ℝ) = √36 by rw [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    rw [Real.sqrt_eq_rpow] at h6
    exact h6.trans (rpow_le_rpow_of_exponent_le hd1 hα₁.le)
  have htd : D ^ α ≤ D := by
    have := rpow_le_rpow_of_exponent_le hd1 hα₂; rwa [rpow_one] at this
  refine ⟨ht6, htd, ?_⟩
  have hkey : log n ^ 2 * D ≤ (D ^ α) ^ 2 := by
    have h3 : log n ^ 2 ≤ D ^ (2 * α - 1) := by
      have := rpow_le_rpow (by positivity) h1 (by linarith : (0 : ℝ) ≤ 2 * α - 1)
      rwa [← rpow_mul (by linarith), div_mul_cancel₀ _ (by linarith : (2 * α - 1 : ℝ) ≠ 0),
        rpow_two] at this
    calc log n ^ 2 * D ≤ D ^ (2 * α - 1) * D ^ (1 : ℝ) := by
          rw [rpow_one]; exact mul_le_mul_of_nonneg_right h3 hd0.le
      _ = (D ^ α) ^ 2 := by
          rw [← rpow_add hd0, ← rpow_natCast, ← rpow_mul hd0.le]; norm_num; ring_nf
  have hE : exp (-(D ^ α) ^ 2 / (32 * D)) ≤ ((n : ℝ) ^ 6)⁻¹ := by
    calc exp (-(D ^ α) ^ 2 / (32 * D)) ≤ exp (-(6 * log n)) := by
          apply exp_le_exp.2
          rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_right hlog (by positivity : 0 ≤ log n * D)]
      _ = ((n : ℝ) ^ 6)⁻¹ := by
          rw [exp_neg, show (6 : ℝ) * log n = ((6 : ℕ) : ℝ) * log n by norm_num, exp_nat_mul,
            exp_log (by linarith)]
  have h16 : (16 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  calc (n : ℝ) * (2 * (D + 1) * exp (-(D ^ α) ^ 2 / (32 * D)))
      ≤ n * (2 * (2 * (n : ℝ) ^ 2) * ((n : ℝ) ^ 6)⁻¹) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (by linarith) hE (exp_pos _).le (by positivity)) (by positivity)
    _ = 4 / (n : ℝ) ^ 3 := by field_simp; ring
    _ ≤ 1 / (n : ℝ) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg (n : ℝ)]

section moments

variable {ι : Type*} [DecidableEq ι]

theorem sum_ite_subset_powersetCard (A S : Finset ι) (a : ℕ) :
    (∑ P ∈ A.powersetCard a, if P ⊆ S then 1 else 0) = (S ∩ A).card.choose a := by
  rw [← card_filter, ← card_powersetCard]
  congr 1; ext P
  simp only [mem_filter, mem_powersetCard, subset_inter_iff]; tauto

/-- Binomial moments of a uniform `k`-subset: for disjoint `A, B ⊆ U`,
`∑_S C(|S ∩ A|, a) C(|S ∩ B|, b) = C(|A|, a) C(|B|, b) C(|U| - a - b, k - a - b)`. -/
theorem sum_choose_inter_mul (U A B : Finset ι) (hA : A ⊆ U) (hB : B ⊆ U) (hAB : Disjoint A B)
    (a b k : ℕ) (hk : a + b ≤ k) :
    ∑ S ∈ U.powersetCard k, (S ∩ A).card.choose a * (S ∩ B).card.choose b =
      A.card.choose a * B.card.choose b * (U.card - (a + b)).choose (k - (a + b)) := by
  calc ∑ S ∈ U.powersetCard k, (S ∩ A).card.choose a * (S ∩ B).card.choose b
      = ∑ S ∈ U.powersetCard k, ∑ P ∈ A.powersetCard a, ∑ Q ∈ B.powersetCard b,
          if P ∪ Q ⊆ S then 1 else 0 := by
        refine sum_congr rfl fun S _ => ?_
        rw [← sum_ite_subset_powersetCard A S a, ← sum_ite_subset_powersetCard B S b,
          sum_mul_sum]
        refine sum_congr rfl fun P _ => sum_congr rfl fun Q _ => ?_
        by_cases hP : P ⊆ S <;> by_cases hQ : Q ⊆ S <;> simp [hP, hQ, union_subset_iff]
    _ = ∑ P ∈ A.powersetCard a, ∑ Q ∈ B.powersetCard b, ∑ S ∈ U.powersetCard k,
          if P ∪ Q ⊆ S then 1 else 0 := by
        rw [sum_comm]; exact sum_congr rfl fun P _ => sum_comm
    _ = ∑ P ∈ A.powersetCard a, ∑ Q ∈ B.powersetCard b,
          (U.card - (a + b)).choose (k - (a + b)) := by
        refine sum_congr rfl fun P hP => sum_congr rfl fun Q hQ => ?_
        rw [mem_powersetCard] at hP hQ
        have hPQ : (P ∪ Q).card = a + b := by
          rw [card_union_of_disjoint (hAB.mono hP.1 hQ.1), hP.2, hQ.2]
        rw [← card_filter, card_filter_powersetCard_subset _ _ _
          (union_subset (hP.1.trans hA) (hQ.1.trans hB)) (by omega), hPQ]
    _ = _ := by simp only [sum_const, card_powersetCard, smul_eq_mul]; ring

/-- Expectation of `φ ∘ f` as a sum over the pushforward. -/
theorem sum_prob_mul {X Y : Type*} [DecidableEq Y] (Ω : Finset X) (f : X → Y) (T : Finset Y)
    (φ : Y → ℝ) (hf : ∀ x ∈ Ω, f x ∈ T) :
    ∑ t ∈ T, prob Ω (f · = t) * φ t = (∑ x ∈ Ω, φ (f x)) / Ω.card := by
  simp only [prob, div_mul_eq_mul_div, ← sum_div]
  congr 1
  rw [← sum_fiberwise_of_maps_to hf]
  refine sum_congr rfl fun t _ => ?_
  rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_mul, one_mul]
  exact sum_congr rfl fun x hx => by rw [(mem_filter.1 hx).2]

end moments

end LW
