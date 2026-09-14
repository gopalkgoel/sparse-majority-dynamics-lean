import MajorityDynamics.Literature.LWFormal.Defs
import MajorityDynamics.Literature.LWFormal.ErdosGallai

set_option autoImplicit true

/-!
# §2–3: Counting graphs with prescribed edges, switching identities

All allowable pairs (`A = [n]⁽²⁾`).  `NE F d` counts realisations of `d` containing the edge
set `F`; `P`, `Y`, `R` are the edge probability, path probability and ratio functions.
-/

namespace LW

open Finset

variable {n : ℕ}

abbrev Seq (n : ℕ) := Fin n → ℤ

/-- Unit vector `e_a`. -/
def e (a : Fin n) : Seq n := Pi.single a 1

/-- Realisations of `d` containing every edge of `F`. -/
def graphsWith (d : Seq n) (F : Finset (Sym2 (Fin n))) : Finset (Graph n) :=
  (graphs d).filter (F ⊆ ·)

/-- `N_F(d)`. -/
def NE (F : Finset (Sym2 (Fin n))) (d : Seq n) : ℕ := (graphsWith d F).card

/-- `N_{av}(d)`. -/
def Nav (a v : Fin n) (d : Seq n) : ℕ := NE {s(a, v)} d

/-- `N_{\{av,bv\}}(d)`. -/
def Navb (a v b : Fin n) (d : Seq n) : ℕ := NE {s(a, v), s(b, v)} d

/-- `P_{av}(d) = N_{av}(d)/N(d)`. -/
noncomputable def P (a v : Fin n) (d : Seq n) : ℝ := Nav a v d / N d

/-- `Y_{avb}(d) = N_{\{av,bv\}}(d)/N(d)`. -/
noncomputable def Y (a v b : Fin n) (d : Seq n) : ℝ := Navb a v b d / N d

/-- `R_{ab}(d) = N(d - e_a)/N(d - e_b)`. -/
noncomputable def R (a b : Fin n) (d : Seq n) : ℝ := N (d - e a) / N (d - e b)

/-- `M₁(d) = ∑ dᵢ`. -/
def M1 (d : Seq n) : ℤ := ∑ i, d i

/-- `d̄ = M₁/n`. -/
noncomputable def dbar (d : Seq n) : ℝ := (M1 d : ℝ) / n

/-- `μ(d) = d̄/(n-1)`. -/
noncomputable def mu (d : Seq n) : ℝ := dbar d / ((n : ℝ) - 1)

/-- `σ²(d) = n⁻¹ ∑ (dᵢ - d̄)²`. -/
noncomputable def sigma2 (d : Seq n) : ℝ := (∑ i, ((d i : ℝ) - dbar d) ^ 2) / n

/-- Maximum degree `Δ` (negative entries count as `0`). -/
def Delta (d : Seq n) : ℕ := univ.sup fun i => (d i).toNat

theorem NE_le_N (F : Finset (Sym2 (Fin n))) (d : Seq n) : NE F d ≤ N d :=
  card_le_card (filter_subset _ _)

theorem NE_mono {F F' : Finset (Sym2 (Fin n))} (h : F ⊆ F') (d : Seq n) : NE F' d ≤ NE F d :=
  card_le_card fun G => by simp only [graphsWith, mem_filter]; exact fun ⟨h1, h2⟩ => ⟨h1, h.trans h2⟩

theorem Nav_le_N (a v : Fin n) (d : Seq n) : Nav a v d ≤ N d := NE_le_N _ _

theorem Navb_le_Nav (a v b : Fin n) (d : Seq n) : Navb a v b d ≤ Nav a v d :=
  NE_mono (by simp) d

theorem e_apply (a w : Fin n) : e a w = if w = a then 1 else 0 := by
  simp [e, Pi.single_apply]

theorem sub_e_sub_e_apply {a v : Fin n} (hav : a ≠ v) (d : Seq n) (w : Fin n) :
    (d - e a - e v) w = d w - if w ∈ s(a, v) then 1 else 0 := by
  simp only [Pi.sub_apply, e_apply, Sym2.mem_iff]
  by_cases ha : w = a <;> by_cases hv : w = v <;> simp_all

theorem mem_graphsWith {d : Seq n} {F : Finset (Sym2 (Fin n))} {G : Graph n} :
    G ∈ graphsWith d F ↔ HasDegSeq G d ∧ F ⊆ G := by
  simp [graphsWith, graphs]

/-- Edge-removal bijection: realisations of `d` containing `av` and `F` correspond to
realisations of `d - e_a - e_v` containing `F` but not `av`. -/
theorem NE_insert_add {a v : Fin n} (hav : a ≠ v) {F : Finset (Sym2 (Fin n))} (hF : s(a, v) ∉ F)
    (d : Seq n) :
    NE (insert s(a, v) F) d + NE (insert s(a, v) F) (d - e a - e v) = NE F (d - e a - e v) := by
  have key : NE (insert s(a, v) F) d =
      ((graphsWith (d - e a - e v) F).filter (s(a, v) ∉ ·)).card := by
    unfold NE
    refine card_nbij' (·.erase s(a, v)) (insert s(a, v) ·) ?_ ?_ ?_ ?_
    · intro G hG
      rw [mem_coe, mem_graphsWith] at hG
      obtain ⟨⟨hs, hd⟩, hsub⟩ := hG
      have hmem : s(a, v) ∈ G := hsub (mem_insert_self _ _)
      simp only [mem_coe, mem_filter, mem_graphsWith, notMem_erase, not_false_eq_true, and_true]
      refine ⟨⟨fun e he => hs e (mem_of_mem_erase he), fun w => ?_⟩, fun f hf => ?_⟩
      · rw [deg_erase G hmem, hd, sub_e_sub_e_apply hav]
      · exact mem_erase.2 ⟨fun h => hF (h ▸ hf), hsub (mem_insert_of_mem hf)⟩
    · intro G hG
      simp only [mem_coe, mem_filter, mem_graphsWith] at hG
      obtain ⟨⟨⟨hs, hd⟩, hsub⟩, hnot⟩ := hG
      rw [mem_coe, mem_graphsWith]
      refine ⟨⟨fun e he => ?_, fun w => ?_⟩, insert_subset_insert _ hsub⟩
      · rcases mem_insert.1 he with rfl | he
        · simpa [Sym2.mk_isDiag_iff] using hav
        · exact hs e he
      · rw [deg_insert G hnot, hd, sub_e_sub_e_apply hav]; ring
    · intro G hG
      rw [mem_coe, mem_graphsWith] at hG
      exact insert_erase (hG.2 (mem_insert_self _ _))
    · intro G hG
      simp only [mem_coe, mem_filter] at hG
      exact erase_insert hG.2
  have : graphsWith (d - e a - e v) (insert s(a, v) F) =
      (graphsWith (d - e a - e v) F).filter (s(a, v) ∈ ·) := by
    ext G; simp only [mem_graphsWith, mem_filter, insert_subset_iff]; tauto
  rw [key, NE, this, add_comm, card_filter_add_card_filter_not]; rfl

/-- Lemma 2.2: `N_{av}(d) + N_{av}(d - e_a - e_v) = N(d - e_a - e_v)` (`a ≠ v`). -/
theorem lemma_2_2 {a v : Fin n} (hav : a ≠ v) (d : Seq n) :
    Nav a v d + Nav a v (d - e a - e v) = N (d - e a - e v) := by
  have := NE_insert_add hav (notMem_empty _) d
  simpa [Nav, NE, graphsWith, N] using this

theorem Navb_add {a v b : Fin n} (hav : a ≠ v) (hab : a ≠ b) (d : Seq n) :
    Navb a v b d + Navb a v b (d - e a - e v) = Nav b v (d - e a - e v) := by
  have := NE_insert_add hav (F := {s(b, v)}) (by simp [hab, hav]) d
  simpa [Navb, Nav] using this

/-- Erdős–Gallai (Koren's form): an even nonnegative sequence is graphical iff
`∑_{i∈S} dᵢ - ∑_{j∈T} dⱼ ≤ |S|(n-1-|T|)` for all disjoint `S, T`. Classical; sufficiency is used
for Lemma 2.4(a). -/
theorem erdos_gallai (d : Seq n) (h0 : ∀ i, 0 ≤ d i) (hev : Even (M1 d))
    (hEG : ∀ S T : Finset (Fin n), Disjoint S T →
      ∑ i ∈ S, d i - ∑ j ∈ T, d j ≤ S.card * (n - 1 - T.card : ℤ)) :
    0 < N d := by
  obtain ⟨G, hG⟩ := Koren.exists_realization hEG h0 hev
  exact card_pos.2 ⟨G, by simpa [graphs] using hG⟩

/-- Lemma 2.4(a) (robust form): even sequences with `dᵢ ∈ ((1-ε)μn, (1+ε)μn)`, `ε ≤ 1/4`,
`4/n ≤ μ ≤ 1/2`, are graphical. The paper's printed version (absolute error `ε`, `μ < 1 - ε`)
fails near `μ = 1 - ε`; this form is what §6 needs. -/
theorem lemma_2_4a {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 4) (d : Seq n) (h0 : ∀ i, 0 ≤ d i)
    (hev : Even (M1 d)) (μ : ℝ) (hμ0 : 4 ≤ μ * n) (hμ1 : μ ≤ 1 / 2)
    (hd : ∀ i, |μ - (d i : ℝ) / n| < ε * μ) : 0 < N d := by
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hn : (0 : ℝ) < n := by
    rcases hn0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hμ0; linarith
  have hμ : 0 < μ := by nlinarith
  have hn8 : (8 : ℝ) ≤ n := by nlinarith
  refine erdos_gallai d h0 hev fun S T hST => ?_
  have hup : ∀ i, (d i : ℝ) ≤ (1 + ε) * μ * n := by
    intro i
    have := (abs_lt.1 (hd i)).1
    have h2 : (d i : ℝ) / n < (1 + ε) * μ := by linarith
    rw [div_lt_iff₀ hn] at h2
    linarith
  have hlo : ∀ i, (1 - ε) * μ * n ≤ d i := by
    intro i
    have := (abs_lt.1 (hd i)).2
    have h2 : (1 - ε) * μ < (d i : ℝ) / n := by linarith
    rw [lt_div_iff₀ hn] at h2
    linarith
  have hS : (∑ i ∈ S, (d i : ℝ)) ≤ S.card * ((1 + ε) * μ * n) := by
    have := sum_le_card_nsmul S (fun i => (d i : ℝ)) _ fun i _ => hup i
    rwa [nsmul_eq_mul] at this
  have hT : T.card * ((1 - ε) * μ * n) ≤ ∑ j ∈ T, (d j : ℝ) := by
    have := card_nsmul_le_sum T (fun i => (d i : ℝ)) _ fun i _ => hlo i
    rwa [nsmul_eq_mul] at this
  have hst : (S.card : ℝ) + T.card ≤ n := by
    have := card_le_univ (S ∪ T)
    rw [card_union_of_disjoint hST, Fintype.card_fin] at this
    exact_mod_cast this
  have hs0 : (0 : ℝ) ≤ S.card := by positivity
  have ht0 : (0 : ℝ) ≤ T.card := by positivity
  suffices h : (∑ i ∈ S, (d i : ℝ)) - ∑ j ∈ T, (d j : ℝ) ≤ S.card * (n - 1 - T.card) by
    exact_mod_cast h
  set s : ℝ := (S.card : ℝ)
  set t : ℝ := (T.card : ℝ)
  suffices h : s * ((1 + ε) * μ * n) - t * ((1 - ε) * μ * n) ≤ s * (n - 1 - t) by linarith
  rcases le_or_gt ((1 - ε) * μ * n) s with hcase | hcase
  · have h1 : t * (s - (1 - ε) * μ * n) ≤ (n - s) * (s - (1 - ε) * μ * n) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h2 : 1 / 4 * (μ * n * n) ≤ (1 - ε - μ) * (μ * n * n) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith [sq_nonneg (s - μ * n)]
  · have h1 : t * (s - (1 - ε) * μ * n) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 (by linarith)
    have h2 : (1 + ε) * μ * n ≤ n - 1 := by nlinarith
    nlinarith

theorem mem_graphs {d : Seq n} {G : Graph n} : G ∈ graphs d ↔ HasDegSeq G d := by
  simp [graphs]

/-- Double counting: `∑_{b ≠ v} N_{bv}(d) = d_v N(d)`. -/
theorem sum_Nav (d : Seq n) (v : Fin n) :
    ∑ b ∈ univ.erase v, (Nav b v d : ℤ) = d v * N d := by
  have : ∑ b ∈ univ.erase v, Nav b v d = ∑ G ∈ graphs d, deg G v := by
    simp only [Nav, NE, graphsWith, card_filter, singleton_subset_iff]
    rw [sum_comm]
    exact sum_congr rfl fun G hG => by rw [deg_eq_card_nbrs (mem_graphs.1 hG).1, card_filter]
  rw [← Nat.cast_sum, this, Nat.cast_sum]
  rw [sum_congr rfl fun G hG => (mem_graphs.1 hG).2 v, sum_const, N, nsmul_eq_mul, mul_comm]

/-- Proposition 3.1(a). -/
theorem prop_3_1a (d : Seq n) (a v : Fin n) (hav : a ≠ v) (h : 0 < Nav a v d) :
    P a v d = (d v : ℝ) *
      (∑ b ∈ univ.erase v, R b a (d - e v) *
        (1 - P b v (d - e b - e v)) / (1 - P a v (d - e a - e v)))⁻¹ := by
  have hN : 0 < N d := lt_of_lt_of_le h (Nav_le_N a v d)
  have hNa : 0 < N (d - e a - e v) := lt_of_lt_of_le h (by rw [← lemma_2_2 hav]; omega)
  have hNa' : (0 : ℝ) < N (d - e a - e v) := by exact_mod_cast hNa
  have hNav : (0 : ℝ) < Nav a v d := by exact_mod_cast h
  -- each summand equals `N_{bv}(d) / N_{av}(d)`
  have term : ∀ b ∈ univ.erase v, R b a (d - e v) *
      (1 - P b v (d - e b - e v)) / (1 - P a v (d - e a - e v)) = (Nav b v d : ℝ) / Nav a v d := by
    intro b hb
    have hbv : b ≠ v := (mem_erase.1 hb).1
    have h2a : (Nav a v d : ℝ) + Nav a v (d - e a - e v) = N (d - e a - e v) := by
      exact_mod_cast lemma_2_2 hav d
    have h2b : (Nav b v d : ℝ) + Nav b v (d - e b - e v) = N (d - e b - e v) := by
      exact_mod_cast lemma_2_2 hbv d
    have hR : d - e v - e b = d - e b - e v := by abel
    have hR' : d - e v - e a = d - e a - e v := by abel
    unfold R P
    rw [hR, hR', ← h2a, ← h2b]
    rcases Nat.eq_zero_or_pos (N (d - e b - e v)) with hb0 | hb0
    · have h22 := lemma_2_2 hbv d
      have h1 : Nav b v d = 0 := by omega
      have h2 : Nav b v (d - e b - e v) = 0 := by omega
      simp [h1, h2]
    · have hb0' : (0 : ℝ) < Nav b v d + Nav b v (d - e b - e v) := by
        rw [h2b]; exact_mod_cast hb0
      have hNa'' : (0 : ℝ) < Nav a v d + Nav a v (d - e a - e v) := by rw [h2a]; exact hNa'
      rw [one_sub_div hb0'.ne', one_sub_div hNa''.ne', add_sub_cancel_right, add_sub_cancel_right]
      field_simp
  rw [sum_congr rfl term, ← sum_div]
  have hs : (∑ b ∈ univ.erase v, (Nav b v d : ℝ)) = d v * N d := by exact_mod_cast sum_Nav d v
  rw [hs]
  have hdv : (d v : ℝ) ≠ 0 := by
    intro h0
    have := sum_Nav d v
    rw [show (d v : ℝ) = 0 from h0] at hs
    have hpos : (0 : ℝ) < ∑ b ∈ univ.erase v, (Nav b v d : ℝ) :=
      sum_pos' (fun _ _ => by positivity) ⟨a, mem_erase.2 ⟨hav, mem_univ _⟩, hNav⟩
    linarith
  unfold P
  have hN' : (0 : ℝ) < N d := by exact_mod_cast hN
  field_simp

/-- `B(i, j, d')` of (3.2), for `A = [n]⁽²⁾`: `A(i)∖A(j) = {j}`, `A(i)∩A(j) = [n]∖{i,j}`. -/
noncomputable def B (i j : Fin n) (d : Seq n) : ℝ :=
  (P i j d + ∑ v ∈ (univ.erase i).erase j, Y i v j d) / d i

/-- Pairs `(G, v)` with `G ∈ 𝒢(d)`, `av ∈ G`, `v ≠ b`, `bv ∉ G`: the valid degree switchings. -/
def T (d : Seq n) (a b : Fin n) : Finset (Graph n × Fin n) :=
  (graphs d ×ˢ univ).filter fun p => p.2 ≠ b ∧ s(a, p.2) ∈ p.1 ∧ s(b, p.2) ∉ p.1

theorem card_T (d : Seq n) (a b : Fin n) :
    ((T d a b).card : ℤ) = ∑ G ∈ graphs d, ∑ v,
      if v ≠ b ∧ s(a, v) ∈ G ∧ s(b, v) ∉ G then (1 : ℤ) else 0 := by
  rw [T, card_filter, Nat.cast_sum, sum_product]
  simp

/-- Splitting `d_a N(d)` (pairs `(G, v)` with `av ∈ G`) by whether `v = b`, `bv ∈ G`, or neither. -/
theorem J_split (d : Seq n) {a b : Fin n} (hab : a ≠ b) :
    d a * (N d : ℤ) =
      Nav a b d + ∑ v ∈ (univ.erase a).erase b, (Navb a v b d : ℤ) + (T d a b).card := by
  have hJ : d a * (N d : ℤ) = ∑ G ∈ graphs d, ∑ v, if s(a, v) ∈ G then (1 : ℤ) else 0 := by
    rw [N, card_eq_sum_ones, Nat.cast_sum, mul_sum]
    refine sum_congr rfl fun G hG => ?_
    have h := mem_graphs.1 hG
    rw [← h.2 a, deg_eq_card_filter h.1, card_filter]
    push_cast
    simp [Sym2.eq_swap]
  have h1 : (Nav a b d : ℤ) =
      ∑ G ∈ graphs d, ∑ v, if v = b ∧ s(a, v) ∈ G then (1 : ℤ) else 0 := by
    simp only [Nav, NE, graphsWith, card_filter, singleton_subset_iff, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero]
    refine sum_congr rfl fun G _ => ?_
    simp_rw [ite_and]
    rw [sum_ite_eq' univ b]
    simp
  have h2 : ∑ v ∈ (univ.erase a).erase b, (Navb a v b d : ℤ) =
      ∑ G ∈ graphs d, ∑ v, if s(a, v) ∈ G ∧ s(b, v) ∈ G then (1 : ℤ) else 0 := by
    simp only [Navb, NE, graphsWith, card_filter, insert_subset_iff, singleton_subset_iff,
      Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [sum_comm]
    refine sum_congr rfl fun G hG => ?_
    have hs := (mem_graphs.1 hG).1
    rw [sum_erase _ (by simp [show s(b, b) ∉ G from fun h => hs _ h (by simp)]),
      sum_erase _ (by simp [show s(a, a) ∉ G from fun h => hs _ h (by simp)])]
  rw [hJ, h1, h2, card_T, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun G hG => ?_
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun v _ => ?_
  have hs := (mem_graphs.1 hG).1
  by_cases hvb : v = b
  · subst hvb
    have : s(v, v) ∉ G := fun h => hs _ h (by simp)
    simp [this]
  · simp only [hvb, false_and, if_false, zero_add, ne_eq, not_false_eq_true, true_and]
    by_cases h1 : s(a, v) ∈ G <;> by_cases h2 : s(b, v) ∈ G <;> simp [h1, h2]

/-- The degree switching `(G, v) ↦ (G - av + bv, v)`. -/
def sw (a b : Fin n) (p : Graph n × Fin n) : Graph n × Fin n :=
  (insert s(b, p.2) (p.1.erase s(a, p.2)), p.2)

theorem mem_T {d : Seq n} {a b : Fin n} {p : Graph n × Fin n} :
    p ∈ T d a b ↔ HasDegSeq p.1 d ∧ p.2 ≠ b ∧ s(a, p.2) ∈ p.1 ∧ s(b, p.2) ∉ p.1 := by
  simp [T, mem_graphs]

theorem sw_mem {d : Seq n} {a b : Fin n} (hab : a ≠ b) {p : Graph n × Fin n} (hp : p ∈ T d a b) :
    sw a b p ∈ T (d - e a + e b) b a := by
  obtain ⟨G, v⟩ := p
  rw [mem_T] at hp ⊢
  obtain ⟨⟨hs, hd⟩, hvb, hav, hbv⟩ := hp
  have hva : v ≠ a := fun h => hs _ hav (by simp [h])
  have hbv' : s(b, v) ∉ G.erase s(a, v) := fun h => hbv (mem_of_mem_erase h)
  refine ⟨⟨fun f hf => ?_, fun w => ?_⟩, hva, by simp [sw], ?_⟩
  · rcases mem_insert.1 hf with rfl | hf
    · simpa [Sym2.mk_isDiag_iff] using hvb.symm
    · exact hs _ (mem_of_mem_erase hf)
  · simp only [sw]
    rw [deg_insert _ hbv', deg_erase _ hav, hd, ite_mem_sym2 hva.symm, ite_mem_sym2 hvb.symm]
    simp only [Pi.add_apply, Pi.sub_apply, e_apply]
    ring
  · simp only [sw, mem_insert, Sym2.eq_iff, notMem_erase, or_false]
    rintro (⟨rfl, -⟩ | ⟨rfl, rfl⟩)
    · exact hab rfl
    · exact hab rfl

theorem sw_sw {d : Seq n} {a b : Fin n} {p : Graph n × Fin n} (hp : p ∈ T d a b) :
    sw b a (sw a b p) = p := by
  obtain ⟨G, v⟩ := p
  rw [mem_T] at hp
  obtain ⟨-, -, hav, hbv⟩ := hp
  simp only [sw, Prod.mk.injEq, and_true]
  rw [erase_insert (fun h => hbv (mem_of_mem_erase h)), insert_erase hav]

theorem card_T_swap (d : Seq n) {a b : Fin n} (hab : a ≠ b) :
    (T (d - e b) a b).card = (T (d - e a) b a).card := by
  have h1 : d - e b - e a + e b = d - e a := by abel
  have h2 : d - e a - e b + e a = d - e b := by abel
  refine card_nbij' (sw a b) (sw b a) (fun p hp => ?_) (fun p hp => ?_)
    (fun p hp => sw_sw hp) (fun p hp => sw_sw hp)
  · have := sw_mem hab hp; rwa [h1] at this
  · have := sw_mem hab.symm hp; rwa [h2] at this

/-- `1 - B(a, b, d) = |T(d, a, b)| / (d_a N(d))`. -/
theorem one_sub_B (d : Seq n) {a b : Fin n} (hab : a ≠ b) (hda : d a ≠ 0) (hN : 0 < N d) :
    1 - B a b d = (T d a b).card / ((d a : ℝ) * N d) := by
  have h := J_split d hab
  have hN' : (0 : ℝ) < N d := by exact_mod_cast hN
  have hda' : (d a : ℝ) ≠ 0 := by exact_mod_cast hda
  have h' : (d a : ℝ) * N d = Nav a b d + ∑ v ∈ (univ.erase a).erase b, (Navb a v b d : ℝ)
      + (T d a b).card := by exact_mod_cast h
  unfold B P Y
  rw [← sum_div, eq_div_iff (mul_ne_zero hda' hN'.ne')]
  field_simp
  linear_combination h'

/-- Proposition 3.1(b). -/
theorem prop_3_1b (d : Seq n) (a b : Fin n) (hab : a ≠ b) (ha : 0 < N (d - e a))
    (hb : 0 < N (d - e b)) (hB : B b a (d - e a) ≠ 1) :
    R a b d = (d a : ℝ) / d b * (1 - B a b (d - e b)) / (1 - B b a (d - e a)) := by
  have hda : (d - e b) a = d a := by simp [e_apply, hab]
  have hdb : (d - e a) b = d b := by simp [e_apply, hab.symm]
  -- `d_a ≥ 1` and `d_b ≥ 1` since `d - e_a`, `d - e_b` are realisable
  obtain ⟨G, hG⟩ := card_pos.1 ha
  obtain ⟨G', hG'⟩ := card_pos.1 hb
  have hda0 : d a ≠ 0 := by
    have := (mem_graphs.1 hG).2 a; simp [e_apply] at this; omega
  have hdb0 : d b ≠ 0 := by
    have := (mem_graphs.1 hG').2 b; simp [e_apply] at this; omega
  have h1 := one_sub_B (d - e b) hab (hda ▸ hda0) hb
  have h2 := one_sub_B (d - e a) hab.symm (hdb ▸ hdb0) ha
  rw [hda] at h1
  rw [hdb] at h2
  rw [card_T_swap d hab] at h1
  have hT : ((T (d - e a) b a).card : ℝ) ≠ 0 := by
    intro h0; apply hB; rw [h0, zero_div] at h2; linarith
  have ha' : (0 : ℝ) < N (d - e a) := by exact_mod_cast ha
  have hb' : (0 : ℝ) < N (d - e b) := by exact_mod_cast hb
  have hda' : (d a : ℝ) ≠ 0 := by exact_mod_cast hda0
  have hdb' : (d b : ℝ) ≠ 0 := by exact_mod_cast hdb0
  rw [R, h1, h2]
  field_simp

/-- Proposition 3.1(c). -/
theorem prop_3_1c (d : Seq n) (a v b : Fin n) (hav : a ≠ v) (hab : a ≠ b)
    (h : 0 < N (d - e a - e v)) :
    Y a v b d = P a v d * (P b v (d - e a - e v) - Y a v b (d - e a - e v)) /
      (1 - P a v (d - e a - e v)) := by
  have h1 : (Navb a v b d : ℝ) + Navb a v b (d - e a - e v) = Nav b v (d - e a - e v) := by
    exact_mod_cast Navb_add hav hab d
  have h2 : (Nav a v d : ℝ) + Nav a v (d - e a - e v) = N (d - e a - e v) := by
    exact_mod_cast lemma_2_2 hav d
  have hN : (0 : ℝ) < N (d - e a - e v) := by exact_mod_cast h
  unfold Y P
  rw [← h1, ← h2] at *
  rcases Nat.eq_zero_or_pos (Nav a v d) with hx | hx
  · have : Navb a v b d = 0 := Nat.eq_zero_of_le_zero (hx ▸ Navb_le_Nav a v b d)
    simp [hx, this]
  · have hx' : (0 : ℝ) < Nav a v d := by exact_mod_cast hx
    have : (1 : ℝ) - (Nav a v (d - e a - e v) : ℝ) / (Nav a v d + Nav a v (d - e a - e v)) =
        Nav a v d / (Nav a v d + Nav a v (d - e a - e v)) := by
      field_simp; ring
    rw [this]
    field_simp
    ring

theorem deg_le_Delta {G : Graph n} {d : Seq n} (h : HasDegSeq G d) (a : Fin n) :
    deg G a ≤ Delta d := by
  have := h.2 a
  have h2 : deg G a = (d a).toNat := by omega
  rw [h2]; exact Finset.le_sup (f := fun i => (d i).toNat) (mem_univ a)

theorem card_filter_product_mem {G : Graph n} (hs : IsSimple G) (S : Finset (Fin n)) :
    ((S ×ˢ univ).filter fun p : Fin n × Fin n => s(p.1, p.2) ∈ G).card = ∑ x ∈ S, deg G x := by
  rw [card_filter, sum_product]
  refine sum_congr rfl fun x _ => ?_
  rw [← card_nbrs hs, nbrs, card_filter]

theorem card_filter_product_mem' {G : Graph n} (hs : IsSimple G) (S : Finset (Fin n)) :
    ((univ ×ˢ S).filter fun p : Fin n × Fin n => s(p.1, p.2) ∈ G).card = ∑ y ∈ S, deg G y := by
  rw [card_filter, sum_product_right]
  refine sum_congr rfl fun y _ => ?_
  rw [← card_nbrs hs, nbrs, card_filter]
  simp_rw [Sym2.eq_swap]

theorem sum_deg_le {G : Graph n} {d : Seq n} (h : HasDegSeq G d) (a : Fin n) :
    ∑ x ∈ insert a (nbrs G a), deg G x ≤ (Delta d + 1) * Delta d := by
  calc ∑ x ∈ insert a (nbrs G a), deg G x ≤ (insert a (nbrs G a)).card • Delta d :=
        sum_le_card_nsmul _ _ _ fun x _ => deg_le_Delta h x
    _ ≤ (Delta d + 1) * Delta d := by
        rw [smul_eq_mul]
        refine Nat.mul_le_mul_right _ ?_
        calc (insert a (nbrs G a)).card ≤ (nbrs G a).card + 1 := card_insert_le _ _
          _ = deg G a + 1 := by rw [card_nbrs h.1]
          _ ≤ Delta d + 1 := by have := deg_le_Delta h a; omega

/-- Ordered pairs `(x, y)` with `xy ∈ G`. -/
def ordEdges (G : Graph n) : Finset (Fin n × Fin n) := univ.filter fun p => s(p.1, p.2) ∈ G

theorem card_ordEdges {G : Graph n} {d : Seq n} (h : HasDegSeq G d) :
    ((ordEdges G).card : ℤ) = M1 d := by
  rw [ordEdges, ← univ_product_univ, card_filter_product_mem h.1, M1, Nat.cast_sum]
  exact sum_congr rfl fun x _ => h.2 x

/-- Eligible switching pairs `(x, y)`: `xy ∈ G`, `x ∉ {a} ∪ N(a)`, `y ∉ {v} ∪ N(v)`. -/
def elig (G : Graph n) (a v : Fin n) : Finset (Fin n × Fin n) :=
  (ordEdges G).filter fun p => p.1 ≠ a ∧ s(a, p.1) ∉ G ∧ p.2 ≠ v ∧ s(v, p.2) ∉ G

theorem card_elig_ge {G : Graph n} {d : Seq n} (h : HasDegSeq G d) (a v : Fin n) :
    M1 d - 2 * (Delta d + 1) * Delta d ≤ ((elig G a v).card : ℤ) := by
  set Ba := ((insert a (nbrs G a)) ×ˢ (univ : Finset (Fin n))).filter
    (fun p : Fin n × Fin n => s(p.1, p.2) ∈ G) with hBa
  set Bv := ((univ : Finset (Fin n)) ×ˢ (insert v (nbrs G v))).filter
    (fun p : Fin n × Fin n => s(p.1, p.2) ∈ G) with hBv
  have hsub : ordEdges G ⊆ elig G a v ∪ Ba ∪ Bv := by
    intro p hp
    have hp' := (mem_filter.1 hp).2
    simp only [hBa, hBv, elig, mem_union, mem_filter, mem_product, mem_univ, mem_insert, nbrs,
      true_and, and_true]
    by_cases h1 : p.1 = a ∨ s(a, p.1) ∈ G
    · exact Or.inl (Or.inr ⟨h1, hp'⟩)
    by_cases h2 : p.2 = v ∨ s(v, p.2) ∈ G
    · exact Or.inr ⟨h2, hp'⟩
    push Not at h1 h2
    exact Or.inl (Or.inl ⟨hp, h1.1, h1.2, h2.1, h2.2⟩)
  have h1 := card_le_card hsub
  have h2 := card_union_le (elig G a v ∪ Ba) Bv
  have h3 := card_union_le (elig G a v) Ba
  have hca : Ba.card = ∑ x ∈ insert a (nbrs G a), deg G x := card_filter_product_mem h.1 _
  have hcv : Bv.card = ∑ x ∈ insert v (nbrs G v), deg G x := card_filter_product_mem' h.1 _
  have h4 := sum_deg_le h a
  have h5 := sum_deg_le h v
  have h6 := card_ordEdges h
  rw [hca] at h3; rw [hcv] at h2
  have h1' : (M1 d : ℤ) ≤ (elig G a v).card + ∑ x ∈ insert a (nbrs G a), deg G x +
      ∑ x ∈ insert v (nbrs G v), deg G x := by rw [← h6]; exact_mod_cast h1.trans (h2.trans (by omega))
  have h4' : (∑ x ∈ insert a (nbrs G a), deg G x : ℤ) ≤ (Delta d + 1) * Delta d := by exact_mod_cast h4
  have h5' : (∑ x ∈ insert v (nbrs G v), deg G x : ℤ) ≤ (Delta d + 1) * Delta d := by exact_mod_cast h5
  linarith

/-- The switching `G ↦ G - av - xy + ax + vy`. -/
def swE (a v : Fin n) (G : Graph n) (p : Fin n × Fin n) : Graph n :=
  insert s(v, p.2) (insert s(a, p.1) ((G.erase s(a, v)).erase s(p.1, p.2)))

/-- Inverse switching `H ↦ H - ax - vy + xy + av`. -/
def unswE (a v : Fin n) (H : Graph n) (p : Fin n × Fin n) : Graph n :=
  insert s(a, v) (insert s(p.1, p.2) ((H.erase s(v, p.2)).erase s(a, p.1)))

/-- Switchings `(G, (x, y))`: `G ∈ 𝒢(d)`, `av ∈ G`, `(x, y)` eligible. -/
def Sw (d : Seq n) (a v : Fin n) : Finset (Graph n × (Fin n × Fin n)) :=
  ((graphs d).filter (s(a, v) ∈ ·) ×ˢ univ).filter fun q => q.2 ∈ elig q.1 a v

/-- Targets `(H, (x, y))`: `H ∈ 𝒢(d)`, `av ∉ H`, `ax ∈ H`, `vy ∈ H`. -/
def Sw' (d : Seq n) (a v : Fin n) : Finset (Graph n × (Fin n × Fin n)) :=
  ((graphs d).filter (s(a, v) ∉ ·) ×ˢ univ).filter fun q => s(a, q.2.1) ∈ q.1 ∧ s(v, q.2.2) ∈ q.1

theorem mem_Sw {d : Seq n} {a v : Fin n} {q : Graph n × (Fin n × Fin n)} :
    q ∈ Sw d a v ↔ HasDegSeq q.1 d ∧ s(a, v) ∈ q.1 ∧ s(q.2.1, q.2.2) ∈ q.1 ∧
      q.2.1 ≠ a ∧ s(a, q.2.1) ∉ q.1 ∧ q.2.2 ≠ v ∧ s(v, q.2.2) ∉ q.1 := by
  simp [Sw, elig, ordEdges, mem_graphs, and_assoc]

theorem mem_Sw' {d : Seq n} {a v : Fin n} {q : Graph n × (Fin n × Fin n)} :
    q ∈ Sw' d a v ↔ HasDegSeq q.1 d ∧ s(a, v) ∉ q.1 ∧ s(a, q.2.1) ∈ q.1 ∧ s(v, q.2.2) ∈ q.1 := by
  simp [Sw', mem_graphs, and_assoc]

theorem Nav_eq_card_filter (d : Seq n) (a v : Fin n) :
    Nav a v d = ((graphs d).filter (s(a, v) ∈ ·)).card := by
  simp [Nav, NE, graphsWith]

theorem card_Sw_ge (d : Seq n) (a v : Fin n) :
    (Nav a v d : ℤ) * (M1 d - 2 * (Delta d + 1) * Delta d) ≤ (Sw d a v).card := by
  rw [Sw, card_filter, Nat.cast_sum, sum_product]
  have hc : ∀ G : Graph n,
      ∑ p : Fin n × Fin n, ((if (G, p).2 ∈ elig (G, p).1 a v then 1 else 0 : ℕ) : ℤ) =
        (elig G a v).card := by
    intro G; simp
  simp_rw [hc]
  rw [Nav_eq_card_filter, ← nsmul_eq_mul]
  exact card_nsmul_le_sum _ _ _ fun G hG => card_elig_ge (mem_graphs.1 (mem_filter.1 hG).1) a v

theorem card_Sw'_le (d : Seq n) (a v : Fin n) :
    ((Sw' d a v).card : ℤ) ≤ ((N d : ℤ) - Nav a v d) * Delta d ^ 2 := by
  rw [Sw', card_filter, Nat.cast_sum, sum_product]
  have hN : ((N d : ℤ) - Nav a v d) = ((graphs d).filter (s(a, v) ∉ ·)).card := by
    have := card_filter_add_card_filter_not (s := graphs d) (s(a, v) ∈ ·)
    rw [Nav_eq_card_filter, N]; omega
  rw [hN, ← nsmul_eq_mul]
  refine sum_le_card_nsmul _ _ _ fun G hG => ?_
  have h := mem_graphs.1 (mem_filter.1 hG).1
  have : (univ.filter fun p : Fin n × Fin n => s(a, p.1) ∈ G ∧ s(v, p.2) ∈ G) =
      nbrs G a ×ˢ nbrs G v := by ext p; simp [nbrs]
  have hc : ∑ p : Fin n × Fin n,
      ((if s(a, (G, p).2.1) ∈ (G, p).1 ∧ s(v, (G, p).2.2) ∈ (G, p).1 then 1 else 0 : ℕ) : ℤ) =
        (deg G a * deg G v : ℕ) := by
    push_cast
    rw [sum_boole, this, card_product, card_nbrs h.1, card_nbrs h.1]; simp
  rw [hc, sq]
  exact_mod_cast Nat.mul_le_mul (deg_le_Delta h a) (deg_le_Delta h v)

theorem unswE_swE {d : Seq n} {a v : Fin n} (hav : a ≠ v) {q : Graph n × (Fin n × Fin n)}
    (hq : q ∈ Sw d a v) : unswE a v (swE a v q.1 q.2) q.2 = q.1 := by
  obtain ⟨G, x, y⟩ := q
  rw [mem_Sw] at hq
  obtain ⟨⟨hs, -⟩, hav', hxy, hxa, hax, hyv, hvy⟩ := hq
  have hxv : x ≠ v := fun h => hax (h ▸ hav')
  have hya : y ≠ a := fun h => hvy (by rw [h, Sym2.eq_swap]; exact hav')
  simp only [unswE, swE]
  rw [erase_insert, erase_insert, insert_erase, insert_erase hav']
  · rw [mem_erase]; refine ⟨?_, hxy⟩
    simp only [ne_eq, Sym2.eq_iff, not_or, not_and]
    exact ⟨fun h => absurd h hxa, fun h => absurd h hxv⟩
  · exact fun h => hax (mem_of_mem_erase (mem_of_mem_erase h))
  · simp only [mem_insert, Sym2.eq_iff, not_or, not_and]
    refine ⟨⟨fun h => absurd h.symm hav, fun h => absurd h.symm hxv⟩, ?_⟩
    exact fun h => hvy (mem_of_mem_erase (mem_of_mem_erase h))

theorem swE_mem {d : Seq n} {a v : Fin n} (hav : a ≠ v) {q : Graph n × (Fin n × Fin n)}
    (hq : q ∈ Sw d a v) : (swE a v q.1 q.2, q.2) ∈ Sw' d a v := by
  obtain ⟨G, x, y⟩ := q
  rw [mem_Sw] at hq
  rw [mem_Sw']
  obtain ⟨⟨hs, hd⟩, hav', hxy, hxa, hax, hyv, hvy⟩ := hq
  have hxv : x ≠ v := fun h => hax (h ▸ hav')
  have hya : y ≠ a := fun h => hvy (by rw [h, Sym2.eq_swap]; exact hav')
  have hxy' : x ≠ y := fun h => hs _ hxy (by simp [h])
  have hE : s(x, y) ∈ G.erase s(a, v) := by
    rw [mem_erase]; refine ⟨?_, hxy⟩
    simp only [ne_eq, Sym2.eq_iff, not_or, not_and]
    exact ⟨fun h => absurd h hxa, fun h => absurd h hxv⟩
  have hax' : s(a, x) ∉ (G.erase s(a, v)).erase s(x, y) :=
    fun h => hax (mem_of_mem_erase (mem_of_mem_erase h))
  have hvy' : s(v, y) ∉ insert s(a, x) ((G.erase s(a, v)).erase s(x, y)) := by
    simp only [mem_insert, Sym2.eq_iff, not_or, not_and]
    refine ⟨⟨fun h => absurd h.symm hav, fun h => absurd h.symm hxv⟩, ?_⟩
    exact fun h => hvy (mem_of_mem_erase (mem_of_mem_erase h))
  refine ⟨⟨fun f hf => ?_, fun w => ?_⟩, ?_, by simp [swE], by simp [swE]⟩
  · simp only [swE, mem_insert] at hf
    rcases hf with rfl | rfl | hf
    · simpa [Sym2.mk_isDiag_iff] using hyv.symm
    · simpa [Sym2.mk_isDiag_iff] using hxa.symm
    · exact hs _ (mem_of_mem_erase (mem_of_mem_erase hf))
  · simp only [swE]
    rw [deg_insert _ hvy', deg_insert _ hax', deg_erase _ hE, deg_erase _ hav', hd,
      ite_mem_sym2 hav, ite_mem_sym2 hxy', ite_mem_sym2 hxa.symm, ite_mem_sym2 hyv.symm]
    ring
  · simp only [swE, mem_insert, Sym2.eq_iff, not_or, not_and]
    refine ⟨⟨fun h => absurd h hav, fun h => absurd h hya.symm⟩,
      ⟨fun _ => hxv.symm, fun h => absurd h hxa.symm⟩, ?_⟩
    exact fun h => notMem_erase _ _ (mem_of_mem_erase h)

theorem card_Sw_le (d : Seq n) {a v : Fin n} (hav : a ≠ v) : (Sw d a v).card ≤ (Sw' d a v).card := by
  refine card_le_card_of_injOn (fun q => (swE a v q.1 q.2, q.2)) (fun q hq => swE_mem hav hq) ?_
  intro q hq q' hq' heq
  simp only [Prod.mk.injEq] at heq
  have h1 := unswE_swE hav hq
  have h2 := unswE_swE hav hq'
  rw [← heq.1, ← heq.2, h1] at h2
  exact Prod.ext h2 heq.2

/-- Lemma 2.3: the switching bound on `P_{av}`. -/
theorem lemma_2_3 (d : Seq n) (hΔ : 2 * (Delta d + 1) * (Delta d : ℝ) < M1 d) (a v : Fin n) :
    P a v d ≤ (Delta d : ℝ) ^ 2 / ((M1 d : ℝ) * (1 - (Delta d : ℝ) * (Delta d + 2) / M1 d)) := by
  have hΔ0 : (0 : ℝ) ≤ Delta d := by positivity
  have hM : (0 : ℝ) < M1 d := by nlinarith
  have hden : (0 : ℝ) < M1 d - Delta d * (Delta d + 2) := by nlinarith
  have hrhs : (Delta d : ℝ) ^ 2 / ((M1 d : ℝ) * (1 - (Delta d : ℝ) * (Delta d + 2) / M1 d)) =
      Delta d ^ 2 / (M1 d - Delta d * (Delta d + 2)) := by
    rw [mul_one_sub, mul_div_cancel₀ _ hM.ne']
  rw [hrhs]
  by_cases hav : a = v
  · subst hav
    have : Nav a a d = 0 := by
      rw [Nav_eq_card_filter, card_eq_zero, filter_eq_empty_iff]
      exact fun G hG h => (mem_graphs.1 hG).1 _ h (by simp)
    simp [P, this]; positivity
  have key : (Nav a v d : ℝ) * (M1 d - 2 * (Delta d + 1) * Delta d) ≤ (N d - Nav a v d) * Delta d ^ 2 := by
    have := (card_Sw_ge d a v).trans ((Int.ofNat_le.2 (card_Sw_le d hav)).trans (card_Sw'_le d a v))
    exact_mod_cast this
  rcases Nat.eq_zero_or_pos (N d) with hN | hN
  · simp [P, hN]; positivity
  have hN' : (0 : ℝ) < N d := by exact_mod_cast hN
  rw [P, div_le_div_iff₀ hN' hden]
  nlinarith [key]

end LW
