import MajorityDynamics.Literature.LWFormal.Bip.Defs

set_option autoImplicit true

/-!
# §2 for bipartite graphs: counting, switching identities, Proposition 2.6

Allowable pairs `𝒜 = S × T`.  `NE F d` counts realisations of `d` containing the edge set `F`;
`P`, `Y`, `R` are the edge probability, path probability and ratio functions (S-first system).
-/

namespace LW.Bip

open Finset

variable {ℓ n : ℕ}

/-- `e_a` for `a ∈ S`. -/
def eS (a : Fin ℓ) : BSeq ℓ n := (e a, 0)

/-- `e_v` for `v ∈ T`. -/
def eT (v : Fin n) : BSeq ℓ n := (0, e v)

@[simp] theorem eS_fst (a : Fin ℓ) : (eS a : BSeq ℓ n).1 = e a := rfl
@[simp] theorem eS_snd (a : Fin ℓ) : (eS a : BSeq ℓ n).2 = 0 := rfl
@[simp] theorem eT_fst (v : Fin n) : (eT v : BSeq ℓ n).1 = 0 := rfl
@[simp] theorem eT_snd (v : Fin n) : (eT v : BSeq ℓ n).2 = e v := rfl
@[simp] theorem sub_eS_fst (d : BSeq ℓ n) (a : Fin ℓ) : (d - eS a).1 = d.1 - e a := rfl
@[simp] theorem sub_eS_snd (d : BSeq ℓ n) (a : Fin ℓ) : (d - eS a).2 = d.2 := by simp [eS]
@[simp] theorem sub_eT_fst (d : BSeq ℓ n) (v : Fin n) : (d - eT v).1 = d.1 := by simp [eT]
@[simp] theorem sub_eT_snd (d : BSeq ℓ n) (v : Fin n) : (d - eT v).2 = d.2 - e v := rfl
@[simp] theorem add_eS_fst (d : BSeq ℓ n) (a : Fin ℓ) : (d + eS a).1 = d.1 + e a := rfl
@[simp] theorem add_eS_snd (d : BSeq ℓ n) (a : Fin ℓ) : (d + eS a).2 = d.2 := by simp [eS]

theorem sub_eS_sub_eT_comm (d : BSeq ℓ n) (a : Fin ℓ) (v : Fin n) :
    d - eT v - eS a = d - eS a - eT v := by abel

/-- Realisations of `d` containing every edge of `F`. -/
def graphsWith (d : BSeq ℓ n) (F : Finset (Fin ℓ × Fin n)) : Finset (BGraph ℓ n) :=
  (graphs d).filter (F ⊆ ·)

/-- `N_F(d)`. -/
def NE (F : Finset (Fin ℓ × Fin n)) (d : BSeq ℓ n) : ℕ := (graphsWith d F).card

/-- `N_{av}(d)`. -/
def Nav (a : Fin ℓ) (v : Fin n) (d : BSeq ℓ n) : ℕ := NE {(a, v)} d

/-- `N_{\{av,bv\}}(d)`. -/
def Navb (a : Fin ℓ) (v : Fin n) (b : Fin ℓ) (d : BSeq ℓ n) : ℕ := NE {(a, v), (b, v)} d

/-- `P_{av}(d) = N_{av}(d)/N(d)`. -/
noncomputable def P (a : Fin ℓ) (v : Fin n) (d : BSeq ℓ n) : ℝ := Nav a v d / N d

/-- `Y_{avb}(d) = N_{\{av,bv\}}(d)/N(d)`. -/
noncomputable def Y (a : Fin ℓ) (v : Fin n) (b : Fin ℓ) (d : BSeq ℓ n) : ℝ := Navb a v b d / N d

/-- `R_{ab}(d) = N(d - e_a)/N(d - e_b)` for `a, b ∈ S`. -/
noncomputable def R (a b : Fin ℓ) (d : BSeq ℓ n) : ℝ := N (d - eS a) / N (d - eS b)

/-- Maximum degrees on each side (negative entries count as `0`). -/
def DeltaS (d : BSeq ℓ n) : ℕ := univ.sup fun a => (d.1 a).toNat
def DeltaT (d : BSeq ℓ n) : ℕ := univ.sup fun v => (d.2 v).toNat

theorem NE_le_N (F : Finset (Fin ℓ × Fin n)) (d : BSeq ℓ n) : NE F d ≤ N d :=
  card_le_card (filter_subset _ _)

theorem NE_mono {F F' : Finset (Fin ℓ × Fin n)} (h : F ⊆ F') (d : BSeq ℓ n) : NE F' d ≤ NE F d :=
  card_le_card fun G => by simp only [graphsWith, mem_filter]; exact fun ⟨h1, h2⟩ => ⟨h1, h.trans h2⟩

theorem Nav_le_N (a : Fin ℓ) (v : Fin n) (d : BSeq ℓ n) : Nav a v d ≤ N d := NE_le_N _ _

theorem Navb_le_Nav (a : Fin ℓ) (v : Fin n) (b : Fin ℓ) (d : BSeq ℓ n) :
    Navb a v b d ≤ Nav a v d := NE_mono (by simp) d

theorem mem_graphsWith {d : BSeq ℓ n} {F : Finset (Fin ℓ × Fin n)} {G : BGraph ℓ n} :
    G ∈ graphsWith d F ↔ HasDeg G d ∧ F ⊆ G := by
  simp [graphsWith, graphs]

theorem mem_graphs {d : BSeq ℓ n} {G : BGraph ℓ n} : G ∈ graphs d ↔ HasDeg G d := by
  simp [graphs]

theorem hasDeg_erase {G : BGraph ℓ n} {d : BSeq ℓ n} (h : HasDeg G d) {a : Fin ℓ} {v : Fin n}
    (hm : (a, v) ∈ G) : HasDeg (G.erase (a, v)) (d - eS a - eT v) := by
  refine ⟨fun a' => ?_, fun v' => ?_⟩
  · rw [ldeg_erase G hm, h.1]; simp [e_apply, eq_comm]
  · rw [rdeg_erase G hm, h.2]; simp [e_apply, eq_comm]

theorem hasDeg_insert {G : BGraph ℓ n} {d : BSeq ℓ n} {a : Fin ℓ} {v : Fin n}
    (h : HasDeg G (d - eS a - eT v))
    (hm : (a, v) ∉ G) : HasDeg (insert (a, v) G) d := by
  refine ⟨fun a' => ?_, fun v' => ?_⟩
  · rw [ldeg_insert G hm, h.1]; simp [e_apply, eq_comm]
  · rw [rdeg_insert G hm, h.2]; simp [e_apply, eq_comm]

/-- Edge-removal bijection: realisations of `d` containing `av` and `F` correspond to
realisations of `d - e_a - e_v` containing `F` but not `av`. -/
theorem NE_insert_add {a : Fin ℓ} {v : Fin n} {F : Finset (Fin ℓ × Fin n)} (hF : (a, v) ∉ F)
    (d : BSeq ℓ n) :
    NE (insert (a, v) F) d + NE (insert (a, v) F) (d - eS a - eT v) = NE F (d - eS a - eT v) := by
  have key : NE (insert (a, v) F) d =
      ((graphsWith (d - eS a - eT v) F).filter ((a, v) ∉ ·)).card := by
    unfold NE
    refine card_nbij' (·.erase (a, v)) (insert (a, v) ·) ?_ ?_ ?_ ?_
    · intro G hG
      rw [mem_coe, mem_graphsWith] at hG
      obtain ⟨hd, hsub⟩ := hG
      have hmem : (a, v) ∈ G := hsub (mem_insert_self _ _)
      simp only [mem_coe, mem_filter, mem_graphsWith, notMem_erase, not_false_eq_true, and_true]
      exact ⟨hasDeg_erase hd hmem, fun f hf => mem_erase.2 ⟨fun h => hF (h ▸ hf),
        hsub (mem_insert_of_mem hf)⟩⟩
    · intro G hG
      simp only [mem_coe, mem_filter, mem_graphsWith] at hG
      obtain ⟨⟨hd, hsub⟩, hnot⟩ := hG
      rw [mem_coe, mem_graphsWith]
      exact ⟨hasDeg_insert hd hnot, insert_subset_insert _ hsub⟩
    · intro G hG
      rw [mem_coe, mem_graphsWith] at hG
      exact insert_erase (hG.2 (mem_insert_self _ _))
    · intro G hG
      simp only [mem_coe, mem_filter] at hG
      exact erase_insert hG.2
  have : graphsWith (d - eS a - eT v) (insert (a, v) F) =
      (graphsWith (d - eS a - eT v) F).filter ((a, v) ∈ ·) := by
    ext G; simp only [mem_graphsWith, mem_filter, insert_subset_iff]; tauto
  rw [key, NE, this, add_comm, card_filter_add_card_filter_not]; rfl

/-- Lemma 2.2: `N_{av}(d) + N_{av}(d - e_a - e_v) = N(d - e_a - e_v)`. -/
theorem lemma_2_2 (a : Fin ℓ) (v : Fin n) (d : BSeq ℓ n) :
    Nav a v d + Nav a v (d - eS a - eT v) = N (d - eS a - eT v) := by
  have := NE_insert_add (a := a) (v := v) (notMem_empty _) d
  simpa [Nav, NE, graphsWith, N] using this

theorem Navb_add {a b : Fin ℓ} (hab : a ≠ b) (v : Fin n) (d : BSeq ℓ n) :
    Navb a v b d + Navb a v b (d - eS a - eT v) = Nav b v (d - eS a - eT v) := by
  have := NE_insert_add (a := a) (v := v) (F := {(b, v)}) (by simp [hab]) d
  simpa [Navb, Nav] using this

/-- Double counting: `∑_{b ∈ S} N_{bv}(d) = t_v N(d)`. -/
theorem sum_Nav_S (d : BSeq ℓ n) (v : Fin n) :
    ∑ b, (Nav b v d : ℤ) = d.2 v * N d := by
  have : ∑ b, Nav b v d = ∑ G ∈ graphs d, rdeg G v := by
    simp only [Nav, NE, graphsWith, card_filter, singleton_subset_iff]
    rw [sum_comm]
    exact sum_congr rfl fun G hG => by rw [← card_rnbrs, rnbrs, card_filter]
  rw [← Nat.cast_sum, this, Nat.cast_sum]
  rw [sum_congr rfl fun G hG => (mem_graphs.1 hG).2 v, sum_const, N, nsmul_eq_mul, mul_comm]

/-- Double counting: `∑_{v ∈ T} N_{av}(d) = s_a N(d)`. -/
theorem sum_Nav_T (d : BSeq ℓ n) (a : Fin ℓ) :
    ∑ v, (Nav a v d : ℤ) = d.1 a * N d := by
  have : ∑ v, Nav a v d = ∑ G ∈ graphs d, ldeg G a := by
    simp only [Nav, NE, graphsWith, card_filter, singleton_subset_iff]
    rw [sum_comm]
    exact sum_congr rfl fun G hG => by rw [← card_lnbrs, lnbrs, card_filter]
  rw [← Nat.cast_sum, this, Nat.cast_sum]
  rw [sum_congr rfl fun G hG => (mem_graphs.1 hG).1 a, sum_const, N, nsmul_eq_mul, mul_comm]

/-- Proposition 2.6(a). -/
theorem prop_2_6a (d : BSeq ℓ n) (a : Fin ℓ) (v : Fin n) (h : 0 < Nav a v d) :
    P a v d = (d.2 v : ℝ) *
      (∑ b, R b a (d - eT v) *
        (1 - P b v (d - eS b - eT v)) / (1 - P a v (d - eS a - eT v)))⁻¹ := by
  have hN : 0 < N d := lt_of_lt_of_le h (Nav_le_N a v d)
  have hNa : 0 < N (d - eS a - eT v) := lt_of_lt_of_le h (by rw [← lemma_2_2]; omega)
  have hNa' : (0 : ℝ) < N (d - eS a - eT v) := by exact_mod_cast hNa
  have hNav : (0 : ℝ) < Nav a v d := by exact_mod_cast h
  have term : ∀ b, R b a (d - eT v) *
      (1 - P b v (d - eS b - eT v)) / (1 - P a v (d - eS a - eT v)) =
        (Nav b v d : ℝ) / Nav a v d := by
    intro b
    have h2a : (Nav a v d : ℝ) + Nav a v (d - eS a - eT v) = N (d - eS a - eT v) := by
      exact_mod_cast lemma_2_2 a v d
    have h2b : (Nav b v d : ℝ) + Nav b v (d - eS b - eT v) = N (d - eS b - eT v) := by
      exact_mod_cast lemma_2_2 b v d
    unfold R P
    rw [sub_eS_sub_eT_comm, sub_eS_sub_eT_comm, ← h2a, ← h2b]
    rcases Nat.eq_zero_or_pos (N (d - eS b - eT v)) with hb0 | hb0
    · have h22 := lemma_2_2 b v d
      have h1 : Nav b v d = 0 := by omega
      have h2 : Nav b v (d - eS b - eT v) = 0 := by omega
      simp [h1, h2]
    · have hb0' : (0 : ℝ) < Nav b v d + Nav b v (d - eS b - eT v) := by
        rw [h2b]; exact_mod_cast hb0
      have hNa'' : (0 : ℝ) < Nav a v d + Nav a v (d - eS a - eT v) := by rw [h2a]; exact hNa'
      rw [one_sub_div hb0'.ne', one_sub_div hNa''.ne', add_sub_cancel_right, add_sub_cancel_right]
      field_simp
  rw [sum_congr rfl fun b _ => term b, ← sum_div]
  have hs : (∑ b, (Nav b v d : ℝ)) = d.2 v * N d := by exact_mod_cast sum_Nav_S d v
  rw [hs]
  have hdv : (d.2 v : ℝ) ≠ 0 := by
    intro h0
    rw [h0] at hs
    have hpos : (0 : ℝ) < ∑ b, (Nav b v d : ℝ) :=
      sum_pos' (fun _ _ => by positivity) ⟨a, mem_univ _, hNav⟩
    linarith
  unfold P
  have hN' : (0 : ℝ) < N d := by exact_mod_cast hN
  field_simp

/-- `B(a, b, d)` of (2.5): `𝒜(a)∖𝒜(b) = ∅`, `𝒜(a)∩𝒜(b) = T`. -/
noncomputable def B (a b : Fin ℓ) (d : BSeq ℓ n) : ℝ := (∑ v, Y a v b d) / d.1 a

/-- Pairs `(G, v)` with `G ∈ 𝒢(d)`, `av ∈ G`, `bv ∉ G`: the valid degree switchings. -/
def T (d : BSeq ℓ n) (a b : Fin ℓ) : Finset (BGraph ℓ n × Fin n) :=
  (graphs d ×ˢ univ).filter fun p => (a, p.2) ∈ p.1 ∧ (b, p.2) ∉ p.1

theorem card_T (d : BSeq ℓ n) (a b : Fin ℓ) :
    ((T d a b).card : ℤ) = ∑ G ∈ graphs d, ∑ v,
      if (a, v) ∈ G ∧ (b, v) ∉ G then (1 : ℤ) else 0 := by
  rw [T, card_filter, Nat.cast_sum, sum_product]
  simp

/-- Splitting `s_a N(d)` (pairs `(G, v)` with `av ∈ G`) by whether `bv ∈ G`. -/
theorem J_split (d : BSeq ℓ n) (a b : Fin ℓ) :
    d.1 a * (N d : ℤ) = ∑ v, (Navb a v b d : ℤ) + (T d a b).card := by
  have hJ : d.1 a * (N d : ℤ) = ∑ G ∈ graphs d, ∑ v, if (a, v) ∈ G then (1 : ℤ) else 0 := by
    rw [N, card_eq_sum_ones, Nat.cast_sum, mul_sum]
    refine sum_congr rfl fun G hG => ?_
    have h := mem_graphs.1 hG
    rw [← h.1 a, ← card_lnbrs, lnbrs, card_filter]
    push_cast
    simp
  have h2 : ∑ v, (Navb a v b d : ℤ) =
      ∑ G ∈ graphs d, ∑ v, if (a, v) ∈ G ∧ (b, v) ∈ G then (1 : ℤ) else 0 := by
    simp only [Navb, NE, graphsWith, card_filter, insert_subset_iff, singleton_subset_iff,
      Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [sum_comm]
  rw [hJ, h2, card_T, ← sum_add_distrib]
  refine sum_congr rfl fun G hG => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun v _ => ?_
  by_cases h1 : (a, v) ∈ G <;> by_cases h2 : (b, v) ∈ G <;> simp [h1, h2]

/-- The degree switching `(G, v) ↦ (G - av + bv, v)`. -/
def sw (a b : Fin ℓ) (p : BGraph ℓ n × Fin n) : BGraph ℓ n × Fin n :=
  (insert (b, p.2) (p.1.erase (a, p.2)), p.2)

theorem mem_T {d : BSeq ℓ n} {a b : Fin ℓ} {p : BGraph ℓ n × Fin n} :
    p ∈ T d a b ↔ HasDeg p.1 d ∧ (a, p.2) ∈ p.1 ∧ (b, p.2) ∉ p.1 := by
  simp [T, mem_graphs]

theorem sw_mem {d : BSeq ℓ n} {a b : Fin ℓ} (hab : a ≠ b) {p : BGraph ℓ n × Fin n}
    (hp : p ∈ T d a b) : sw a b p ∈ T (d - eS a + eS b) b a := by
  obtain ⟨G, v⟩ := p
  rw [mem_T] at hp ⊢
  obtain ⟨hd, hav, hbv⟩ := hp
  have hbv' : (b, v) ∉ G.erase (a, v) := fun h => hbv (mem_of_mem_erase h)
  refine ⟨⟨fun a' => ?_, fun v' => ?_⟩, by simp [sw], ?_⟩
  · simp only [sw]
    rw [ldeg_insert _ hbv', ldeg_erase _ hav, hd.1]
    simp [e_apply, eq_comm]
  · simp only [sw]
    rw [rdeg_insert _ hbv', rdeg_erase _ hav, hd.2]
    simp
  · simp only [sw, mem_insert, Prod.mk.injEq, notMem_erase, or_false, and_true]
    exact hab

theorem sw_sw {d : BSeq ℓ n} {a b : Fin ℓ} {p : BGraph ℓ n × Fin n} (hp : p ∈ T d a b) :
    sw b a (sw a b p) = p := by
  obtain ⟨G, v⟩ := p
  rw [mem_T] at hp
  obtain ⟨-, hav, hbv⟩ := hp
  simp only [sw, Prod.mk.injEq, and_true]
  rw [erase_insert (fun h => hbv (mem_of_mem_erase h)), insert_erase hav]

theorem card_T_swap (d : BSeq ℓ n) {a b : Fin ℓ} (hab : a ≠ b) :
    (T (d - eS b) a b).card = (T (d - eS a) b a).card := by
  have h1 : d - eS b - eS a + eS b = d - eS a := by abel
  have h2 : d - eS a - eS b + eS a = d - eS b := by abel
  refine card_nbij' (sw a b) (sw b a) (fun p hp => ?_) (fun p hp => ?_)
    (fun p hp => sw_sw hp) (fun p hp => sw_sw hp)
  · have := sw_mem hab hp; rwa [h1] at this
  · have := sw_mem hab.symm hp; rwa [h2] at this

/-- `1 - B(a, b, d) = |T(d, a, b)| / (s_a N(d))`. -/
theorem one_sub_B (d : BSeq ℓ n) (a b : Fin ℓ) (hda : d.1 a ≠ 0) (hN : 0 < N d) :
    1 - B a b d = (T d a b).card / ((d.1 a : ℝ) * N d) := by
  have h := J_split d a b
  have hN' : (0 : ℝ) < N d := by exact_mod_cast hN
  have hda' : (d.1 a : ℝ) ≠ 0 := by exact_mod_cast hda
  have h' : (d.1 a : ℝ) * N d = ∑ v, (Navb a v b d : ℝ) + (T d a b).card := by exact_mod_cast h
  unfold B Y
  rw [← sum_div, eq_div_iff (mul_ne_zero hda' hN'.ne')]
  field_simp
  linear_combination h'

/-- Proposition 2.6(b). -/
theorem prop_2_6b (d : BSeq ℓ n) {a b : Fin ℓ} (hab : a ≠ b) (ha : 0 < N (d - eS a))
    (hb : 0 < N (d - eS b)) (hB : B b a (d - eS a) ≠ 1) :
    R a b d = (d.1 a : ℝ) / d.1 b * (1 - B a b (d - eS b)) / (1 - B b a (d - eS a)) := by
  have hda : (d - eS b).1 a = d.1 a := by simp [e_apply, hab]
  have hdb : (d - eS a).1 b = d.1 b := by simp [e_apply, hab.symm]
  obtain ⟨G, hG⟩ := card_pos.1 ha
  obtain ⟨G', hG'⟩ := card_pos.1 hb
  have hda0 : d.1 a ≠ 0 := by
    have := (mem_graphs.1 hG).1 a; simp [e_apply] at this; omega
  have hdb0 : d.1 b ≠ 0 := by
    have := (mem_graphs.1 hG').1 b; simp [e_apply] at this; omega
  have h1 := one_sub_B (d - eS b) a b (hda ▸ hda0) hb
  have h2 := one_sub_B (d - eS a) b a (hdb ▸ hdb0) ha
  rw [hda] at h1
  rw [hdb] at h2
  rw [card_T_swap d hab] at h1
  have hT : ((T (d - eS a) b a).card : ℝ) ≠ 0 := by
    intro h0; apply hB; rw [h0, zero_div] at h2; linarith
  have ha' : (0 : ℝ) < N (d - eS a) := by exact_mod_cast ha
  have hb' : (0 : ℝ) < N (d - eS b) := by exact_mod_cast hb
  have hda' : (d.1 a : ℝ) ≠ 0 := by exact_mod_cast hda0
  have hdb' : (d.1 b : ℝ) ≠ 0 := by exact_mod_cast hdb0
  rw [R, h1, h2]
  field_simp

/-- Proposition 2.6(c). -/
theorem prop_2_6c (d : BSeq ℓ n) (a : Fin ℓ) (v : Fin n) {b : Fin ℓ} (hab : a ≠ b)
    (h : 0 < N (d - eS a - eT v)) :
    Y a v b d = P a v d * (P b v (d - eS a - eT v) - Y a v b (d - eS a - eT v)) /
      (1 - P a v (d - eS a - eT v)) := by
  have h1 : (Navb a v b d : ℝ) + Navb a v b (d - eS a - eT v) = Nav b v (d - eS a - eT v) := by
    exact_mod_cast Navb_add hab v d
  have h2 : (Nav a v d : ℝ) + Nav a v (d - eS a - eT v) = N (d - eS a - eT v) := by
    exact_mod_cast lemma_2_2 a v d
  have hN : (0 : ℝ) < N (d - eS a - eT v) := by exact_mod_cast h
  unfold Y P
  rw [← h1, ← h2] at *
  rcases Nat.eq_zero_or_pos (Nav a v d) with hx | hx
  · have : Navb a v b d = 0 := Nat.eq_zero_of_le_zero (hx ▸ Navb_le_Nav a v b d)
    simp [hx, this]
  · have hx' : (0 : ℝ) < Nav a v d := by exact_mod_cast hx
    have : (1 : ℝ) - (Nav a v (d - eS a - eT v) : ℝ) /
        (Nav a v d + Nav a v (d - eS a - eT v)) =
        Nav a v d / (Nav a v d + Nav a v (d - eS a - eT v)) := by
      field_simp; ring
    rw [this]
    field_simp
    ring

/-! ### Lemma 2.3: the switching bound -/

theorem ldeg_le_DeltaS {G : BGraph ℓ n} {d : BSeq ℓ n} (h : HasDeg G d) (a : Fin ℓ) :
    ldeg G a ≤ DeltaS d := by
  have := h.1 a
  have h2 : ldeg G a = (d.1 a).toNat := by omega
  rw [h2]; exact Finset.le_sup (f := fun i => (d.1 i).toNat) (mem_univ a)

theorem rdeg_le_DeltaT {G : BGraph ℓ n} {d : BSeq ℓ n} (h : HasDeg G d) (v : Fin n) :
    rdeg G v ≤ DeltaT d := by
  have := h.2 v
  have h2 : rdeg G v = (d.2 v).toNat := by omega
  rw [h2]; exact Finset.le_sup (f := fun i => (d.2 i).toNat) (mem_univ v)

theorem card_filter_fst_mem (G : BGraph ℓ n) (A : Finset (Fin ℓ)) :
    (G.filter fun p => p.1 ∈ A).card = ∑ x ∈ A, ldeg G x := by
  unfold ldeg
  rw [card_eq_sum_card_fiberwise (s := G.filter fun p => p.1 ∈ A) (f := Prod.fst) (t := A)
    (fun p hp => (mem_filter.1 hp).2)]
  exact sum_congr rfl fun x hx => by
    congr 1; ext p; simp only [mem_filter]; constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ hx⟩, h2⟩

theorem card_filter_snd_mem (G : BGraph ℓ n) (V : Finset (Fin n)) :
    (G.filter fun p => p.2 ∈ V).card = ∑ y ∈ V, rdeg G y := by
  unfold rdeg
  rw [card_eq_sum_card_fiberwise (s := G.filter fun p => p.2 ∈ V) (f := Prod.snd) (t := V)
    (fun p hp => (mem_filter.1 hp).2)]
  exact sum_congr rfl fun y hy => by
    congr 1; ext p; simp only [mem_filter]; constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ hy⟩, h2⟩

/-- `|G| = ∑_a s_a` for `G ∈ 𝒢(d)`. -/
theorem card_eq_M1 {G : BGraph ℓ n} {d : BSeq ℓ n} (h : HasDeg G d) : (G.card : ℤ) = M1 d.1 := by
  have := card_filter_fst_mem G univ
  simp only [mem_univ, filter_true_of_mem, implies_true] at this
  rw [this, M1, Nat.cast_sum]
  exact sum_congr rfl fun x _ => h.1 x

theorem sum_ldeg_le {G : BGraph ℓ n} {d : BSeq ℓ n} (h : HasDeg G d) (v : Fin n) :
    ∑ x ∈ rnbrs G v, ldeg G x ≤ DeltaT d * DeltaS d := by
  calc ∑ x ∈ rnbrs G v, ldeg G x ≤ (rnbrs G v).card • DeltaS d :=
        sum_le_card_nsmul _ _ _ fun x _ => ldeg_le_DeltaS h x
    _ ≤ DeltaT d * DeltaS d := by
        rw [smul_eq_mul, card_rnbrs]; exact Nat.mul_le_mul_right _ (rdeg_le_DeltaT h v)

theorem sum_rdeg_le {G : BGraph ℓ n} {d : BSeq ℓ n} (h : HasDeg G d) (a : Fin ℓ) :
    ∑ y ∈ lnbrs G a, rdeg G y ≤ DeltaS d * DeltaT d := by
  calc ∑ y ∈ lnbrs G a, rdeg G y ≤ (lnbrs G a).card • DeltaT d :=
        sum_le_card_nsmul _ _ _ fun y _ => rdeg_le_DeltaT h y
    _ ≤ DeltaS d * DeltaT d := by
        rw [smul_eq_mul, card_lnbrs]; exact Nat.mul_le_mul_right _ (ldeg_le_DeltaS h a)

/-- Eligible switching edges `xy ∈ G`: `x ∉ N(v)`, `y ∉ N(a)`. -/
def elig (G : BGraph ℓ n) (a : Fin ℓ) (v : Fin n) : Finset (Fin ℓ × Fin n) :=
  G.filter fun p => (p.1, v) ∉ G ∧ (a, p.2) ∉ G

theorem card_elig_ge {G : BGraph ℓ n} {d : BSeq ℓ n} (h : HasDeg G d) (a : Fin ℓ) (v : Fin n) :
    M1 d.1 - 2 * (DeltaS d * DeltaT d) ≤ ((elig G a v).card : ℤ) := by
  set Bv := G.filter fun p : Fin ℓ × Fin n => p.1 ∈ rnbrs G v with hBv
  set Ba := G.filter fun p : Fin ℓ × Fin n => p.2 ∈ lnbrs G a with hBa
  have hsub : G ⊆ elig G a v ∪ Bv ∪ Ba := by
    intro p hp
    simp only [hBa, hBv, elig, mem_union, mem_filter, rnbrs, lnbrs, mem_univ, true_and]
    by_cases h1 : (p.1, v) ∈ G
    · exact Or.inl (Or.inr ⟨hp, h1⟩)
    by_cases h2 : (a, p.2) ∈ G
    · exact Or.inr ⟨hp, h2⟩
    exact Or.inl (Or.inl ⟨hp, h1, h2⟩)
  have h1 := card_le_card hsub
  have h2 := card_union_le (elig G a v ∪ Bv) Ba
  have h3 := card_union_le (elig G a v) Bv
  have hcv : Bv.card = ∑ x ∈ rnbrs G v, ldeg G x := card_filter_fst_mem G _
  have hca : Ba.card = ∑ y ∈ lnbrs G a, rdeg G y := card_filter_snd_mem G _
  have h4 := sum_ldeg_le h v
  have h5 := sum_rdeg_le h a
  have h6 := card_eq_M1 h
  rw [hcv] at h3; rw [hca] at h2
  have h1' : (M1 d.1 : ℤ) ≤ (elig G a v).card + ∑ x ∈ rnbrs G v, ldeg G x +
      ∑ y ∈ lnbrs G a, rdeg G y := by
    rw [← h6]; exact_mod_cast h1.trans (h2.trans (by omega))
  have h4' : (∑ x ∈ rnbrs G v, ldeg G x : ℤ) ≤ DeltaT d * DeltaS d := by exact_mod_cast h4
  have h5' : (∑ y ∈ lnbrs G a, rdeg G y : ℤ) ≤ DeltaS d * DeltaT d := by exact_mod_cast h5
  linarith

/-- The switching `G ↦ G - av - xy + ay + xv`. -/
def swE (a : Fin ℓ) (v : Fin n) (G : BGraph ℓ n) (p : Fin ℓ × Fin n) : BGraph ℓ n :=
  insert (p.1, v) (insert (a, p.2) ((G.erase (a, v)).erase p))

/-- Inverse switching `H ↦ H - ay - xv + xy + av`. -/
def unswE (a : Fin ℓ) (v : Fin n) (H : BGraph ℓ n) (p : Fin ℓ × Fin n) : BGraph ℓ n :=
  insert (a, v) (insert p ((H.erase (p.1, v)).erase (a, p.2)))

/-- Switchings `(G, (x, y))`: `G ∈ 𝒢(d)`, `av ∈ G`, `(x, y)` eligible. -/
def Sw (d : BSeq ℓ n) (a : Fin ℓ) (v : Fin n) : Finset (BGraph ℓ n × (Fin ℓ × Fin n)) :=
  ((graphs d).filter ((a, v) ∈ ·) ×ˢ univ).filter fun q => q.2 ∈ elig q.1 a v

/-- Targets `(H, (x, y))`: `H ∈ 𝒢(d)`, `av ∉ H`, `ay ∈ H`, `xv ∈ H`. -/
def Sw' (d : BSeq ℓ n) (a : Fin ℓ) (v : Fin n) : Finset (BGraph ℓ n × (Fin ℓ × Fin n)) :=
  ((graphs d).filter ((a, v) ∉ ·) ×ˢ univ).filter fun q => (a, q.2.2) ∈ q.1 ∧ (q.2.1, v) ∈ q.1

theorem mem_Sw {d : BSeq ℓ n} {a : Fin ℓ} {v : Fin n} {q : BGraph ℓ n × (Fin ℓ × Fin n)} :
    q ∈ Sw d a v ↔ HasDeg q.1 d ∧ (a, v) ∈ q.1 ∧ q.2 ∈ q.1 ∧
      (q.2.1, v) ∉ q.1 ∧ (a, q.2.2) ∉ q.1 := by
  simp [Sw, elig, mem_graphs, and_assoc]

theorem mem_Sw' {d : BSeq ℓ n} {a : Fin ℓ} {v : Fin n} {q : BGraph ℓ n × (Fin ℓ × Fin n)} :
    q ∈ Sw' d a v ↔ HasDeg q.1 d ∧ (a, v) ∉ q.1 ∧ (a, q.2.2) ∈ q.1 ∧ (q.2.1, v) ∈ q.1 := by
  simp [Sw', mem_graphs, and_assoc]

theorem Nav_eq_card_filter (d : BSeq ℓ n) (a : Fin ℓ) (v : Fin n) :
    Nav a v d = ((graphs d).filter ((a, v) ∈ ·)).card := by
  simp [Nav, NE, graphsWith]

theorem card_Sw_ge (d : BSeq ℓ n) (a : Fin ℓ) (v : Fin n) :
    (Nav a v d : ℤ) * (M1 d.1 - 2 * (DeltaS d * DeltaT d)) ≤ (Sw d a v).card := by
  rw [Sw, card_filter, Nat.cast_sum, sum_product]
  have hc : ∀ G : BGraph ℓ n,
      ∑ p : Fin ℓ × Fin n, ((if (G, p).2 ∈ elig (G, p).1 a v then 1 else 0 : ℕ) : ℤ) =
        (elig G a v).card := by
    intro G; simp
  simp_rw [hc]
  rw [Nav_eq_card_filter, ← nsmul_eq_mul]
  exact card_nsmul_le_sum _ _ _ fun G hG => card_elig_ge (mem_graphs.1 (mem_filter.1 hG).1) a v

theorem card_Sw'_le (d : BSeq ℓ n) (a : Fin ℓ) (v : Fin n) :
    ((Sw' d a v).card : ℤ) ≤ ((N d : ℤ) - Nav a v d) * (DeltaS d * DeltaT d) := by
  rw [Sw', card_filter, Nat.cast_sum, sum_product]
  have hN : ((N d : ℤ) - Nav a v d) = ((graphs d).filter ((a, v) ∉ ·)).card := by
    have := card_filter_add_card_filter_not (s := graphs d) ((a, v) ∈ ·)
    rw [Nav_eq_card_filter, N]; omega
  rw [hN, ← nsmul_eq_mul]
  refine sum_le_card_nsmul _ _ _ fun G hG => ?_
  have h := mem_graphs.1 (mem_filter.1 hG).1
  have : (univ.filter fun p : Fin ℓ × Fin n => (a, p.2) ∈ G ∧ (p.1, v) ∈ G) =
      rnbrs G v ×ˢ lnbrs G a := by ext p; simp [rnbrs, lnbrs, and_comm]
  have hc : ∑ p : Fin ℓ × Fin n,
      ((if (a, (G, p).2.2) ∈ (G, p).1 ∧ ((G, p).2.1, v) ∈ (G, p).1 then 1 else 0 : ℕ) : ℤ) =
        (rdeg G v * ldeg G a : ℕ) := by
    push_cast
    rw [sum_boole, this, card_product, card_rnbrs, card_lnbrs]; simp
  rw [hc]
  exact_mod_cast (Nat.mul_le_mul (rdeg_le_DeltaT h v) (ldeg_le_DeltaS h a)).trans_eq
    (Nat.mul_comm _ _)

theorem unswE_swE {d : BSeq ℓ n} {a : Fin ℓ} {v : Fin n} {q : BGraph ℓ n × (Fin ℓ × Fin n)}
    (hq : q ∈ Sw d a v) : unswE a v (swE a v q.1 q.2) q.2 = q.1 := by
  obtain ⟨G, x, y⟩ := q
  rw [mem_Sw] at hq
  obtain ⟨-, hav, hxy, hxv, hay⟩ := hq
  have hxa : x ≠ a := fun h => hxv (h ▸ hav)
  have hyv : y ≠ v := fun h => hay (h ▸ hav)
  simp only [unswE, swE]
  rw [erase_insert, erase_insert, insert_erase, insert_erase hav]
  · exact mem_erase.2 ⟨by simp [hxa, hyv], hxy⟩
  · exact fun h => hay (mem_of_mem_erase (mem_of_mem_erase h))
  · simp only [mem_insert, Prod.mk.injEq, not_or, not_and]
    exact ⟨fun h => absurd h hxa, fun h => hxv (mem_of_mem_erase (mem_of_mem_erase h))⟩

theorem swE_mem {d : BSeq ℓ n} {a : Fin ℓ} {v : Fin n} {q : BGraph ℓ n × (Fin ℓ × Fin n)}
    (hq : q ∈ Sw d a v) : (swE a v q.1 q.2, q.2) ∈ Sw' d a v := by
  obtain ⟨G, x, y⟩ := q
  rw [mem_Sw] at hq
  rw [mem_Sw']
  obtain ⟨hd, hav, hxy, hxv, hay⟩ := hq
  have hxa : x ≠ a := fun h => hxv (h ▸ hav)
  have hyv : y ≠ v := fun h => hay (h ▸ hav)
  have hE : (x, y) ∈ G.erase (a, v) := mem_erase.2 ⟨by simp [hxa, hyv], hxy⟩
  have hay' : (a, y) ∉ (G.erase (a, v)).erase (x, y) :=
    fun h => hay (mem_of_mem_erase (mem_of_mem_erase h))
  have hxv' : (x, v) ∉ insert (a, y) ((G.erase (a, v)).erase (x, y)) := by
    simp only [mem_insert, Prod.mk.injEq, not_or, not_and]
    exact ⟨fun h => absurd h hxa, fun h => hxv (mem_of_mem_erase (mem_of_mem_erase h))⟩
  refine ⟨⟨fun a' => ?_, fun v' => ?_⟩, ?_, by simp [swE], by simp [swE]⟩
  · simp only [swE]
    rw [ldeg_insert _ hxv', ldeg_insert _ hay', ldeg_erase _ hE, ldeg_erase _ hav, hd.1]
    simp only
    ring
  · simp only [swE]
    rw [rdeg_insert _ hxv', rdeg_insert _ hay', rdeg_erase _ hE, rdeg_erase _ hav, hd.2]
    simp only
    ring
  · simp only [swE, mem_insert, Prod.mk.injEq, not_or, not_and]
    refine ⟨fun h => absurd h.symm hxa, fun _ => hyv.symm, ?_⟩
    exact fun h => notMem_erase _ _ (mem_of_mem_erase h)

theorem card_Sw_le (d : BSeq ℓ n) (a : Fin ℓ) (v : Fin n) : (Sw d a v).card ≤ (Sw' d a v).card := by
  refine card_le_card_of_injOn (fun q => (swE a v q.1 q.2, q.2)) (fun q hq => swE_mem hq) ?_
  intro q hq q' hq' heq
  simp only [Prod.mk.injEq] at heq
  have h1 := unswE_swE hq
  have h2 := unswE_swE hq'
  rw [← heq.1, ← heq.2, h1] at h2
  exact Prod.ext h2 heq.2

/-- Lemma 2.3: the switching bound `P_{av} ≤ Δ_SΔ_T / (m - 3Δ_SΔ_T)`, `m = ∑ s_a`. -/
theorem lemma_2_3 (d : BSeq ℓ n) (hΔ : 3 * (DeltaS d * DeltaT d : ℝ) < M1 d.1) (a : Fin ℓ)
    (v : Fin n) :
    P a v d ≤ (DeltaS d * DeltaT d : ℝ) / ((M1 d.1 : ℝ) - 3 * (DeltaS d * DeltaT d)) := by
  have hΔ0 : (0 : ℝ) ≤ DeltaS d * DeltaT d := by positivity
  have hden : (0 : ℝ) < M1 d.1 - 3 * (DeltaS d * DeltaT d) := by linarith
  have key : (Nav a v d : ℝ) * (M1 d.1 - 2 * (DeltaS d * DeltaT d)) ≤
      (N d - Nav a v d) * (DeltaS d * DeltaT d) := by
    have := (card_Sw_ge d a v).trans ((Int.ofNat_le.2 (card_Sw_le d a v)).trans (card_Sw'_le d a v))
    exact_mod_cast this
  rcases Nat.eq_zero_or_pos (N d) with hN | hN
  · simp [P, hN]; positivity
  have hN' : (0 : ℝ) < N d := by exact_mod_cast hN
  rw [P, div_le_div_iff₀ hN' hden]
  nlinarith [key]

end LW.Bip
