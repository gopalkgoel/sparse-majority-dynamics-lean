import MajorityDynamics.Literature.LWFormal.Counting
import MajorityDynamics.Literature.LWFormal.Hypergeom

set_option autoImplicit true

/-!
# §6: Concentration for the degree sequences of `𝒢(n,m)` and `ℬ_m(n)`

`ℬ_m(n)` is realised as a uniform `2m`-subset of the `n(n-1)` ordered pairs `(i,j)`, `i ≠ j`;
`dᵢ` is the number of chosen pairs with first coordinate `i`.

The paper's Lemma 6.1 (McDiarmid) and Lemma 6.2(ii) are not needed: the degree tails come
directly from the hypergeometric bound `hyp_tail'`, and (6.8) from the exact second moment.
-/

namespace LW

open Finset Real

variable {n : ℕ}

/-- Ordered pairs `(i,j)` with `i ≠ j`. -/
def allPairs (n : ℕ) : Finset (Fin n × Fin n) := univ.filter fun p => p.1 ≠ p.2

/-- The sample space of `ℬ_m(n)`. -/
def Bm (n m : ℕ) : Finset (Finset (Fin n × Fin n)) := (allPairs n).powersetCard (2 * m)

def pairDeg (S : Finset (Fin n × Fin n)) : Fin n → ℕ := fun i => (S.filter (·.1 = i)).card

/-- Handshake: a simple graph has `2|G|` ordered edges. -/
theorem card_ordEdges_eq {G : Graph n} (hs : IsSimple G) : (ordEdges G).card = 2 * G.card := by
  rw [card_eq_sum_card_fiberwise (f := fun p : Fin n × Fin n => s(p.1, p.2)) (t := G)
    (fun p hp => by simpa [ordEdges] using hp), mul_comm, ← smul_eq_mul, ← sum_const]
  refine sum_congr rfl fun e he => ?_
  induction e using Sym2.inductionOn with
  | hf x y =>
    have hxy : x ≠ y := fun h => hs _ he (by simp [h])
    have : (ordEdges G).filter (fun p : Fin n × Fin n => s(p.1, p.2) = s(x, y)) = {(x, y), (y, x)} := by
      ext ⟨a, b⟩
      simp only [mem_filter, ordEdges, mem_univ, true_and, mem_insert, mem_singleton,
        Prod.mk.injEq, Sym2.eq_iff]
      constructor
      · rintro ⟨-, h⟩; exact h
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨he, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨by rwa [Sym2.eq_swap], Or.inr ⟨rfl, rfl⟩⟩
    rw [this, card_pair (by simp [hxy])]

theorem sum_deg_eq {G : Graph n} (hs : IsSimple G) : ∑ v, deg G v = 2 * G.card := by
  rw [← card_ordEdges_eq hs, ordEdges, ← univ_product_univ, card_filter_product_mem hs]

theorem Gnm_eq (n m : ℕ) : Gnm n m = univ.filter fun E : Graph n => IsSimple E ∧ E.card = m := by
  ext E
  rw [Gnm, mem_powersetCard, mem_filter, and_iff_right (mem_univ _)]
  refine and_congr ?_ Iff.rfl
  constructor
  · intro h e he; simpa [allEdges] using h he
  · intro h e he; simpa [allEdges] using h e he

theorem card_Gnm (n m : ℕ) : (Gnm n m).card = edgeGraphCount n m := by
  rw [Gnm_eq]; rfl

theorem Gnm_filter_degSeq (n m : ℕ) (d : Fin n → ℕ) (hd : ∑ i, d i = 2 * m) :
    (Gnm n m).filter (degSeq · = d) = graphs fun i => (d i : ℤ) := by
  ext G
  rw [mem_filter, mem_graphs, Gnm_eq, mem_filter, and_iff_right (mem_univ _)]
  simp only [HasDegSeq, degSeq]
  constructor
  · rintro ⟨⟨hs, -⟩, rfl⟩; exact ⟨hs, fun v => rfl⟩
  · rintro ⟨hs, hdeg⟩
    have h : deg G = d := funext fun v => by exact_mod_cast hdeg v
    refine ⟨⟨hs, ?_⟩, h⟩
    have := sum_deg_eq hs
    rw [h, hd] at this; omega

/-- `P_{𝒟(𝒢(n,m))}(d) = N(d) / C(n(n-1)/2, m)` when `∑ dᵢ = 2m`. -/
theorem probGnm_eq (n m : ℕ) (d : Fin n → ℕ) (hd : ∑ i, d i = 2 * m) :
    probGnm n m d = N (fun i => (d i : ℤ)) / edgeGraphCount n m := by
  rw [probGnm, prob, Gnm_filter_degSeq n m d hd, card_Gnm, N]

/-- The fibres `{j : (i,j) ∈ S}` of a set of ordered pairs. -/
def fibres (S : Finset (Fin n × Fin n)) (i : Fin n) : Finset (Fin n) :=
  (S.filter (·.1 = i)).image Prod.snd

theorem card_fibres (S : Finset (Fin n × Fin n)) (i : Fin n) : (fibres S i).card = pairDeg S i := by
  rw [fibres, pairDeg, card_image_of_injOn]
  rintro ⟨a, b⟩ ha ⟨c, e⟩ hc h
  simp only [coe_filter, Set.mem_ofPred_eq] at ha hc
  simp only at h
  rw [Prod.mk.injEq]; exact ⟨ha.2.trans hc.2.symm, h⟩

theorem card_eq_sum_pairDeg (S : Finset (Fin n × Fin n)) : S.card = ∑ i, pairDeg S i :=
  card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) fun _ _ => mem_univ _

theorem mem_fibres {S : Finset (Fin n × Fin n)} {a b : Fin n} : b ∈ fibres S a ↔ (a, b) ∈ S := by
  simp only [fibres, mem_image, mem_filter]
  constructor
  · rintro ⟨⟨c, e⟩, ⟨h, rfl⟩, rfl⟩; exact h
  · intro h; exact ⟨(a, b), ⟨h, rfl⟩, rfl⟩

theorem card_allPairs (n : ℕ) : (allPairs n).card = n * (n - 1) := by
  rw [allPairs, ← compl_filter, card_compl, Fintype.card_prod, Fintype.card_fin]
  have : (univ.filter fun p : Fin n × Fin n => p.1 = p.2) = univ.image fun i => (i, i) := by
    ext ⟨a, b⟩; simp [eq_comm]
  rw [this, card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1), card_univ,
    Fintype.card_fin, Nat.mul_sub_one]

theorem card_Bm (n m : ℕ) : (Bm n m).card = (n * (n - 1)).choose (2 * m) := by
  rw [Bm, card_powersetCard, card_allPairs]

/-- Sets of pairs with fibre sizes `d` correspond to choices of `dᵢ`-subsets of `[n] \ {i}`. -/
theorem card_Bm_filter (n m : ℕ) (d : Fin n → ℕ) (hd : ∑ i, d i = 2 * m) :
    ((Bm n m).filter (pairDeg · = d)).card = ∏ i, (n - 1).choose (d i) := by
  have key : ∏ i, (n - 1).choose (d i) =
      (Fintype.piFinset fun i => (univ.erase i).powersetCard (d i)).card := by
    rw [Fintype.card_piFinset]
    refine prod_congr rfl fun i _ => ?_
    rw [card_powersetCard, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
  rw [key]
  refine card_bij (fun S _ => fibres S) ?_ ?_ ?_
  · intro S hS
    simp only [mem_filter, Bm, mem_powersetCard, allPairs, subset_iff, mem_univ, true_and] at hS
    obtain ⟨⟨hsub, -⟩, hdeg⟩ := hS
    rw [Fintype.mem_piFinset]
    intro i
    rw [mem_powersetCard, card_fibres, hdeg]
    refine ⟨fun j hj => ?_, rfl⟩
    simp only [fibres, mem_image, mem_filter] at hj
    obtain ⟨⟨a, b⟩, ⟨hab, rfl⟩, rfl⟩ := hj
    exact mem_erase.2 ⟨fun h => hsub hab (h ▸ rfl), mem_univ _⟩
  · intro S _ T _ hST
    ext ⟨a, b⟩
    rw [← mem_fibres, ← mem_fibres, hST]
  · intro F hF
    rw [Fintype.mem_piFinset] at hF
    have hfib : fibres (univ.filter fun p : Fin n × Fin n => p.2 ∈ F p.1) = F := by
      ext i j
      rw [mem_fibres, mem_filter]; simp
    refine ⟨univ.filter fun p : Fin n × Fin n => p.2 ∈ F p.1, ?_, hfib⟩
    have hdeg : pairDeg (univ.filter fun p : Fin n × Fin n => p.2 ∈ F p.1) = d := by
      ext i
      rw [← card_fibres, hfib]
      exact (mem_powersetCard.1 (hF i)).2
    simp only [mem_filter, Bm, mem_powersetCard, allPairs, subset_iff, mem_univ, true_and]
    refine ⟨⟨fun p hp => ?_, ?_⟩, hdeg⟩
    · obtain ⟨a, b⟩ := p
      exact fun h => (mem_erase.1 ((mem_powersetCard.1 (hF a)).1 hp)).1 (by simpa using h.symm)
    · rw [card_eq_sum_pairDeg, hdeg, hd]

/-- `P_{ℬ_m}(d)` agrees with the formula `C(n(n-1),2m)⁻¹ ∏ C(n-1,dᵢ)`. -/
theorem probBinom_eq (n m : ℕ) (d : Fin n → ℕ) (hd : ∑ i, d i = 2 * m) :
    probBinom n m d = prob (Bm n m) (pairDeg · = d) := by
  rw [probBinom, prob, card_Bm_filter n m d hd, card_Bm, div_eq_inv_mul, Nat.cast_prod]

theorem two_mul_card_allEdges (n : ℕ) : 2 * (allEdges n).card = n * (n - 1) := by
  have hs : IsSimple (allEdges n) := fun e he => by simpa [allEdges] using he
  have : ordEdges (allEdges n) = allPairs n := by
    ext ⟨a, b⟩; simp [ordEdges, allEdges, allPairs]
  have h := card_ordEdges_eq hs
  rw [this, card_allPairs] at h
  exact h.symm

/-- The `n - 1` potential edges at vertex `i`; `deg E i = |E ∩ starE n i|`. -/
def starE (n : ℕ) (i : Fin n) : Finset (Sym2 (Fin n)) := (allEdges n).filter (i ∈ ·)

theorem card_starE (n : ℕ) (i : Fin n) : (starE n i).card = n - 1 := by
  have hs : IsSimple (allEdges n) := fun e he => by simpa [allEdges] using he
  have : nbrs (allEdges n) i = univ.erase i := by
    ext j; simp [nbrs, allEdges, eq_comm]
  rw [starE, ← deg, ← card_nbrs hs, this, card_erase_of_mem (mem_univ i), card_univ,
    Fintype.card_fin]

theorem deg_eq_card_inter {E : Graph n} (hE : E ⊆ allEdges n) (i : Fin n) :
    deg E i = (E ∩ starE n i).card := by
  rw [deg, starE, inter_filter, inter_eq_left.2 hE]

/-- The `n - 1` ordered pairs with first coordinate `i`; `pairDeg S i = |S ∩ starP n i|`. -/
def starP (n : ℕ) (i : Fin n) : Finset (Fin n × Fin n) := (allPairs n).filter (·.1 = i)

theorem card_starP (n : ℕ) (i : Fin n) : (starP n i).card = n - 1 := by
  have : starP n i = (univ.erase i).image fun j => (i, j) := by
    ext ⟨a, b⟩
    simp only [starP, allPairs, mem_filter, mem_univ, true_and, mem_image, mem_erase,
      Prod.mk.injEq]
    constructor
    · rintro ⟨h, rfl⟩; exact ⟨b, ⟨fun h' => h h'.symm, trivial⟩, rfl, rfl⟩
    · rintro ⟨j, ⟨hj, -⟩, rfl, rfl⟩; exact ⟨fun h => hj h.symm, rfl⟩
  rw [this, card_image_of_injective _ (Prod.mk_right_injective i), card_erase_of_mem (mem_univ i),
    card_univ, Fintype.card_fin]

theorem pairDeg_eq_card_inter {S : Finset (Fin n × Fin n)} (hS : S ⊆ allPairs n) (i : Fin n) :
    pairDeg S i = (S ∩ starP n i).card := by
  rw [pairDeg, starP, inter_filter, inter_eq_left.2 hS]

/-- Lemma 6.2(i) for `𝒢(n,m)`, via the hypergeometric tail: `P(|dᵢ - d| > t) ≤ 2(d+1)e^{-t²/32d}`. -/
theorem deg_tail_G (n m : ℕ) (hn : 4 ≤ n) (hm : 8 * m ≤ n * n) (i : Fin n) {t : ℝ} (ht : 6 ≤ t)
    (htμ : t ≤ 2 * m / n) :
    prob (Gnm n m) (fun E => t < |(deg E i : ℝ) - 2 * m / n|) ≤
      2 * (2 * m / n + 1) * exp (-t ^ 2 / (32 * (2 * m / n))) := by
  have hA : starE n i ⊆ allEdges n := filter_subset _ _
  have h2 := two_mul_card_allEdges n
  have hk : (starE n i).card + m ≤ (allEdges n).card := by
    rw [card_starE]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    rw [show k + 4 - 1 = k + 3 by omega] at h2 ⊢
    nlinarith
  have hμ : (2 * m / n : ℝ) = (starE n i).card * m / (allEdges n).card := by
    have h2' : (2 * (allEdges n).card : ℝ) = n * ((n : ℝ) - 1) := by
      rw [← Nat.cast_ofNat, ← Nat.cast_mul, h2, Nat.cast_mul, Nat.cast_sub (by omega),
        Nat.cast_one]
    have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
    rw [card_starE, Nat.cast_sub (by omega), Nat.cast_one,
      div_eq_div_iff (by linarith) (by nlinarith)]
    linear_combination (m : ℝ) * h2'
  refine le_trans (prob_mono _ fun E hE h => ?_)
    (hyp_tail' (allEdges n) (starE n i) m hA hk hμ ht htμ)
  rwa [deg_eq_card_inter (mem_powersetCard.1 hE).1] at h

/-- Lemma 6.2(i) for `ℬ_m(n)`. -/
theorem deg_tail_B (n m : ℕ) (hn : 4 ≤ n) (hm : 8 * m ≤ n * n) (i : Fin n) {t : ℝ} (ht : 6 ≤ t)
    (htμ : t ≤ 2 * m / n) :
    prob (Bm n m) (fun S => t < |(pairDeg S i : ℝ) - 2 * m / n|) ≤
      2 * (2 * m / n + 1) * exp (-t ^ 2 / (32 * (2 * m / n))) := by
  have hA : starP n i ⊆ allPairs n := filter_subset _ _
  have h2 := card_allPairs n
  have hk : (starP n i).card + 2 * m ≤ (allPairs n).card := by
    rw [card_starP, h2]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    rw [show k + 4 - 1 = k + 3 by omega]
    nlinarith
  have hμ : (2 * m / n : ℝ) = (starP n i).card * ((2 * m : ℕ) : ℝ) / (allPairs n).card := by
    have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
    rw [card_starP, h2]
    push_cast [Nat.cast_sub (by omega : 1 ≤ n)]
    rw [div_eq_div_iff (by linarith) (by nlinarith)]
    ring
  refine le_trans (prob_mono _ fun S hS h => ?_)
    (hyp_tail' (allPairs n) (starP n i) (2 * m) hA hk hμ ht htμ)
  rwa [pairDeg_eq_card_inter (mem_powersetCard.1 hS).1] at h

end LW
