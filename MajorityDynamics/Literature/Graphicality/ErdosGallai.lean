import MajorityDynamics.Literature.Graphicality.Basic
import MajorityDynamics.Literature.Graphicality.Edits
import MajorityDynamics.Literature.Graphicality.Exchanges
import MajorityDynamics.Literature.Graphicality.Counting
import MajorityDynamics.Literature.Graphicality.ExchangesTwo

/-!
# Erdős–Gallai via subrealizations

The proof follows Theorem 1 of A. Tripathi, S. Venugopalan, D. B. West,
“A short constructive proof of the Erdős–Gallai characterization of graphic
lists”, Discrete Mathematics 310 (2010), 843–844. Author manuscript,
September 6, 2009, pp. 2–3: https://dwest.web.illinois.edu/pubs/tripathi.pdf.
The Lean proof is new; no external formal source is copied.
-/

namespace MajorityDynamics.Combinatorics.SufficientGraphicality
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

namespace ErdosGallai

/-- A subrealization with a saturated initial segment and an independent tail. -/
def Partial {n : ℕ} (d : Fin n → ℕ) (r : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  (∀ v, G.degree v ≤ d v) ∧
  (∀ v, v.val < r → G.degree v = d v) ∧
  (∀ v w, r < v.val → r < w.val → ¬ G.Adj v w)

theorem partial_bot {n : ℕ} (d : Fin n → ℕ) : Partial d 0 ⊥ := by
  refine ⟨?_, ?_, ?_⟩
  · simp
  · intro v hv
    omega
  · simp

theorem exists_maximal {n : ℕ} (d : Fin n → ℕ) (r : Fin n)
    (G₀ : SimpleGraph (Fin n)) (hG₀ : Partial d r.val G₀) :
    ∃ G : SimpleGraph (Fin n), Partial d r.val G ∧
      ∀ H : SimpleGraph (Fin n), Partial d r.val H → H.degree r ≤ G.degree r := by
  classical
  let s := (Finset.univ : Finset (SimpleGraph (Fin n))).filter (Partial d r.val)
  have hs : s.Nonempty := ⟨G₀, by simp [s, hG₀]⟩
  obtain ⟨G, hG, hmax⟩ := Finset.exists_max_image s (fun G => G.degree r) hs
  refine ⟨G, (Finset.mem_filter.mp hG).2, ?_⟩
  intro H hH
  exact hmax H (by simp [s, hH])

section Maximal
variable {n : ℕ} {d : Fin n → ℕ} {r : Fin n} {G : SimpleGraph (Fin n)}
variable (hG : Partial d r.val G)
variable (hmax : ∀ H : SimpleGraph (Fin n), Partial d r.val H → H.degree r ≤ G.degree r)
variable (hdef : G.degree r < d r)
include hG

theorem deficient_later {k : Fin n} (hkr : k ≠ r) (hk : G.degree k < d k) :
    r.val < k.val := by
  have hne : k.val ≠ r.val := fun h => hkr (Fin.ext h)
  by_contra h
  have he := hG.2.1 k (by omega)
  omega

include hmax hdef
/-- Case 0 of the source proof: two unsaturated nonadjacent vertices admit an edge. -/
theorem deficient_adj {k : Fin n} (hkr : k ≠ r) (hk : G.degree k < d k) :
    G.Adj r k := by
  classical
  by_contra hnot
  have hlate := deficient_later hG hkr hk
  let H := addEdge G r k (Ne.symm hkr)
  have hdeg (v) := degree_addEdge G r k (Ne.symm hkr) hnot v
  have hH : Partial d r.val H := by
    refine ⟨?_, ?_, ?_⟩
    · intro v
      have hv := hG.1 v
      have he := hdeg v
      change H.degree v = _ at he
      by_cases hvr : v = r
      · subst v
        simp only [ite_true, if_neg (Ne.symm hkr)] at he
        omega
      · by_cases hvk : v = k
        · subst v
          simp only [if_neg hkr, ite_true] at he
          omega
        · simp only [if_neg hvr, if_neg hvk, Nat.add_zero] at he
          omega
    · intro v hv
      have hvr : v ≠ r := by intro h; subst v; omega
      have hvk : v ≠ k := by intro h; subst v; omega
      simpa [H, hvr, hvk] using (hdeg v).trans (by simpa [hvr, hvk] using hG.2.1 v hv)
    · intro v w hv hw
      have hvr : v ≠ r := by intro h; subst v; omega
      have hwr : w ≠ r := by intro h; subst w; omega
      simpa [H, addEdge_adj, hvr, hwr] using hG.2.2 v w hv hw
  have hm := hmax H hH
  have he := hdeg r
  change H.degree r = _ at he
  simp only [ite_true, if_neg (Ne.symm hkr)] at he
  omega

omit hmax hdef in
theorem partial_of_edit (H : SimpleGraph (Fin n))
    (hb : ∀ v, H.degree v ≤ d v)
    (he : ∀ v, v.val < r.val → H.degree v = G.degree v)
    (ha : ∀ v w, H.Adj v w → G.Adj v w ∨ v.val ≤ r.val ∨ w.val ≤ r.val) :
    Partial d r.val H := by
  refine ⟨hb, fun v hv => (he v hv).trans (hG.2.1 v hv), ?_⟩
  intro v w hv hw hadj
  rcases ha v w hadj with ho | ho | ho
  · exact hG.2.2 v w hv hw ho
  · omega
  · omega

omit hdef in
theorem no_double_improvement (H : SimpleGraph (Fin n))
    (hroom : G.degree r + 2 ≤ d r)
    (hd : ∀ v, H.degree v = G.degree v + if v = r then 2 else 0)
    (ha : ∀ v w, H.Adj v w → G.Adj v w ∨ v.val ≤ r.val ∨ w.val ≤ r.val) : False := by
  have hh : Partial d r.val H := partial_of_edit hG H (by
      intro v
      by_cases hv : v = r
      · subst v; simpa [hd] using hroom
      · simpa [hd, hv] using hG.1 v) (by
      intro v hv
      have hn : v ≠ r := by intro he; subst v; omega
      simp [hd, hn]) ha
  have := hmax H hh
  have := hd r
  simp only [ite_true] at this
  omega

theorem no_single_transfer (H : SimpleGraph (Fin n)) (k : Fin n) (hk : r.val < k.val)
    (hd : ∀ v, H.degree v + (if v = k then 1 else 0) =
      G.degree v + if v = r then 1 else 0)
    (ha : ∀ v w, H.Adj v w → G.Adj v w ∨ v.val ≤ r.val ∨ w.val ≤ r.val) : False := by
  have hkr : k ≠ r := by intro he; subst k; omega
  have hh : Partial d r.val H := partial_of_edit hG H (by
      intro v
      have he := hd v
      have hb := hG.1 v
      by_cases hv : v = r
      · subst v
        simp only [ite_true, if_neg hkr.symm, Nat.add_zero] at he
        omega
      · simp only [if_neg hv, Nat.add_zero] at he
        omega) (by
      intro v hv
      have hvr : v ≠ r := by intro he; subst v; omega
      have hvk : v ≠ k := by intro he; subst v; omega
      simpa [hvr, hvk] using hd v) ha
  have hm := hmax H hh
  have he := hd r
  simp only [if_neg hkr.symm, ite_true, Nat.add_zero] at he
  omega

theorem no_pair_improvement (H : SimpleGraph (Fin n)) (k : Fin n)
    (hk : r.val < k.val) (hroom : G.degree k < d k)
    (hd : ∀ v, H.degree v = G.degree v + (if v = r then 1 else 0) +
      if v = k then 1 else 0)
    (ha : ∀ v w, H.Adj v w → G.Adj v w ∨ v.val ≤ r.val ∨ w.val ≤ r.val) : False := by
  have hkr : k ≠ r := by intro he; subst k; omega
  have hh : Partial d r.val H := partial_of_edit hG H (by
      intro v
      have he := hd v
      have hb := hG.1 v
      by_cases hv : v = r
      · subst v
        simp only [ite_true, if_neg hkr.symm] at he
        omega
      · by_cases hvk : v = k
        · subst v
          simp only [if_neg hkr, ite_true] at he
          omega
        · simp only [if_neg hv, if_neg hvk, Nat.add_zero] at he
          omega) (by
      intro v hv
      have hvr : v ≠ r := by intro he; subst v; omega
      have hvk : v ≠ k := by intro he; subst v; omega
      simpa [hvr, hvk] using hd v) ha
  have hm := hmax H hh
  have he := hd r
  simp only [if_neg hkr.symm, ite_true] at he
  omega

variable (hsort : Antitone d) (heven : Even (total d))
include hsort heven

/-- Case 1 forces every earlier vertex to be adjacent to the critical vertex. -/
theorem earlier_adj (i : Fin n) (hi : i.val < r.val) : G.Adj r i := by
  by_contra hri
  have hrine : r ≠ i := by intro he; subst i; omega
  have hdi : G.degree r < G.degree i := by
    have he := hG.2.1 i hi
    have hs := hsort (show i ≤ r from Fin.le_iff_val_le_val.mpr (by omega))
    omega
  obtain ⟨u, hur, hiu, hru⟩ := exists_neighbor_of_degree_lt G hdi
  by_cases hroom : G.degree r + 2 ≤ d r
  · obtain ⟨H, hd, ha, _⟩ := exists_double_augmentation G hrine hri hiu hru hur
    apply no_double_improvement hG hmax H hroom hd
    intro v w hvw
    rcases ha v w hvw with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by subst v; omega))
    · exact Or.inr (Or.inr (by subst w; omega))
  · have hone : G.degree r + 1 = d r := by omega
    obtain ⟨k, hk, hdk⟩ := exists_later_deficient_of_one_deficiency G d r hG.1
      heven (fun v hv => hG.2.1 v (Fin.lt_def.mp hv)) hone
    have hkr : k ≠ r := ne_of_gt hk
    have hrk := deficient_adj hG hmax hdef hkr hdk
    have hki : k ≠ i := by
      intro he
      subst k
      have := Fin.lt_def.mp hk
      omega
    obtain ⟨H, hd, ha⟩ := exists_single_augmentation G hrine hri hiu hru hur hrk hki
    apply no_single_transfer hG hmax hdef H k (Fin.lt_def.mp hk) hd
    intro v w hvw
    rcases ha v w hvw with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by subst v; omega))
    · exact Or.inr (Or.inr (by subst w; omega))

theorem nonneighbor_later {u : Fin n} (hur : u ≠ r) (hru : ¬ G.Adj r u) :
    r.val < u.val := by
  have hne : u.val ≠ r.val := fun he => hur (Fin.ext he)
  by_contra h
  exact hru (earlier_adj hG hmax hdef hsort heven u (by omega))

omit hmax hdef hsort heven in
/-- The independent tail bounds each tail degree by the size of the prefix. -/
theorem tail_degree_le {k : Fin n} (hk : r.val < k.val) :
    G.degree k ≤ r.val + 1 := by
  have hs : G.neighborFinset k ⊆ prefixSet n (r.val + 1) (by omega) := by
    intro v hv
    rw [mem_prefixSet]
    have hadj : G.Adj k v := by simpa using hv
    by_contra hn
    exact hG.2.2 k v hk (by omega) hadj
  simpa using Finset.card_le_card hs

omit hG hmax hdef hsort heven in
/-- A tail vertex of degree below the prefix size misses an earlier vertex. -/
theorem missing_earlier {k : Fin n}
    (hdeg : G.degree k < r.val + 1) (hrk : G.Adj r k) :
    ∃ i : Fin n, i.val < r.val ∧ ¬ G.Adj i k := by
  by_contra! hn
  have hs : prefixSet n (r.val + 1) (by omega) ⊆ G.neighborFinset k := by
    intro i hi
    rw [mem_prefixSet] at hi
    rw [SimpleGraph.mem_neighborFinset]
    by_cases hir : i = r
    · subst i; exact hrk.symm
    · have hne : i.val ≠ r.val := fun he => hir (Fin.ext he)
      exact (hn i (by omega)).symm
  have := Finset.card_le_card hs
  simp only [card_prefix, SimpleGraph.card_neighborFinset_eq_degree] at this
  omega

omit heven in
/-- Case 2 forces all tail vertices to have their maximal permitted degree. -/
theorem tail_degree_eq (k : Fin n) (hk : r.val < k.val) :
    G.degree k = min (r.val + 1) (d k) := by
  have hb := hG.1 k
  have hc := tail_degree_le hG hk
  by_contra hne
  have hlt : G.degree k < min (r.val + 1) (d k) := by omega
  have hd : G.degree k < d k := lt_of_lt_of_le hlt (min_le_right _ _)
  have hkr : k ≠ r := by intro he; subst k; omega
  have hrk := deficient_adj hG hmax hdef hkr hd
  obtain ⟨i, hi, hik⟩ := missing_earlier (lt_of_lt_of_le hlt (min_le_left _ _)) hrk
  have hdi : G.degree r < G.degree i := by
    have he := hG.2.1 i hi
    have hs := hsort (show i ≤ r from Fin.le_iff_val_le_val.mpr (by omega))
    omega
  obtain ⟨u, hur, hiu, hru⟩ := exists_neighbor_of_degree_lt G hdi
  have hri : r ≠ i := by intro he; subst i; omega
  have hikne : i ≠ k := by intro he; subst i; omega
  obtain ⟨H, he, ha⟩ := exchange_two_edges G r i u k hiu hru hik hri hkr.symm hur hikne
  apply no_pair_improvement hG hmax hdef H k hk hd he
  intro v w hvw
  rcases ha v w hvw with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (by subst v; omega))
  · exact Or.inr (Or.inr (by subst w; omega))
  · exact Or.inr (Or.inl (by subst v; omega))
  · exact Or.inr (Or.inr (by subst w; omega))

/-- Case 3 forces the earlier saturated vertices to form a clique. -/
theorem earlier_clique (i j : Fin n) (hi : i.val < r.val) (hj : j.val < r.val)
    (hijne : i ≠ j) : G.Adj i j := by
  by_contra hij
  have hdi : G.degree r < G.degree i := by
    have he := hG.2.1 i hi
    have hs := hsort (show i ≤ r from Fin.le_iff_val_le_val.mpr (by omega))
    omega
  have hdj : G.degree r < G.degree j := by
    have he := hG.2.1 j hj
    have hs := hsort (show j ≤ r from Fin.le_iff_val_le_val.mpr (by omega))
    omega
  obtain ⟨u, hur, hiu, hru⟩ := exists_neighbor_of_degree_lt G hdi
  obtain ⟨w, hwr, hjw, hrw⟩ := exists_neighbor_of_degree_lt G hdj
  have hu := nonneighbor_later hG hmax hdef hsort heven hur hru
  have hw := nonneighbor_later hG hmax hdef hsort heven hwr hrw
  have hri : r ≠ i := by intro he; subst i; omega
  have hrj : r ≠ j := by intro he; subst j; omega
  have hju : j ≠ u := by intro he; subst j; omega
  obtain ⟨H, he, ha⟩ := exchange_three_edges G r i j u w hiu hjw hij hru
    hri hrj hur.symm hijne hju
  apply no_single_transfer hG hmax hdef H w hw he
  intro v z hvz
  rcases ha v z hvz with h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (by subst v; omega))
  · exact Or.inr (Or.inr (by subst z; omega))
  · exact Or.inr (Or.inl (by subst v; omega))
  · exact Or.inr (Or.inr (by subst z; omega))
  · exact Or.inr (Or.inl (by subst v; omega))
  · exact Or.inr (Or.inr (by subst z; omega))

end Maximal

/-- The maximal subrealization must saturate the next vertex: otherwise its
forced clique and tail degrees violate precisely the next prefix inequality. -/
theorem maximal_saturates {n : ℕ} (d : Fin n → ℕ) (r : Fin n)
    (hsort : Antitone d) (heven : Even (total d))
    (hineq : (∑ i ∈ prefixSet n (r.val + 1) (by omega), d i) ≤
      (r.val + 1) * r.val +
        ∑ i ∈ (prefixSet n (r.val + 1) (by omega))ᶜ, min (r.val + 1) (d i))
    (G : SimpleGraph (Fin n)) (hG : Partial d r.val G)
    (hmax : ∀ H : SimpleGraph (Fin n), Partial d r.val H → H.degree r ≤ G.degree r) :
    G.degree r = d r := by
  by_contra hne
  have hdef : G.degree r < d r := by have := hG.1 r; omega
  have hc : ∀ i, i ≤ r → ∀ j, j ≤ r → i ≠ j → G.Adj i j := by
    intro i hi j hj hij
    by_cases hir : i = r
    · subst i
      exact earlier_adj hG hmax hdef hsort heven j
        (by have := Fin.le_iff_val_le_val.mp hj; have hn : j.val ≠ r.val := fun he => hij (Fin.ext he).symm; omega)
    · by_cases hjr : j = r
      · subst j
        exact (earlier_adj hG hmax hdef hsort heven i
          (by have := Fin.le_iff_val_le_val.mp hi; have hn : i.val ≠ r.val := fun he => hir (Fin.ext he); omega)).symm
      · apply earlier_clique hG hmax hdef hsort heven i j _ _ hij
        · have := Fin.le_iff_val_le_val.mp hi
          have hn : i.val ≠ r.val := fun he => hir (Fin.ext he)
          omega
        · have := Fin.le_iff_val_le_val.mp hj
          have hn : j.val ≠ r.val := fun he => hjr (Fin.ext he)
          omega
  have hind : ∀ i, r < i → ∀ j, r < j → ¬ G.Adj i j := by
    intro i hi j hj
    exact hG.2.2 i j (Fin.lt_def.mp hi) (Fin.lt_def.mp hj)
  have hcount := prefix_degree_sum_clique_independent G r hc hind
  have htail : (∑ i ∈ (prefixSet n (r.val + 1) (by omega))ᶜ, G.degree i) =
      ∑ i ∈ (prefixSet n (r.val + 1) (by omega))ᶜ, min (r.val + 1) (d i) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [mem_compl, mem_prefixSet, not_lt] at hi
    exact tail_degree_eq hG hmax hdef hsort i (by omega)
  have hstrict : (∑ i ∈ prefixSet n (r.val + 1) (by omega), G.degree i) <
      ∑ i ∈ prefixSet n (r.val + 1) (by omega), d i := by
    apply Finset.sum_lt_sum
    · intro i _; exact hG.1 i
    · exact ⟨r, by simp, hdef⟩
  omega

/-- Full-range Erdős–Gallai sufficiency, retaining the original vertex labels. -/
theorem sufficient (n : ℕ) (d : Fin n → ℕ) (hsort : Antitone d)
    (heven : Even (total d))
    (hineq : ∀ (k : ℕ) (hk : k ≤ n), 1 ≤ k →
      (∑ i ∈ prefixSet n k hk, d i) ≤ k * (k - 1) +
        ∑ i ∈ (prefixSet n k hk)ᶜ, min k (d i)) : Graphical d := by
  have hstage : ∀ k : ℕ, k ≤ n → ∃ G : SimpleGraph (Fin n), Partial d k G := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨⊥, partial_bot d⟩
    | succ k ih =>
      intro hk
      obtain ⟨G₀, hG₀⟩ := ih (by omega)
      let r : Fin n := ⟨k, by omega⟩
      obtain ⟨G, hG, hmax⟩ := exists_maximal d r G₀ hG₀
      have he : G.degree r = d r := maximal_saturates d r hsort heven
        (by simpa [r] using hineq (k + 1) hk (by omega)) G hG hmax
      refine ⟨G, hG.1, ?_, ?_⟩
      · intro v hv
        by_cases hvk : v.val = k
        · have hvr : v = r := Fin.ext hvk
          subst v
          exact he
        · exact hG.2.1 v (by dsimp [r]; omega)
      · intro v w hv hw
        exact hG.2.2 v w (by dsimp [r]; omega) (by dsimp [r]; omega)
  obtain ⟨G, hG⟩ := hstage n le_rfl
  exact ⟨G, fun v => hG.2.1 v v.isLt⟩

end ErdosGallai
end
end MajorityDynamics.Combinatorics.SufficientGraphicality
