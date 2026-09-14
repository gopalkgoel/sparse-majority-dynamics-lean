import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Basic
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.BipartitePairs

noncomputable section
open scoped Classical BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.Probability.FixedDegreeEdgeConcentration
open FixedDegreeSampling
variable {V L R : Type*} [Fintype V] [Fintype L] [Fintype R]

theorem remaining_card (v : V) : Fintype.card (Remaining v) = Fintype.card V - 1 := by
  simp [Remaining, Fintype.card_subtype_compl]

theorem remaining_sum (f : V → ℕ) (v : V) :
    f v + ∑ u : Remaining v, f u = ∑ u, f u := by
  exact (Fintype.sum_eq_add_sum_subtype_ne f v).symm

theorem graph_residual_total (d : V → ℕ) (m : ℕ) (v : V) (S : Finset V)
    (hs : ∑ u, d u = 2*m) (hS : graphAdmissible d v S) :
    d v ≤ m ∧ ∑ u : Remaining v, residualDegree d v S u = 2*(m-d v) := by
  have hind : (∑ u : Remaining v, if u.val ∈ S then (1:ℕ) else 0) = S.card := by
    have hh := remaining_sum (fun u => if u ∈ S then 1 else 0) v
    simpa [hS.1, ← Finset.sum_filter, Finset.sum_const, Finset.filter_mem_eq_inter,
      Finset.univ_inter] using hh
  have hh := Finset.sum_congr (s₁ := (Finset.univ : Finset (Remaining v))) rfl
    (fun u _ => residualDegree_add d v S hS u)
  rw [Finset.sum_add_distrib, hind, hS.2.1] at hh
  have hall := remaining_sum d v
  omega

theorem bipartite_residual_totals (a : L → ℕ) (b : R → ℕ) (m : ℕ)
    (v : L) (S : Finset R) (hsA : ∑ u, a u = m) (hsB : ∑ w, b w = m)
    (hS : bipartiteAdmissible a b v S) :
    a v ≤ m ∧ (∑ u : Remaining v, a u) = m-a v ∧
      (∑ w, residualRightDegree b S w) = m-a v := by
  have hA := remaining_sum a v
  have hdecr : ∀ w, residualRightDegree b S w + (if w ∈ S then 1 else 0) = b w := by
    intro w
    apply Nat.sub_add_cancel
    split_ifs with hw
    · exact hS.2 w hw
    · exact Nat.zero_le _
  have hh := Finset.sum_congr (s₁ := (Finset.univ : Finset R)) rfl (fun w _ => hdecr w)
  rw [Finset.sum_add_distrib] at hh
  have hind : (∑ w : R, if w ∈ S then (1:ℕ) else 0) = S.card := by
    simp
  rw [hind, hS.1, hsB] at hh
  rw [hsA] at hA
  omega

private theorem graph_bound_from_realized (d : V → ℕ) (h : (graphFamily d).Nonempty) :
    ∀ v, d v ≤ Fintype.card V - 1 := by
  obtain ⟨G,hG⟩ := h
  intro v
  have hd := G.degree_lt_card_verts v
  rw [hG v] at hd
  omega

private theorem bipartite_bounds_from_realized (a : L → ℕ) (b : R → ℕ)
    (h : (bipartiteFamily a b).Nonempty) :
    (∀ v, a v ≤ Fintype.card R) ∧ (∀ w, b w ≤ Fintype.card L) := by
  obtain ⟨E,hE⟩ := h
  constructor
  · intro v
    rw [← hE.1 v]
    exact Finset.card_le_univ _
  · intro w
    rw [← hE.2 w]
    exact Finset.card_le_univ _

private theorem enlarged_size {N k : ℕ} {T : ℝ} (hT : 1 ≤ T)
    (hlo : (N:ℝ)/T ≤ k) (hhi : (k:ℝ) ≤ T*N) :
    (N:ℝ)/(2*T+2) ≤ k ∧ (k:ℝ) ≤ (2*T+2)*N := by
  have hTp : 0 < T := by linarith
  constructor
  · exact (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hTp (by linarith)).trans hlo
  · nlinarith [Nat.cast_nonneg (α := ℝ) N]

private theorem enlarged_deleted_size {N k : ℕ} {T : ℝ} (hT : 1 ≤ T)
    (hN : 2*T ≤ (N:ℝ)) (hlo : (N:ℝ)/T ≤ k) (hhi : (k:ℝ) ≤ T*N) :
    (N:ℝ)/(2*T+2) ≤ (k-1:ℕ) ∧ ((k-1:ℕ):ℝ) ≤ (2*T+2)*N := by
  have hTp : 0 < T := by linarith
  have hk : (2:ℝ) ≤ k := by
    have := (le_div_iff₀ hTp).2 hN
    linarith
  have hkN : 1 ≤ k := by exact_mod_cast (show (1:ℝ) ≤ k by linarith)
  rw [Nat.cast_sub hkN, Nat.cast_one]
  have hn0 := Nat.cast_nonneg (α := ℝ) N
  have hkN' : (N:ℝ) ≤ (k:ℝ)*T := (div_le_iff₀ hTp).1 hlo
  constructor
  · apply (div_le_iff₀ (by linarith : 0 < 2*T+2)).2
    nlinarith
  · nlinarith

private theorem degree_decrement_bound (d e : ℕ) (z p s : ℝ)
    (he : e ≤ 1) (hed : e ≤ d) (hd : |(d:ℝ)-z| ≤ s)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hs : 1 ≤ s) :
    |((d-e:ℕ):ℝ) - (z-p)| ≤ 4*s+1 := by
  rw [Nat.cast_sub hed]
  have he0 := Nat.cast_nonneg (α := ℝ) e
  have he1 : (e:ℝ) ≤ 1 := by exact_mod_cast he
  have hh := abs_le.mp hd
  rw [abs_le]
  constructor <;> linarith

private theorem self_size (N : ℕ) (T : ℝ) (hT : 1 ≤ T) :
    (N:ℝ)/T ≤ N ∧ (N:ℝ) ≤ T*N := by
  have hN := Nat.cast_nonneg (α := ℝ) N
  constructor
  · apply (div_le_iff₀ (by linarith : 0 < T)).2
    nlinarith
  · nlinarith

/-- Original graph data lies in the shared uniform marginal window. -/
theorem original_graph_window (N m : ℕ) (p T : ℝ) (d : V → ℕ)
    (h : GraphInput N m p T d) (hT : 1 ≤ T)
    (hs : 1 ≤ (p*N)^((4:ℝ)/7)) (hr : (graphFamily d).Nonempty) :
    GraphWindow N N m p (2*T+2) 4 d := by
  obtain ⟨hlo,hhi⟩ := enlarged_size hT (self_size N T hT).1 (self_size N T hT).2
  refine ⟨h.card,hlo,hhi,h.bounded,h.total,?_,hr⟩
  intro v
  exact (h.degree_window v).trans (by linarith)

/-- Every feasible graph-neighborhood residual has the same ambient sparse scale,
with its literal remaining cardinality and edge total `m-d v`. -/
theorem graph_residual_window (N m : ℕ) (p T : ℝ) (d : V → ℕ)
    (h : GraphInput N m p T d) (hT : 1 ≤ T) (hN : 2*T ≤ (N:ℝ))
    (hs : 1 ≤ (p*N)^((4:ℝ)/7)) (v : V) (S : Finset V)
    (hS : graphAdmissible d v S) (hr : (graphFamily (residualDegree d v S)).Nonempty) :
    GraphWindow N (N-1) (m-d v) p (2*T+2) 4 (residualDegree d v S) := by
  have hc : Fintype.card (Remaining v) = N-1 := by rw [remaining_card,h.card]
  obtain ⟨hlo,hhi⟩ := enlarged_deleted_size hT hN
    (self_size N T hT).1 (self_size N T hT).2
  refine ⟨hc,hlo,hhi,?_,(graph_residual_total d m v S h.total hS).2,?_,hr⟩
  · simpa only [hc] using graph_bound_from_realized (residualDegree d v S) hr
  · intro u
    have he : (if u.val ∈ S then 1 else 0) ≤ d u := by
      split_ifs with hu
      · exact hS.2.2 u hu
      · exact Nat.zero_le _
    simpa only [sub_zero, residualDegree] using degree_decrement_bound
      (d u) (if u.val ∈ S then 1 else 0) (p*N) 0 ((p*N)^((4:ℝ)/7))
      (by split_ifs <;> omega) he (h.degree_window u) (by rfl) (by norm_num) hs

/-- General finite left-deletion bookkeeping, symmetric in the two original sizes.
This also supplies the right-deletion case by exact transposition. -/
theorem bipartite_left_window_of_bounds (N ell n m : ℕ) (p T : ℝ)
    (a : L → ℕ) (b : R → ℕ)
    (hcL : Fintype.card L = ell) (hcR : Fintype.card R = n)
    (hT : 1 ≤ T) (hN : 2*T ≤ (N:ℝ)) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hs : 1 ≤ (p*N)^((4:ℝ)/7))
    (hloL : (N:ℝ)/T ≤ ell) (hhiL : (ell:ℝ) ≤ T*N)
    (hloR : (N:ℝ)/T ≤ n) (hhiR : (n:ℝ) ≤ T*N)
    (hsA : ∑ u, a u = m) (hsB : ∑ w, b w = m)
    (hdA : ∀ u, |(a u:ℝ)-p*n| ≤ (p*N)^((4:ℝ)/7))
    (hdB : ∀ w, |(b w:ℝ)-p*ell| ≤ (p*N)^((4:ℝ)/7))
    (v : L) (S : Finset R) (hS : bipartiteAdmissible a b v S)
    (hr : (bipartiteFamily (fun u : Remaining v => a u) (residualRightDegree b S)).Nonempty) :
    BipartiteWindow N (ell-1) n (m-a v) p (2*T+2) 4
      (fun u : Remaining v => a u) (residualRightDegree b S) := by
  have hc : Fintype.card (Remaining v) = ell-1 := by rw [remaining_card,hcL]
  obtain ⟨hlL,hhL⟩ := enlarged_deleted_size hT hN hloL hhiL
  obtain ⟨hlR,hhR⟩ := enlarged_size hT hloR hhiR
  obtain ⟨hbL,hbR⟩ := bipartite_bounds_from_realized _ _ hr
  obtain ⟨_,htL,htR⟩ := bipartite_residual_totals a b m v S hsA hsB hS
  refine ⟨hc,hcR,hlL,hhL,hlR,hhR,?_,?_,htL,htR,?_,?_,hr⟩
  · simpa only [hcR] using hbL
  · simpa only [hc] using hbR
  · intro u
    exact (hdA u).trans (by linarith)
  · intro w
    have he : (if w ∈ S then 1 else 0) ≤ b w := by
      split_ifs with hw
      · exact hS.2 w hw
      · exact Nat.zero_le _
    have hell : 1 ≤ ell := by
      have hpos : 0 < Fintype.card L := Fintype.card_pos_iff.mpr ⟨v⟩
      omega
    have hh := degree_decrement_bound (b w) (if w ∈ S then 1 else 0) (p*ell) p
      ((p*N)^((4:ℝ)/7)) (by split_ifs <;> omega) he (hdB w) hp hp1 hs
    simpa only [residualRightDegree, Nat.cast_sub hell, Nat.cast_one, mul_sub, mul_one] using hh

/-- Original bipartite data lies in the shared window, preserving the common
right-block tolerance on both sides. -/
theorem original_bipartite_window (N ell m : ℕ) (p T : ℝ) (a : L → ℕ) (b : R → ℕ)
    (h : BipartiteInput ell N m p T a b) (hT : 1 ≤ T)
    (hs : 1 ≤ (p*N)^((4:ℝ)/7)) (hr : (bipartiteFamily a b).Nonempty) :
    BipartiteWindow N ell N m p (2*T+2) 4 a b := by
  obtain ⟨hloL,hhiL⟩ := enlarged_size hT h.size_lower h.size_upper
  obtain ⟨hloR,hhiR⟩ := enlarged_size hT (self_size N T hT).1 (self_size N T hT).2
  refine ⟨h.card_left,h.card_right,hloL,hhiL,hloR,hhiR,h.bounded_left,
    h.bounded_right,h.total_left,h.total_right,?_,?_,hr⟩
  · intro v; exact (h.degree_left v).trans (by linarith)
  · intro w; exact (h.degree_right w).trans (by linarith)

/-- Feasible exact left-neighborhood residual, from the original manuscript inputs. -/
theorem bipartite_left_residual_window (N ell m : ℕ) (p T : ℝ) (a : L → ℕ) (b : R → ℕ)
    (h : BipartiteInput ell N m p T a b) (hT : 1 ≤ T) (hN : 2*T ≤ (N:ℝ))
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hs : 1 ≤ (p*N)^((4:ℝ)/7))
    (v : L) (S : Finset R) (hS : bipartiteAdmissible a b v S)
    (hr : (bipartiteFamily (fun u : Remaining v => a u) (residualRightDegree b S)).Nonempty) :
    BipartiteWindow N (ell-1) N (m-a v) p (2*T+2) 4
      (fun u : Remaining v => a u) (residualRightDegree b S) :=
  bipartite_left_window_of_bounds N ell N m p T a b h.card_left h.card_right hT hN hp hp1 hs
    h.size_lower h.size_upper (self_size N T hT).1 (self_size N T hT).2
    h.total_left h.total_right h.degree_left h.degree_right v S hS hr

/-- The shared reference-scale window is exactly symmetric under transposition. -/
theorem bipartite_window_transpose (N ell n m : ℕ) (p K A : ℝ) (a : L → ℕ) (b : R → ℕ)
    (h : BipartiteWindow N ell n m p K A a b) :
    BipartiteWindow N n ell m p K A b a := by
  obtain ⟨E,hE⟩ := h.realized
  exact ⟨h.card_right,h.card_left,h.size_right_lower,h.size_right_upper,
    h.size_left_lower,h.size_left_upper,h.bounded_right,h.bounded_left,
    h.total_right,h.total_left,h.degree_right,h.degree_left,
    ⟨_,((transposeFamily a b) ⟨E,hE⟩).property⟩⟩

/-- Feasible exact right-neighborhood residual: the right carrier is reduced,
the left degrees decremented, and the actual total is `m-b v`. -/
theorem bipartite_right_residual_window (N ell m : ℕ) (p T : ℝ) (a : L → ℕ) (b : R → ℕ)
    (h : BipartiteInput ell N m p T a b) (hT : 1 ≤ T) (hN : 2*T ≤ (N:ℝ))
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hs : 1 ≤ (p*N)^((4:ℝ)/7))
    (v : R) (S : Finset L) (hS : bipartiteAdmissible b a v S)
    (hr : (bipartiteFamily (residualRightDegree a S) (fun w : Remaining v => b w)).Nonempty) :
    BipartiteWindow N ell (N-1) (m-b v) p (2*T+2) 4
      (residualRightDegree a S) (fun w : Remaining v => b w) := by
  have hr' : (bipartiteFamily (fun w : Remaining v => b w) (residualRightDegree a S)).Nonempty := by
    obtain ⟨E,hE⟩ := hr
    exact ⟨_,((transposeFamily _ _) ⟨E,hE⟩).property⟩
  have hh := bipartite_left_window_of_bounds N N ell m p T b a h.card_right h.card_left
    hT hN hp hp1 hs (self_size N T hT).1 (self_size N T hT).2 h.size_lower h.size_upper
    h.total_right h.total_left h.degree_right h.degree_left v S hS hr'
  exact bipartite_window_transpose N (N-1) ell (m-b v) p (2*T+2) 4 _ _ hh

end MajorityDynamics.Probability.FixedDegreeEdgeConcentration
