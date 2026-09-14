import MajorityDynamics.Probability.DegreeConcentration.Basic

/-!
# Deterministic ingredients of the graph reduction

* `sum_sq_mean_le`: the empirical mean minimises `a ↦ ∑ᵢ (dᵢ - a)²`.
* The random-cut covering. For a fixed simple graph `G` on `Fin n`, a vertex set `S`, and
  `v ∉ S`, the cut degree `deg_S v` is the number of neighbours of `v` in `S`, and
  `Δ_S(v) = deg_S v - p |S ∖ {v}|`. Averaging over all `2^n` sets `S` (the manuscript's
  uniformly random `S`; here a plain finite average, which is auxiliary randomness distinct
  from the randomness of `G`) gives

    `∑_S ∑_{v ∉ S} Δ_S(v)² ≥ (2^n/8) ∑_v (d_v - p(n-1))²`,

  so some `S` satisfies `∑_{v ∉ S} (deg_S v - p|S|)² ≥ (1/8) ∑_v (d_v - p(n-1))²`
  (`exists_cut_of_spread`). This is purely combinatorial; no probability is involved.
-/

noncomputable section

open Finset
open scoped BigOperators symmDiff

namespace MajorityDynamics.Probability.DegreeConcentration

/-! ### The empirical mean minimises the sum of squares -/

theorem sum_sq_mean_le {J : Type*} [Fintype J] (d : J → ℝ) (a : ℝ) :
    ∑ j, (d j - (∑ j, d j) / (Fintype.card J : ℝ)) ^ 2 ≤ ∑ j, (d j - a) ^ 2 := by
  set m : ℝ := (∑ j, d j) / (Fintype.card J : ℝ) with hm
  rcases (Fintype.card J).eq_zero_or_pos with h0 | hpos
  · have : IsEmpty J := Fintype.card_eq_zero_iff.mp h0
    simp
  · have hcard : (Fintype.card J : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    have hsum : ∑ j, d j = (Fintype.card J : ℝ) * m := by
      rw [hm, mul_div_cancel₀ _ hcard]
    have key : ∑ j, (d j - a) ^ 2 - ∑ j, (d j - m) ^ 2 = (Fintype.card J : ℝ) * (m - a) ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      have h1 : ∀ j, (d j - a) ^ 2 - (d j - m) ^ 2 = (m - a) * (2 * d j) - (m - a) * (a + m) :=
        fun j ↦ by ring
      simp_rw [h1]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, hsum]
      ring
    nlinarith [key, mul_nonneg (Nat.cast_nonneg (Fintype.card J)) (sq_nonneg (m - a))]

/-! ### Cut degrees and deviations -/

variable {n : ℕ}

open Classical in
/-- `deg_S v`: the number of neighbours of `v` inside `S`. -/
def cutDegree (G : Graph n) (S : Finset (Fin n)) (v : Fin n) : ℕ :=
  (S.filter fun w ↦ G.Adj v w).card

open Classical in
/-- `Δ_S(v) = deg_S v - p |S ∖ {v}|`. -/
def cutDeviation (G : Graph n) (p : ℝ) (S : Finset (Fin n)) (v : Fin n) : ℝ :=
  (cutDegree G S v : ℝ) - p * ((S.erase v).card : ℝ)

open Classical in
theorem cutDegree_erase (G : Graph n) (S : Finset (Fin n)) (v : Fin n) :
    cutDegree G (S.erase v) v = cutDegree G S v := by
  unfold cutDegree
  rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
  simp

open Classical in
theorem cutDegree_le_degree (G : Graph n) (S : Finset (Fin n)) (v : Fin n) :
    cutDegree G S v ≤ G.degree v := by
  unfold cutDegree
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ S))

open Classical in
theorem cutDegree_univ (G : Graph n) (v : Fin n) : cutDegree G Finset.univ v = G.degree v := by
  unfold cutDegree
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]

open Classical in
theorem cutDegree_add_compl (G : Graph n) (S : Finset (Fin n)) (v : Fin n) :
    cutDegree G S v + cutDegree G Sᶜ v = G.degree v := by
  unfold cutDegree
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter,
    ← Finset.union_compl S, Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter (disjoint_compl_right))]

theorem card_erase_add_card_compl_erase (S : Finset (Fin n)) (v : Fin n) :
    (S.erase v).card + (Sᶜ.erase v).card = n - 1 := by
  rw [← Finset.card_union_of_disjoint, ← Finset.erase_union_distrib, Finset.union_compl,
    Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]
  exact Finset.disjoint_of_subset_left (Finset.erase_subset _ _)
    (Finset.disjoint_of_subset_right (Finset.erase_subset _ _) disjoint_compl_right)

open Classical in
/-- `Δ_S(v) + Δ_{Sᶜ}(v) = d_v - p(n-1)`. -/
theorem cutDeviation_add_compl (G : Graph n) (p : ℝ) (S : Finset (Fin n)) (v : Fin n) :
    cutDeviation G p S v + cutDeviation G p Sᶜ v = (G.degree v : ℝ) - p * ((n : ℝ) - 1) := by
  unfold cutDeviation
  have h1 := cutDegree_add_compl G S v
  have h2 := card_erase_add_card_compl_erase S v
  have h1' : (cutDegree G S v : ℝ) + cutDegree G Sᶜ v = G.degree v := by exact_mod_cast h1
  have h2' : ((S.erase v).card : ℝ) + (Sᶜ.erase v).card = (n : ℝ) - 1 := by
    rw [← Nat.cast_pred (Fin.pos v)]
    exact_mod_cast h2
  linear_combination h1' - p * h2'

theorem erase_symmDiff_singleton (S : Finset (Fin n)) (v : Fin n) :
    (S ∆ {v}).erase v = S.erase v := by
  ext w
  by_cases hw : w = v
  · simp [hw]
  · simp [Finset.mem_symmDiff, hw]

open Classical in
/-- `Δ_S(v)` depends only on `S ∖ {v}`, so toggling `v` does not change it. -/
theorem cutDeviation_symmDiff (G : Graph n) (p : ℝ) (S : Finset (Fin n)) (v : Fin n) :
    cutDeviation G p (S ∆ {v}) v = cutDeviation G p S v := by
  unfold cutDeviation
  rw [← cutDegree_erase G (S ∆ {v}) v, erase_symmDiff_singleton, cutDegree_erase]

open Classical in
theorem cutDeviation_of_notMem (G : Graph n) (p : ℝ) (S : Finset (Fin n)) (v : Fin n)
    (hv : v ∉ S) : cutDeviation G p S v = (cutDegree G S v : ℝ) - p * (S.card : ℝ) := by
  unfold cutDeviation
  rw [Finset.erase_eq_of_notMem hv]

/-! ### Averaging over all cuts -/

/-- Toggling `v` is an involution of `Finset (Fin n)`. -/
def toggle (v : Fin n) : Equiv.Perm (Finset (Fin n)) :=
  Function.Involutive.toPerm (fun S ↦ S ∆ {v}) fun S ↦ symmDiff_symmDiff_cancel_right {v} S

@[simp] theorem toggle_apply (v : Fin n) (S : Finset (Fin n)) : toggle v S = S ∆ {v} := rfl

/-- Complementation is an involution of `Finset (Fin n)`. -/
def complPerm : Equiv.Perm (Finset (Fin n)) :=
  Function.Involutive.toPerm (fun S ↦ Sᶜ) fun S ↦ compl_compl S

@[simp] theorem complPerm_apply (S : Finset (Fin n)) : complPerm S = Sᶜ := rfl

theorem mem_symmDiff_singleton_self (S : Finset (Fin n)) (v : Fin n) :
    v ∈ S ∆ {v} ↔ v ∉ S := by
  simp [Finset.mem_symmDiff]

open Classical in
/-- For a fixed vertex, the cuts not containing it carry half of the total squared deviation. -/
theorem sum_cutDeviation_sq_notMem (G : Graph n) (p : ℝ) (v : Fin n) :
    ∑ S : Finset (Fin n), (if v ∈ S then 0 else cutDeviation G p S v ^ 2) =
      (1 / 2) * ∑ S : Finset (Fin n), cutDeviation G p S v ^ 2 := by
  have hswap : ∑ S : Finset (Fin n), (if v ∈ S then cutDeviation G p S v ^ 2 else 0) =
      ∑ S : Finset (Fin n), (if v ∈ S then 0 else cutDeviation G p S v ^ 2) := by
    rw [← Equiv.sum_comp (toggle v)]
    refine Finset.sum_congr rfl fun S _ ↦ ?_
    simp only [toggle_apply, mem_symmDiff_singleton_self, cutDeviation_symmDiff]
    split_ifs <;> simp_all
  have htotal : ∑ S : Finset (Fin n), (if v ∈ S then 0 else cutDeviation G p S v ^ 2) +
      ∑ S : Finset (Fin n), (if v ∈ S then cutDeviation G p S v ^ 2 else 0) =
      ∑ S : Finset (Fin n), cutDeviation G p S v ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun S _ ↦ ?_
    split_ifs <;> simp
  linarith

open Classical in
theorem sum_cutDeviation_sq_compl (G : Graph n) (p : ℝ) (v : Fin n) :
    ∑ S : Finset (Fin n), cutDeviation G p S v ^ 2 =
      ∑ S : Finset (Fin n), cutDeviation G p Sᶜ v ^ 2 := by
  rw [← Equiv.sum_comp complPerm]
  rfl

open Classical in
/-- The manuscript's averaging inequality for one vertex:
`∑_S 1_{v ∉ S} Δ_S(v)² ≥ (2^n / 8) (d_v - p(n-1))²`. -/
theorem sum_cutDeviation_sq_notMem_ge (G : Graph n) (p : ℝ) (v : Fin n) :
    ((2 : ℝ) ^ n / 8) * ((G.degree v : ℝ) - p * ((n : ℝ) - 1)) ^ 2 ≤
      ∑ S : Finset (Fin n), (if v ∈ S then 0 else cutDeviation G p S v ^ 2) := by
  rw [sum_cutDeviation_sq_notMem]
  have hhalf : ∑ S : Finset (Fin n), cutDeviation G p S v ^ 2 =
      (1 / 2) * ∑ S : Finset (Fin n),
        (cutDeviation G p S v ^ 2 + cutDeviation G p Sᶜ v ^ 2) := by
    rw [Finset.sum_add_distrib, ← sum_cutDeviation_sq_compl]
    ring
  have hpt : ∀ S : Finset (Fin n),
      (1 / 2) * ((G.degree v : ℝ) - p * ((n : ℝ) - 1)) ^ 2 ≤
        cutDeviation G p S v ^ 2 + cutDeviation G p Sᶜ v ^ 2 := by
    intro S
    rw [← cutDeviation_add_compl G p S v]
    nlinarith [sq_nonneg (cutDeviation G p S v - cutDeviation G p Sᶜ v)]
  have hsum := Finset.sum_le_sum fun S (_ : S ∈ (Finset.univ : Finset (Finset (Fin n)))) ↦ hpt S
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [hhalf]
  push_cast at hsum
  linarith

open Classical in
/-- The random-cut covering: if `∑_v (d_v - p(n-1))² ≥ 8t`, some cut `S` has
`∑_{v ∉ S} (deg_S v - p|S|)² ≥ t`. -/
theorem exists_cut_of_spread (G : Graph n) (p t : ℝ)
    (h : 8 * t ≤ ∑ v, ((G.degree v : ℝ) - p * ((n : ℝ) - 1)) ^ 2) :
    ∃ S : Finset (Fin n), t ≤ ∑ v ∈ Sᶜ, ((cutDegree G S v : ℝ) - p * (S.card : ℝ)) ^ 2 := by
  -- the double sum over all cuts
  have hdouble : ((2 : ℝ) ^ n) * t ≤ ∑ S : Finset (Fin n),
      ∑ v, (if v ∈ S then 0 else cutDeviation G p S v ^ 2) := by
    rw [Finset.sum_comm]
    calc ((2 : ℝ) ^ n) * t = ((2 : ℝ) ^ n / 8) * (8 * t) := by ring
      _ ≤ ((2 : ℝ) ^ n / 8) * ∑ v, ((G.degree v : ℝ) - p * ((n : ℝ) - 1)) ^ 2 :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = ∑ v, ((2 : ℝ) ^ n / 8) * ((G.degree v : ℝ) - p * ((n : ℝ) - 1)) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum fun v _ ↦ sum_cutDeviation_sq_notMem_ge G p v
  by_contra hcon
  push Not at hcon
  have hlt : ∑ S : Finset (Fin n), ∑ v, (if v ∈ S then 0 else cutDeviation G p S v ^ 2) <
      ∑ _S : Finset (Fin n), t := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro S _
    have hS := hcon S
    have heq : ∑ v, (if v ∈ S then 0 else cutDeviation G p S v ^ 2) =
        ∑ v ∈ Sᶜ, ((cutDegree G S v : ℝ) - p * (S.card : ℝ)) ^ 2 := by
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
      refine Finset.sum_congr (by ext w; simp) fun v hv ↦ ?_
      rw [cutDeviation_of_notMem G p S v (Finset.mem_compl.mp hv)]
    rw [heq]
    exact hS
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
    nsmul_eq_mul] at hlt
  push_cast at hlt
  linarith

end MajorityDynamics.Probability.DegreeConcentration
