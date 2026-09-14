import MajorityDynamics.Literature.DegreeEnumeration.Consequences

noncomputable section
open scoped Classical
namespace MajorityDynamics.Literature.DegreeEnumeration
open MajorityDynamics.Probability.FixedDegreeSampling

def graphCountModel {n : ℕ} (m : ℕ) (d : Fin n → ℕ) : ℝ :=
  (((n.choose 2).choose m : ℝ) / ((n * (n - 1)).choose (2 * m) : ℝ)) *
    ∏ i, ((n - 1).choose (d i) : ℝ)

def bipartiteCountModel {ell n : ℕ} (m : ℕ) (a : Fin ell → ℕ) (b : Fin n → ℕ) : ℝ :=
  ((∏ i, (n.choose (a i) : ℝ)) * ∏ j, (ell.choose (b j) : ℝ)) /
    ((ell * n).choose m : ℝ)

theorem graph_degree_total_capacity {n m : ℕ} (d : Fin n → ℕ)
    (hd : ∀ i, d i ≤ n - 1) (hs : ∑ i, d i = 2 * m) : 2 * m ≤ n * (n - 1) := by
  calc
    _ = ∑ i, d i := hs.symm
    _ ≤ ∑ _ : Fin n, (n - 1) := Finset.sum_le_sum (fun i _ => hd i)
    _ = _ := by simp

theorem graphCountModel_pos {n m : ℕ} (d : Fin n → ℕ) (hm : m ≤ n.choose 2)
    (hd : ∀ i, d i ≤ n - 1) (hs : ∑ i, d i = 2 * m) : 0 < graphCountModel m d := by
  unfold graphCountModel
  apply mul_pos
  · exact div_pos (by exact_mod_cast Nat.choose_pos hm)
      (by exact_mod_cast Nat.choose_pos (graph_degree_total_capacity d hd hs))
  · exact Finset.prod_pos (fun i _ => by exact_mod_cast Nat.choose_pos (hd i))

theorem bipartiteCountModel_pos {ell n m : ℕ} (a : Fin ell → ℕ) (b : Fin n → ℕ)
    (hm : m ≤ ell * n) (ha : ∀ i, a i ≤ n) (hb : ∀ j, b j ≤ ell) :
    0 < bipartiteCountModel m a b := by
  unfold bipartiteCountModel
  apply div_pos
  · exact mul_pos (Finset.prod_pos (fun i _ => by exact_mod_cast Nat.choose_pos (ha i)))
      (Finset.prod_pos (fun j _ => by exact_mod_cast Nat.choose_pos (hb j)))
  · exact_mod_cast Nat.choose_pos hm

theorem graph_count_relative {n m : ℕ} {δ : ℝ} (d : Fin n → ℕ)
    (hm : m ≤ n.choose 2) (hd : ∀ i, d i ≤ n - 1) (hs : ∑ i, d i = 2 * m)
    (h : RelativeApproximation δ ((graphDegreeLaw (Fin n) m).real {d})
      ((graphBinomialLaw (Fin n) m).real {d} * graphCorrection m d)) :
    RelativeApproximation δ (graphCount d : ℝ) (graphCountModel m d * graphCorrection m d) := by
  obtain ⟨ε, hε, he⟩ := h
  rw [graphDegreeLaw_real_atom d m hs,
    graphBinomialLaw_atom m d (by simpa using graph_degree_total_capacity d hd hs) hs] at he
  simp only [Fintype.card_fin] at he
  have hc : ((n.choose 2).choose m : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hm).ne'
  have hh := (div_eq_iff hc).mp he
  refine ⟨ε, hε, ?_⟩
  rw [hh]
  unfold graphCountModel
  ring

theorem bipartite_count_relative {ell n m : ℕ} {δ : ℝ} (a : Fin ell → ℕ) (b : Fin n → ℕ)
    (hm : m ≤ ell * n) (ha : ∑ i, a i = m) (hb : ∑ j, b j = m)
    (h : RelativeApproximation δ ((bipartiteDegreeLaw (Fin ell) (Fin n) m).real {(a, b)})
      ((bipartiteBinomialLaw (Fin ell) (Fin n) m).real {(a, b)} * bipartiteCorrection m a b)) :
    RelativeApproximation δ (bipartiteCount a b : ℝ)
      (bipartiteCountModel m a b * bipartiteCorrection m a b) := by
  obtain ⟨ε, hε, he⟩ := h
  rw [bipartiteDegreeLaw_real_atom a b m ha,
    bipartiteBinomialLaw_atom m a b (by simpa using hm) ha hb] at he
  simp only [Fintype.card_fin] at he
  have hc : ((ell * n).choose m : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hm).ne'
  have hh := (div_eq_iff hc).mp he
  refine ⟨ε, hε, ?_⟩
  rw [hh]
  unfold bipartiteCountModel
  field_simp

end MajorityDynamics.Literature.DegreeEnumeration
