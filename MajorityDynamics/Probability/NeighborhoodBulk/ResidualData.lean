import MajorityDynamics.Probability.NeighborhoodBulk.Relabel
import MajorityDynamics.Probability.NeighborhoodBulk.Regularity

/-! Exact sums and carrier conversions for vertex deletion. These statements
do not require the original or residual degree sequence to be graphical. -/
noncomputable section
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodBulk
open FixedDegreeSampling
variable {V L R : Type*} [Fintype V] [Fintype L] [Fintype R]

theorem remaining_card (v : V) : Fintype.card (Remaining v) = Fintype.card V - 1 := by
  simpa only [Fintype.card_unique] using Fintype.card_subtype_compl (fun u : V => u = v)

theorem sum_remaining_add {M : Type*} [AddCommMonoid M] (f : V → M) (v : V) :
    (∑ u : Remaining v, f u) + f v = ∑ u, f u := by
  rw [← Finset.sum_subtype (Finset.univ.erase v) (by simp)]
  exact Finset.sum_erase_add _ _ (Finset.mem_univ v)

theorem sum_remaining_indicator (v : V) (S : Finset V) (hv : v ∉ S) :
    (∑ u : Remaining v, if u.val ∈ S then 1 else 0 : ℕ) = S.card := by
  have hs := sum_remaining_add (fun u : V => if u ∈ S then (1 : ℕ) else 0) v
  simpa [hv] using hs

theorem sum_residualDegree (d : V → ℕ) (v : V) (S : Finset V)
    (h : graphAdmissible d v S) (m : ℕ) (hs : ∑ u, d u = 2 * m) :
    d v ≤ m ∧ (∑ u, residualDegree d v S u) = 2 * (m - d v) := by
  have hh := congrArg (fun f : Remaining v → ℕ => ∑ u, f u)
    (funext (residualDegree_add d v S h))
  simp only [Finset.sum_add_distrib] at hh
  rw [sum_remaining_indicator v S h.1, h.2.1] at hh
  have hsum := sum_remaining_add d v
  rw [hs] at hsum
  omega

theorem sum_residualRightDegree (b : R → ℕ) (S : Finset R)
    (h : ∀ j ∈ S, 1 ≤ b j) :
    (∑ j, residualRightDegree b S j) + S.card = ∑ j, b j := by
  have hh : ∀ j, residualRightDegree b S j + (if j ∈ S then 1 else 0) = b j := by
    intro j
    unfold residualRightDegree
    apply Nat.sub_add_cancel
    split_ifs with hj
    · exact h j hj
    · omega
  have he := congrArg (fun f : R → ℕ => ∑ j, f j) (funext hh)
  simpa only [Finset.sum_add_distrib, Finset.sum_boole, Finset.filter_mem_eq_inter,
    Finset.univ_inter, Nat.cast_id] using he

theorem bipartite_residual_sums (a : L → ℕ) (b : R → ℕ) (v : L) (S : Finset R)
    (h : bipartiteAdmissible a b v S) (m : ℕ) (ha : ∑ i, a i = m) (hb : ∑ j, b j = m) :
    a v ≤ m ∧ (∑ i : Remaining v, a i) = m - a v ∧
      (∑ j, residualRightDegree b S j) = m - a v := by
  have hl := sum_remaining_add a v
  have hr := sum_residualRightDegree b S h.2
  rw [ha] at hl
  rw [hb, h.1] at hr
  omega

def remainingEquiv {n : ℕ} (v : Fin n) : Remaining v ≃ Fin (n - 1) :=
  Fintype.equivFinOfCardEq (by
    convert remaining_card v using 1
    · exact congrArg (@Fintype.card (Remaining v)) (Subsingleton.elim _ _)
    · simp)

def graphResidualFin {n : ℕ} (d : Fin n → ℕ) (v : Fin n) (S : Finset (Fin n)) : Fin (n - 1) → ℕ :=
  fun i => residualDegree d v S ((remainingEquiv v).symm i)

theorem graphResidualFin_sum {n : ℕ} (d : Fin n → ℕ) (v : Fin n) (S : Finset (Fin n))
    (h : graphAdmissible d v S) (m : ℕ) (hs : ∑ i, d i = 2 * m) :
    (∑ i, graphResidualFin d v S i) = 2 * (m - d v) := by
  unfold graphResidualFin
  rw [(remainingEquiv v).symm.sum_comp]
  convert (sum_residualDegree d v S h m hs).2 using 1
  congr 1
  ext u
  simp

theorem graphResidualFin_count {n : ℕ} (d : Fin n → ℕ) (v : Fin n) (S : Finset (Fin n)) :
    graphCount (graphResidualFin d v S) = graphCount (residualDegree d v S) :=
  graphCount_relabel (remainingEquiv v) (residualDegree d v S)

def leftResidualFin {ell : ℕ} (a : Fin ell → ℕ) (v : Fin ell) : Fin (ell - 1) → ℕ :=
  fun i => a ((remainingEquiv v).symm i)

theorem leftResidualFin_sum {ell : ℕ} (a : Fin ell → ℕ) (v : Fin ell) :
    (∑ i, leftResidualFin a v i) + a v = ∑ i, a i := by
  unfold leftResidualFin
  rw [(remainingEquiv v).symm.sum_comp (fun u : Remaining v => a u)]
  convert sum_remaining_add a v using 1
  congr 2
  ext u
  simp

theorem bipartiteResidualFin_count {ell n : ℕ} (a : Fin ell → ℕ) (b : Fin n → ℕ)
    (v : Fin ell) (S : Finset (Fin n)) :
    bipartiteCount (leftResidualFin a v) (residualRightDegree b S) =
      bipartiteCount (fun u : Remaining v => a u) (residualRightDegree b S) := by
  exact bipartiteCount_relabel (remainingEquiv v) (Equiv.refl (Fin n))
    (fun u : Remaining v => a u) (residualRightDegree b S)

theorem decrement_deviation (d : ℕ) (x B : ℝ) (h : |(d : ℝ) - x| ≤ B)
    (step : ℕ) (hstep : step ≤ 1) (hd : step ≤ d) :
    |((d - step : ℕ) : ℝ) - x| ≤ B + 1 := by
  rw [Nat.cast_sub hd]
  have hs : (step : ℝ) ≤ 1 := by exact_mod_cast hstep
  calc
    _ = |((d : ℝ) - x) - step| := by congr 1; ring
    _ ≤ |(d : ℝ) - x| + |(step : ℝ)| := abs_sub _ _
    _ ≤ B + 1 := by rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ step)]; linarith

theorem graphResidualFin_deviation {n : ℕ} (d : Fin n → ℕ) (v : Fin n) (S : Finset (Fin n))
    (h : graphAdmissible d v S) (x B : ℝ) (hd : ∀ i, |(d i : ℝ) - x| ≤ B) :
    ∀ i, |(graphResidualFin d v S i : ℝ) - x| ≤ B + 1 := by
  intro i
  apply decrement_deviation _ x B (hd _) _ (by split_ifs <;> omega)
  split_ifs with hi
  · exact h.2.2 _ hi
  · omega

omit [Fintype R] in
theorem residualRightDegree_deviation (b : R → ℕ) (S : Finset R)
    (h : ∀ j ∈ S, 1 ≤ b j) (x B : ℝ) (hb : ∀ j, |(b j : ℝ) - x| ≤ B) :
    ∀ j, |(residualRightDegree b S j : ℝ) - x| ≤ B + 1 := by
  intro j
  apply decrement_deviation _ x B (hb j) _ (by split_ifs <;> omega)
  split_ifs with hj
  · exact h j hj
  · omega

end MajorityDynamics.Probability.NeighborhoodBulk
