import MajorityDynamics.GraphProcess.GammaNumerator.Restrictions
import MajorityDynamics.GraphProcess.RowArray.Statistics

/-! Exact block degree statistics and the deterministic reduction to A.10. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.GammaNumerator
open Universal
open MajorityDynamics.Probability.DegreeConcentration
variable {V : Type*} [Fintype V] {n : ℕ}

theorem sum_vertex (π : V → History (n + 1)) (s : History (n + 1))
    {A : Type*} [AddCommMonoid A] (f : V → A) :
    ∑ i, f (vertex π s i) = ∑ v ∈ History.block π s, f v := by
  calc
    _ = ∑ v : {v : V // π v = s}, f v :=
      (blockEquiv π s).sum_comp (fun v => f v.val)
    _ = _ := (Finset.sum_subtype (History.block π s)
      (fun v => History.mem_block π s v) f).symm

theorem internal_degree (π : V → History (n + 1)) (s : History (n + 1))
    (G : SimpleGraph V) (i : Fin (blockSize π s)) :
    graphDegree (internal π s G) i =
      (RowArray.values (RowArray.graphArray π G) (vertex π s i) s : ℝ) := by
  have h : ((internal π s G).degree i : ℤ) =
      History.degreeArray π G (vertex π s i) s := by
    rw [History.graph_degree_eq_sum]
    change (∑ j, if G.Adj (vertex π s i) (vertex π s j) then (1 : ℤ) else 0) = _
    exact sum_vertex π s (fun v => if G.Adj (vertex π s i) v then (1 : ℤ) else 0)
  simpa only [graphDegree, RowArray.values_graphArray, Int.cast_natCast] using
    congrArg (fun z : ℤ => (z : ℝ)) h

theorem cross_left_degree (π : V → History (n + 1)) (s t : History (n + 1))
    (G : SimpleGraph V) (i : Fin (blockSize π s)) :
    leftDegree (cross π s t G) i =
      (RowArray.values (RowArray.graphArray π G) (vertex π s i) t : ℝ) := by
  rw [leftDegree, RowArray.values_graphArray]
  have h := sum_vertex π t (fun v => if G.Adj (vertex π s i) v then (1 : ℤ) else 0)
  change (∑ j, if G.Adj (vertex π s i) (vertex π t j) then (1 : ℤ) else 0) =
    History.degreeArray π G (vertex π s i) t at h
  simp only [Finset.sum_boole] at h
  convert (show
    ((Finset.univ.filter fun j => G.Adj (vertex π s i) (vertex π t j)).card : ℝ) =
      (History.degreeArray π G (vertex π s i) t : ℝ) by exact_mod_cast h) using 1
  congr 2

theorem cross_right_degree (π : V → History (n + 1)) (s t : History (n + 1))
    (G : SimpleGraph V) (j : Fin (blockSize π t)) :
    rightDegree (cross π s t G) j =
      (RowArray.values (RowArray.graphArray π G) (vertex π t j) s : ℝ) := by
  rw [rightDegree, RowArray.values_graphArray]
  have h : (∑ i, if G.Adj (vertex π s i) (vertex π t j) then (1 : ℤ) else 0) =
      History.degreeArray π G (vertex π t j) s := by
    rw [sum_vertex π s (fun v => if G.Adj v (vertex π t j) then (1 : ℤ) else 0)]
    unfold History.degreeArray
    apply Finset.sum_congr rfl
    intro v hv
    rw [G.adj_comm v (vertex π t j)]
  simp only [Finset.sum_boole] at h
  convert (show
    ((Finset.univ.filter fun i => G.Adj (vertex π s i) (vertex π t j)).card : ℝ) =
      (History.degreeArray π G (vertex π t j) s : ℝ) by exact_mod_cast h) using 1
  congr 2

theorem sum_values (π : V → History (n + 1)) (s t : History (n + 1))
    (G : SimpleGraph V) :
    ∑ i, (RowArray.values (RowArray.graphArray π G) (vertex π s i) t : ℝ) =
      (RowArray.totals (RowArray.graphArray π G) s t : ℝ) := by
  rw [sum_vertex π s (fun v => (RowArray.values (RowArray.graphArray π G) v t : ℝ))]
  simp only [RowArray.totals, History.edgeTotals, Int.cast_sum]

theorem actual_totals_symm (π : V → History (n + 1)) (G : SimpleGraph V)
    (s t : History (n + 1)) :
    RowArray.totals (RowArray.graphArray π G) s t =
      RowArray.totals (RowArray.graphArray π G) t s := by
  simp only [RowArray.totals_graphArray]
  exact History.edgeTotals_symm π G s t

theorem internal_mean (π : V → History (n + 1)) (s : History (n + 1))
    (G : SimpleGraph V) :
    graphDegreeMean (internal π s G) =
      (RowArray.totals (RowArray.graphArray π G) s s : ℝ) /
        (Local.partSizes π s : ℝ) := by
  simp only [graphDegreeMean, internal_degree, sum_values, blockSize_eq]

theorem cross_left_mean (π : V → History (n + 1)) (s t : History (n + 1))
    (G : SimpleGraph V) :
    leftDegreeMean (cross π s t G) =
      (RowArray.totals (RowArray.graphArray π G) s t : ℝ) /
        (Local.partSizes π s : ℝ) := by
  simp only [leftDegreeMean, cross_left_degree, sum_values, blockSize_eq]

theorem cross_right_mean (π : V → History (n + 1)) (s t : History (n + 1))
    (G : SimpleGraph V) :
    rightDegreeMean (cross π s t G) =
      (RowArray.totals (RowArray.graphArray π G) t s : ℝ) /
        (Local.partSizes π t : ℝ) := by
  simp only [rightDegreeMean, cross_right_degree, sum_values, blockSize_eq]

/-- The unnormalized numerator in the original Gamma predicate. -/
def squareSum (π : V → History (n + 1)) (G : SimpleGraph V)
    (s t : History (n + 1)) : ℝ :=
  ∑ v ∈ History.block π s,
    ((RowArray.values (RowArray.graphArray π G) v t : ℝ) -
      (RowArray.totals (RowArray.graphArray π G) s t : ℝ) /
        (Local.partSizes π s : ℝ)) ^ 2

theorem internal_squareSum (π : V → History (n + 1)) (s : History (n + 1))
    (G : SimpleGraph V) : graphSquareSum (internal π s G) = squareSum π G s s := by
  simp only [graphSquareSum, internal_degree, internal_mean, squareSum]
  exact sum_vertex π s (fun v =>
    ((RowArray.values (RowArray.graphArray π G) v s : ℝ) -
      (RowArray.totals (RowArray.graphArray π G) s s : ℝ) /
        (Local.partSizes π s : ℝ)) ^ 2)

theorem cross_left_squareSum (π : V → History (n + 1)) (s t : History (n + 1))
    (G : SimpleGraph V) : leftSquareSum (cross π s t G) = squareSum π G s t := by
  simp only [leftSquareSum, cross_left_degree, cross_left_mean, squareSum]
  exact sum_vertex π s (fun v =>
    ((RowArray.values (RowArray.graphArray π G) v t : ℝ) -
      (RowArray.totals (RowArray.graphArray π G) s t : ℝ) /
        (Local.partSizes π s : ℝ)) ^ 2)

theorem cross_right_squareSum (π : V → History (n + 1)) (s t : History (n + 1))
    (G : SimpleGraph V) : rightSquareSum (cross π s t G) = squareSum π G t s := by
  simp only [rightSquareSum, cross_right_degree, cross_right_mean, squareSum]
  exact sum_vertex π t (fun v =>
    ((RowArray.values (RowArray.graphArray π G) v s : ℝ) -
      (RowArray.totals (RowArray.graphArray π G) t s : ℝ) /
        (Local.partSizes π t : ℝ)) ^ 2)

theorem internal_truncation (π : V → History (n + 1)) (G : SimpleGraph V)
    (p : ℝ) (hreg : RowArray.Regular p (RowArray.graphArray π G))
    (htol : ∀ s, (p * (Fintype.card V : ℝ)) ^ (4 / 7 : ℝ) ≤
      p * (Local.partSizes π s : ℝ)) (s : History (n + 1)) :
    internal π s G ∈ graphTruncation (blockSize π s) p := by
  intro i
  rw [internal_degree, blockSize_eq]
  exact (hreg (vertex π s i) s).trans (htol s)

theorem cross_truncation (π : V → History (n + 1)) (G : SimpleGraph V)
    (p : ℝ) (hreg : RowArray.Regular p (RowArray.graphArray π G))
    (htol : ∀ s, (p * (Fintype.card V : ℝ)) ^ (4 / 7 : ℝ) ≤
      p * (Local.partSizes π s : ℝ)) (s t : History (n + 1)) :
    cross π s t G ∈ bipartiteTruncation (blockSize π s) (blockSize π t) p := by
  constructor
  · intro i
    rw [cross_left_degree, blockSize_eq]
    exact (hreg (vertex π s i) t).trans (htol t)
  · intro j
    rw [cross_right_degree, blockSize_eq, blockSize_eq]
    exact (hreg (vertex π t j) s).trans (htol t)

/-- Ordered-pair A.10 events; both directed cross failures are covered. -/
def blockBad (π : V → History (n + 1)) (C p : ℝ) (s t : History (n + 1)) :
    Set (SimpleGraph V) :=
  if s = t then (internal π s) ⁻¹' graphBad (blockSize π s) C p
  else (cross π s t) ⁻¹' bipartiteBad (blockSize π s) (blockSize π t) C p

theorem blockSize_le (π : V → History (n + 1)) (s : History (n + 1)) :
    blockSize π s ≤ Fintype.card V := by
  rw [blockSize_eq, ← History.block_card_partSizes]
  exact Finset.card_le_univ _

theorem event_subset_iUnion (π : V → History (n + 1)) (C p : ℝ)
    (hp : 0 < p) (hC : 0 ≤ C)
    (htol : ∀ s, (p * (Fintype.card V : ℝ)) ^ (4 / 7 : ℝ) ≤
      p * (Local.partSizes π s : ℝ)) :
    {G | ¬ RowArray.Gamma π (RowArray.totals (RowArray.graphArray π G))
        C p (RowArray.graphArray π G) ∧
      RowArray.Regular p (RowArray.graphArray π G)} ⊆
      ⋃ s, ⋃ t, blockBad π C p s t := by
  rintro G ⟨hbad, hreg⟩
  have hN : 0 < (Fintype.card V : ℝ) := by
    by_contra h
    have hz : (Fintype.card V : ℝ) = 0 := le_antisymm (le_of_not_gt h) (by positivity)
    exact hbad (by simp [RowArray.Gamma, hz, hC])
  obtain ⟨s, hsbad⟩ := not_forall.mp hbad
  obtain ⟨t, hst⟩ := not_forall.mp hsbad
  have hden : 0 < p * (Fintype.card V : ℝ) ^ 2 := mul_pos hp (sq_pos_of_pos hN)
  have hlarge : C * p * (Fintype.card V : ℝ) ^ 2 < squareSum π G s t := by
    have hlt : C < squareSum π G s t / (p * (Fintype.card V : ℝ)^2) := by
      simpa only [squareSum, one_div, ← div_eq_inv_mul] using lt_of_not_ge hst
    have := (lt_div_iff₀ hden).mp hlt
    nlinarith
  have hs : (blockSize π s : ℝ) ≤ Fintype.card V := by exact_mod_cast blockSize_le π s
  have ht : (blockSize π t : ℝ) ≤ Fintype.card V := by exact_mod_cast blockSize_le π t
  have hs0 : 0 ≤ (blockSize π s : ℝ) := by positivity
  have ht0 : 0 ≤ (blockSize π t : ℝ) := by positivity
  have hCp : 0 ≤ C * p := mul_nonneg hC hp.le
  apply Set.mem_iUnion.mpr
  refine ⟨s, Set.mem_iUnion.mpr ⟨t, ?_⟩⟩
  by_cases heq : s = t
  · subst t
    rw [blockBad, if_pos rfl]
    refine ⟨?_, internal_truncation π G p hreg htol s⟩
    change C * p * (blockSize π s : ℝ)^2 ≤ graphSquareSum (internal π s G)
    rw [internal_squareSum]
    have hsq : (blockSize π s : ℝ)^2 ≤ (Fintype.card V : ℝ)^2 :=
      sq_le_sq₀ hs0 hN.le |>.mpr hs
    exact (mul_le_mul_of_nonneg_left hsq hCp).trans hlarge.le
  · rw [blockBad, if_neg heq]
    refine ⟨Or.inl ?_, cross_truncation π G p hreg htol s t⟩
    rw [cross_left_squareSum]
    have hprod : (blockSize π s : ℝ) * (blockSize π t : ℝ) ≤
        (Fintype.card V : ℝ)^2 := by
      calc
        _ ≤ (Fintype.card V : ℝ) * Fintype.card V := mul_le_mul hs ht ht0 hN.le
        _ = _ := (pow_two _).symm
    have hscale := mul_le_mul_of_nonneg_left hprod hCp
    nlinarith

end MajorityDynamics.GraphProcess.GammaNumerator
