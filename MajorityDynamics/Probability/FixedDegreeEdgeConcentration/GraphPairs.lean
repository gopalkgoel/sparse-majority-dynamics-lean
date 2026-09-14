import MajorityDynamics.Probability.FixedDegreeSampling.Laws

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
namespace MajorityDynamics.Probability.FixedDegreeEdgeConcentration
open FixedDegreeSampling

/-- Event probabilities under equivalent finite uniform families, including empty families. -/
theorem uniform_event_of_equiv {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace Ω'] [MeasurableSingletonClass Ω']
    (s : Set Ω) (s' : Set Ω') (e : s ≃ s') (A : Set Ω) (A' : Set Ω')
    (he : ∀ x : s, x.val ∈ A ↔ (e x).val ∈ A') :
    (uniformOn s).real A = (uniformOn s').real A' := by
  have ec : (s ∩ A : Set Ω) ≃ (s' ∩ A' : Set Ω') :=
    { toFun := fun x => ⟨(e ⟨x.val, x.property.1⟩).val,
        (e ⟨x.val, x.property.1⟩).property, (he _).1 x.property.2⟩
      invFun := fun x => ⟨(e.symm ⟨x.val, x.property.1⟩).val,
        (e.symm ⟨x.val, x.property.1⟩).property, by
          apply (he _).2
          simpa using x.property.2⟩
      left_inv := by intro x; apply Subtype.ext; simp
      right_inv := by intro x; apply Subtype.ext; simp }
  unfold Measure.real
  rw [uniform_apply, uniform_apply, Set.ncard_congr' e, Set.ncard_congr' ec]

/-- A finite partition into actual fibers decomposes an event exactly. -/
theorem real_partition {Ω I : Type*} [Fintype Ω] [Fintype I]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (π : Ω → I) (A : Set I) (F : Set Ω) :
    μ.real {ω | π ω ∈ A ∧ ω ∈ F} =
      ∑ i : A, μ.real ({ω | π ω = i.val} ∩ F) := by
  have hu : {ω | π ω ∈ A ∧ ω ∈ F} =
      ⋃ i : A, ({ω | π ω = i.val} ∩ F) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨hA,hF⟩
      exact ⟨⟨π ω,hA⟩,rfl,hF⟩
    · rintro ⟨i,hi,hF⟩
      exact ⟨hi ▸ i.property,hF⟩
  rw [hu]
  apply measureReal_iUnion_fintype
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro ω ⟨hi,_⟩ ⟨hj,_⟩
    exact hij (Subtype.ext (hi.symm.trans hj))
  · intro i
    exact (Set.toFinite _).measurableSet
  · intro i
    exact measure_ne_top _ _

/-- Uniform finite-fiber averaging. Bounds are only needed on nonempty fibers. -/
theorem uniform_partition_upper {Ω I : Type*} [Fintype Ω] [Fintype I]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (s : Set Ω) (π : Ω → I) (A : Set I) (F : Set Ω) {B : ℝ}
    (h : ∀ i ∈ A, (s ∩ {ω | π ω = i}).Nonempty →
      (uniformOn (s ∩ {ω | π ω = i})).real F ≤ B) :
    (uniformOn s).real {ω | π ω ∈ A ∧ ω ∈ F} ≤
      (uniformOn s).real {ω | π ω ∈ A} * B := by
  rw [real_partition (uniformOn s) π A F]
  have hm := real_partition (uniformOn s) π A Set.univ
  simp only [Set.mem_univ, and_true, Set.inter_univ] at hm
  rw [hm, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have hi : (uniformOn s).real ({ω | π ω = i.val} ∩ F) =
      (uniformOn (s ∩ {ω | π ω = i.val})).real F *
        (uniformOn s).real {ω | π ω = i.val} := by
    unfold Measure.real
    rw [uniformOn_inter (Set.toFinite s), ENNReal.toReal_mul]
  rw [hi]
  by_cases hn : (s ∩ {ω | π ω = i.val}).Nonempty
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_right
      (h i.val i.property hn) (measureReal_nonneg)
  · have he : s ∩ {ω | π ω = i.val} = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have hz : (uniformOn s).real {ω | π ω = i.val} = 0 := by
      unfold Measure.real
      rw [uniform_apply, he]
      simp
    rw [hz, mul_zero, zero_mul]

/-- Conditioning on an exact admissible neighborhood leaves the actual residual edge law. -/
theorem graph_fiber_edge_probability {V : Type*} [Fintype V]
    (d : V → ℕ) (v : V) (R : Finset V) (hR : graphAdmissible d v R)
    (x y : V) (hx : x ≠ v) (hy : y ≠ v) :
    (uniformOn (graphFamily d ∩ {G | G.neighborFinset v = R})).real
      {G | G.Adj x y} =
      (fixedDegreeLaw (residualDegree d v R)).real
        {H | H.Adj ⟨x,hx⟩ ⟨y,hy⟩} := by
  apply uniform_event_of_equiv _ _ (graph_neighborhood_removal_equiv d v R hR)
  intro G
  rfl

/-- Exact neighborhood disintegration of a surviving edge, including empty residual fibers. -/
theorem graph_neighborhood_edge_probability {V : Type*} [Fintype V]
    (d : V → ℕ) (v : V) (R : Finset V) (hR : graphAdmissible d v R)
    (x y : V) (hx : x ≠ v) (hy : y ≠ v) :
    (fixedDegreeLaw d).real {G | G.neighborFinset v = R ∧ G.Adj x y} =
      (fixedDegreeLaw d).real {G | G.neighborFinset v = R} *
      (fixedDegreeLaw (residualDegree d v R)).real {H | H.Adj ⟨x,hx⟩ ⟨y,hy⟩} := by
  change (uniformOn (graphFamily d)).real
    ({G | G.neighborFinset v = R} ∩ {G | G.Adj x y}) = _
  have h := congrArg ENNReal.toReal (uniformOn_inter (s := graphFamily d)
    (t := {G | G.neighborFinset v = R}) (u := {G | G.Adj x y}) (Set.toFinite _))
  simp only [ENNReal.toReal_mul] at h
  change _ = (uniformOn (graphFamily d ∩ {G | G.neighborFinset v = R})).real
    {G | G.Adj x y} * (fixedDegreeLaw d).real {G | G.neighborFinset v = R} at h
  rw [graph_fiber_edge_probability d v R hR x y hx hy] at h
  simpa only [Measure.real, mul_comm] using h

/-- A residual single-edge upper bound gives the actual joint upper bound.
Only feasible neighborhoods containing the first edge need a bound. No
normalization premise is needed: empty original and residual families are exact. -/
theorem graph_pair_upper {V : Type*} [Fintype V]
    (d : V → ℕ) (v u x y : V) (hx : x ≠ v) (hy : y ≠ v) {B : ℝ}
    (hres : ∀ R : Finset V, graphAdmissible d v R →
      (graphFamily (residualDegree d v R)).Nonempty → u ∈ R →
      (fixedDegreeLaw (residualDegree d v R)).real
        {H | H.Adj ⟨x,hx⟩ ⟨y,hy⟩} ≤ B) :
    (fixedDegreeLaw d).real {G | G.Adj v u ∧ G.Adj x y} ≤
      (fixedDegreeLaw d).real {G | G.Adj v u} * B := by
  have h := uniform_partition_upper (graphFamily d) (fun G => G.neighborFinset v)
    {R | u ∈ R} {G | G.Adj x y} (B := B) (by
      intro R hu hnonempty
      obtain ⟨G,hG,hGR⟩ := hnonempty
      have hR := neighborhood_admissible d v R ⟨G,hG,hGR⟩
      rw [graph_fiber_edge_probability d v R hR x y hx hy]
      apply hres R hR _ hu
      exact ⟨_,(graph_neighborhood_removal_equiv d v R hR ⟨G,hG,hGR⟩).property⟩)
  simpa only [Set.mem_ofPred_eq, SimpleGraph.mem_neighborFinset, fixedDegreeLaw] using h

/-- Distinct unordered graph edges admit a deletion endpoint outside the second edge.
The first loop case is exact zero, so this statement needs no loopless input assumption. -/
theorem graph_pair_upper_distinct {V : Type*} [Fintype V]
    (d : V → ℕ) (a b x y : V) (hedge : s(a,b) ≠ s(x,y)) {B : ℝ}
    (hres : ∀ v : V, (v = a ∨ v = b) → ∀ (hx : x ≠ v) (hy : y ≠ v),
      ∀ R : Finset V, graphAdmissible d v R →
      (graphFamily (residualDegree d v R)).Nonempty →
      (fixedDegreeLaw (residualDegree d v R)).real
        {H | H.Adj ⟨x,hx⟩ ⟨y,hy⟩} ≤ B) :
    (fixedDegreeLaw d).real {G | G.Adj a b ∧ G.Adj x y} ≤
      (fixedDegreeLaw d).real {G | G.Adj a b} * B := by
  by_cases hab : a = b
  · subst b
    simp
  by_cases ha : x ≠ a ∧ y ≠ a
  · exact graph_pair_upper d a b x y ha.1 ha.2
      (fun R hR hn _ => hres a (Or.inl rfl) ha.1 ha.2 R hR hn)
  · have hb : x ≠ b ∧ y ≠ b := by
      by_contra hn
      by_cases hxa : x = a <;> by_cases hya : y = a <;>
        by_cases hxb : x = b <;> by_cases hyb : y = b <;> simp_all
    have h := graph_pair_upper d b a x y hb.1 hb.2
      (fun R hR hn _ => hres b (Or.inr rfl) hb.1 hb.2 R hR hn)
    simpa only [SimpleGraph.adj_comm] using h

end MajorityDynamics.Probability.FixedDegreeEdgeConcentration
