import MajorityDynamics.Literature.DegreeEnumeration.Laws

/-! Exact fixed-edge sample-space cardinalities and degree-law atoms. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace MajorityDynamics.Literature.DegreeEnumeration
open MajorityDynamics.Probability.FixedDegreeSampling
variable {V L R : Type*} [Fintype V] [Fintype L] [Fintype R]

theorem edgeFinset_from_subset (s : Finset (Sym2 V))
    (hs : s ⊆ (⊤ : SimpleGraph V).edgeFinset)
    :
    (SimpleGraph.fromEdgeSet (s : Set (Sym2 V))).edgeFinset = s := by
  apply Finset.coe_injective
  rw [SimpleGraph.coe_edgeFinset, SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  constructor
  · exact fun h => h.1
  · intro he
    exact ⟨he, (⊤ : SimpleGraph V).not_isDiag_of_mem_edgeFinset (hs he)⟩

theorem graphEdgeFamily_card (m : ℕ) :
    (graphEdgeFamily V m).ncard = ((Fintype.card V).choose 2).choose m := by
  calc
    _ = (((⊤ : SimpleGraph V).edgeFinset.powersetCard m :
        Finset (Finset (Sym2 V))) : Set (Finset (Sym2 V))).ncard := by
      apply Set.ncard_congr (fun G _ => G.edgeFinset)
      · intro G hG
        exact Finset.mem_powersetCard.mpr ⟨SimpleGraph.edgeFinset_mono le_top, hG⟩
      · intro G H _ _ h
        exact SimpleGraph.edgeFinset_inj.mp h
      · intro s hs
        obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hs
        let G := SimpleGraph.fromEdgeSet (s : Set (Sym2 V))
        have he : @SimpleGraph.edgeFinset V G G.fintypeEdgeSet = s := by
          apply Finset.coe_injective
          rw [SimpleGraph.coe_edgeFinset]
          change (SimpleGraph.fromEdgeSet (s : Set (Sym2 V))).edgeSet = _
          rw [SimpleGraph.edgeSet_fromEdgeSet]
          ext e
          exact ⟨fun h => h.1, fun h =>
            ⟨h, (⊤ : SimpleGraph V).not_isDiag_of_mem_edgeFinset (hsub h)⟩⟩
        have he' : (fun H : SimpleGraph V => H.edgeFinset) G = s := by
          ext e
          simpa only [SimpleGraph.mem_edgeFinset] using Finset.ext_iff.mp he e
        refine ⟨G, ?_, he'⟩
        exact (congrArg Finset.card he').trans hcard
    _ = _ := by
      rw [Set.ncard_coe_finset, Finset.card_powersetCard,
        SimpleGraph.card_edgeFinset_top_eq_card_choose_two]

theorem crossEdgeFamily_card (m : ℕ) :
    (crossEdgeFamily L R m).ncard = (Fintype.card L * Fintype.card R).choose m := by
  calc
    _ = ((Finset.univ.powersetCard m : Finset (Finset (L × R))) :
        Set (Finset (L × R))).ncard := by
      apply Set.ncard_congr (fun E _ => E.toFinset)
      · intro E hE
        exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,
          by simpa [crossEdgeFamily, Set.ncard_eq_toFinset_card'] using hE⟩
      · intro E F _ _ h
        exact Set.toFinset_inj.mp h
      · intro s hs
        obtain ⟨_, hcard⟩ := Finset.mem_powersetCard.mp hs
        refine ⟨(s : Set (L × R)), ?_, by simp⟩
        simpa [crossEdgeFamily] using hcard
    _ = _ := by simp

theorem fixedEdgeGraphLaw_normalized (m : ℕ) (hm : m ≤ (Fintype.card V).choose 2) :
    IsProbabilityMeasure (fixedEdgeGraphLaw V m) := by
  apply isProbabilityMeasure_uniformOn (Set.toFinite _)
  apply (Set.ncard_pos (Set.toFinite _)).mp
  rw [graphEdgeFamily_card]
  exact Nat.choose_pos hm

theorem fixedEdgeBipartiteLaw_normalized (m : ℕ)
    (hm : m ≤ Fintype.card L * Fintype.card R) :
    IsProbabilityMeasure (fixedEdgeBipartiteLaw L R m) := by
  apply isProbabilityMeasure_uniformOn (Set.toFinite _)
  apply (Set.ncard_pos (Set.toFinite _)).mp
  rw [crossEdgeFamily_card]
  exact Nat.choose_pos hm

theorem graphDegreeLaw_atom (d : V → ℕ) (m : ℕ) (hs : ∑ i, d i = 2 * m) :
    graphDegreeLaw V m {d} =
      (graphCount d : ℝ≥0∞) / (((Fintype.card V).choose 2).choose m : ℕ) := by
  rw [graphDegreeLaw_atom_count d m hs, graphEdgeFamily_card]

theorem sum_leftDegree (E : CrossEdges L R) : ∑ i, leftDegree E i = E.ncard := by
  have h := Finset.card_eq_sum_card_fiberwise (s := E.toFinset)
    (t := Finset.univ) (f := Prod.fst) (fun _ _ => Finset.mem_univ _)
  rw [Set.ncard_eq_toFinset_card', h]
  apply Finset.sum_congr rfl
  intro i _
  unfold leftDegree leftNeighbors
  apply Finset.card_bij (fun j _ => (i, j))
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp [hj]
  · intro j _ k _ h
    exact Prod.mk.inj h |>.2
  · intro e he
    simp only [Finset.mem_filter, Set.mem_toFinset] at he
    refine ⟨e.2, ?_, ?_⟩
    · simp [← he.2, he.1]
    · exact Prod.ext he.2.symm rfl

theorem bipartiteFamily_subset_edgeFamily (a : L → ℕ) (b : R → ℕ) (m : ℕ)
    (hs : ∑ i, a i = m) : bipartiteFamily a b ⊆ crossEdgeFamily L R m := by
  intro E hE
  change E.ncard = m
  rw [← sum_leftDegree]
  simpa only [hE.1] using hs

theorem bipartiteDegreeLaw_atom (a : L → ℕ) (b : R → ℕ) (m : ℕ)
    (hs : ∑ i, a i = m) :
    bipartiteDegreeLaw L R m {(a, b)} =
      (bipartiteCount a b : ℝ≥0∞) / ((Fintype.card L * Fintype.card R).choose m : ℕ) := by
  rw [bipartiteDegreeLaw, Measure.map_apply .of_discrete (measurableSet_singleton _),
    fixedEdgeBipartiteLaw, uniform_apply, crossEdgeFamily_card]
  congr 2
  have he : (fun E : CrossEdges L R => (leftDegree E, rightDegree E)) ⁻¹' {(a, b)} =
      bipartiteFamily a b := by
    ext E
    simp [bipartiteFamily, funext_iff]
  rw [he, Set.inter_eq_right.mpr (bipartiteFamily_subset_edgeFamily a b m hs)]
  rfl

end MajorityDynamics.Literature.DegreeEnumeration
