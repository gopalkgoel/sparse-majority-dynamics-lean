import MajorityDynamics.Literature.LWFormal.Statements
import MajorityDynamics.Literature.DegreeEnumeration.ComparisonLaws

noncomputable section
open MeasureTheory
open scoped Classical
namespace MajorityDynamics.Literature.LWAdapters
open MajorityDynamics.Probability.FixedDegreeSampling
open MajorityDynamics.Literature.DegreeEnumeration

def asGraph {n : ℕ} (E : LW.Graph n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))

theorem edgeFinset_simple {n : ℕ} (G : SimpleGraph (Fin n)) : LW.IsSimple G.edgeFinset := by
  intro e he
  exact G.not_isDiag_of_mem_edgeFinset he

theorem simple_subset_top {n : ℕ} {E : LW.Graph n} (hE : LW.IsSimple E) :
    E ⊆ (⊤ : SimpleGraph (Fin n)).edgeFinset := by
  intro e he
  simpa using hE e he

theorem degree_edgeFinset {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    LW.deg G.edgeFinset v = G.degree v := by
  rw [LW.deg_eq_card_filter (edgeFinset_simple G)]
  congr 1
  ext w
  simp [SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm]

theorem fromEdgeSet_finset {n : ℕ} {E : LW.Graph n} (hs : LW.IsSimple E) :
    (asGraph E).edgeFinset = E := by
  apply Finset.coe_injective
  rw [SimpleGraph.coe_edgeFinset]
  unfold asGraph
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  exact ⟨fun h => h.1, fun h => ⟨h, hs e h⟩⟩

theorem graph_card_transport {n : ℕ} (A : Set (SimpleGraph (Fin n))) :
    A.ncard =
      (Finset.univ.filter fun E : LW.Graph n =>
        LW.IsSimple E ∧ asGraph E ∈ A).card := by
  rw [← Set.ncard_coe_finset]
  apply Set.ncard_congr (fun G _ => G.edgeFinset)
  · intro G hG
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨edgeFinset_simple G, ?_⟩
    simpa [asGraph] using hG
  · intro G H _ _ h
    exact SimpleGraph.edgeFinset_inj.mp h
  · intro E hE
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hE
    exact ⟨asGraph E, hE.2,
      by
        ext e
        simpa only [SimpleGraph.mem_edgeFinset] using Finset.ext_iff.mp (fromEdgeSet_finset hE.1) e⟩

theorem probGnm_eq_degreeLaw {n m : ℕ} (d : Fin n → ℕ) :
    LW.probGnm n m d = (graphDegreeLaw (Fin n) m).real {d} := by
  rw [measureReal_def, graphDegreeLaw,
    Measure.map_apply .of_discrete (measurableSet_singleton _), fixedEdgeGraphLaw,
    uniform_apply, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  unfold LW.probGnm LW.prob
  congr 1
  · rw [graph_card_transport]
    apply congrArg (fun s : Finset (LW.Graph n) => (s.card : ℝ))
    ext E
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_singleton_iff, graphEdgeFamily, Set.mem_ofPred_eq,
      LW.Gnm, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hsub, hcard⟩, hdeg⟩
      have hs : LW.IsSimple E := by
        intro e he
        exact (Finset.mem_filter.mp (hsub he)).2
      have he := fromEdgeSet_finset hs
      refine ⟨hs, ?_, ?_⟩
      · simpa only [he] using hcard
      · funext v
        have := degree_edgeFinset (asGraph E) v
        rw [he] at this
        exact this.symm.trans (congrFun hdeg v)
    · rintro ⟨hs, hcard, hdeg⟩
      have he := fromEdgeSet_finset hs
      refine ⟨⟨?_, by simpa only [he] using hcard⟩, ?_⟩
      · intro e heE
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs e heE⟩
      · funext v
        have := degree_edgeFinset (asGraph E) v
        rw [he] at this
        exact this.trans (congrFun hdeg v)
  · rw [graph_card_transport]
    apply congrArg (fun s : Finset (LW.Graph n) => (s.card : ℝ))
    ext E
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, LW.Gnm, Finset.mem_powersetCard]
    change (E ⊆ LW.allEdges n ∧ E.card = m) ↔
      (LW.IsSimple E ∧ (asGraph E).edgeFinset.card = m)
    constructor
    · rintro ⟨hsub, hcard⟩
      have hs : LW.IsSimple E := by
        intro e he
        exact (Finset.mem_filter.mp (hsub he)).2
      exact ⟨hs, by simpa only [fromEdgeSet_finset hs] using hcard⟩
    · rintro ⟨hs, hcard⟩
      refine ⟨?_, ?_⟩
      · intro e he
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs e he⟩
      · simpa only [fromEdgeSet_finset hs] using hcard

theorem probBinom_eq_binomialLaw {n m : ℕ} (d : Fin n → ℕ)
    (hm : 2*m ≤ n*(n-1)) (hd : ∑ i, d i = 2*m) :
    LW.probBinom n m d = (graphBinomialLaw (Fin n) m).real {d} := by
  rw [graphBinomialLaw_atom m d (by simpa using hm) hd]
  simp [LW.probBinom, div_eq_mul_inv, mul_comm]

end MajorityDynamics.Literature.LWAdapters
