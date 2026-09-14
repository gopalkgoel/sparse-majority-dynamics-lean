import MajorityDynamics.Literature.LWFormal.Bip.Statement
import MajorityDynamics.Literature.DegreeEnumeration.ComparisonLaws

noncomputable section
open MeasureTheory
open scoped Classical
namespace MajorityDynamics.Literature.LWAdapters
open MajorityDynamics.Probability.FixedDegreeSampling
open MajorityDynamics.Literature.DegreeEnumeration

theorem leftDegree_finset {l n : ℕ} (E : LW.Bip.BGraph l n) (i : Fin l) :
    leftDegree (E : Set (Fin l × Fin n)) i = LW.Bip.ldeg E i := by
  unfold leftDegree LW.Bip.ldeg
  apply Finset.card_bij (fun j _ => (i,j))
  · intro j hj
    simp only [leftNeighbors, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact Finset.mem_filter.mpr ⟨hj, rfl⟩
  · intro j _ k _ h
    exact (Prod.mk.inj h).2
  · intro e he
    obtain ⟨he, hi⟩ := Finset.mem_filter.mp he
    refine ⟨e.2, ?_, ?_⟩
    · simp [leftNeighbors, ← hi, he]
    · exact Prod.ext hi.symm rfl

theorem rightDegree_finset {l n : ℕ} (E : LW.Bip.BGraph l n) (j : Fin n) :
    rightDegree (E : Set (Fin l × Fin n)) j = LW.Bip.rdeg E j := by
  unfold rightDegree LW.Bip.rdeg
  apply Finset.card_bij (fun i _ => (i,j))
  · intro i hi
    simp only [rightNeighbors, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact Finset.mem_filter.mpr ⟨hi, rfl⟩
  · intro i _ k _ h
    exact (Prod.mk.inj h).1
  · intro e he
    obtain ⟨he, hj⟩ := Finset.mem_filter.mp he
    refine ⟨e.1, ?_, ?_⟩
    · simp [rightNeighbors, ← hj, he]
    · exact Prod.ext rfl hj.symm

theorem bip_card_transport {l n : ℕ} (A : Set (CrossEdges (Fin l) (Fin n))) :
    A.ncard = (Finset.univ.filter fun E : LW.Bip.BGraph l n => (E : Set _) ∈ A).card := by
  rw [← Set.ncard_coe_finset]
  apply Set.ncard_congr (fun E _ => E.toFinset)
  · intro E hE
    simpa using hE
  · intro E F _ _ h
    exact Set.toFinset_inj.mp h
  · intro E hE
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hE
    exact ⟨(E : Set _), hE, by simp⟩

theorem probG_eq_bipartiteDegreeLaw {l n m : ℕ} (a : Fin l → ℕ) (b : Fin n → ℕ) :
    LW.Bip.probG l n m a b = (bipartiteDegreeLaw (Fin l) (Fin n) m).real {(a,b)} := by
  rw [measureReal_def, bipartiteDegreeLaw,
    Measure.map_apply .of_discrete (measurableSet_singleton _), fixedEdgeBipartiteLaw,
    uniform_apply, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  unfold LW.Bip.probG LW.prob
  congr 1
  · rw [bip_card_transport]
    apply congrArg (fun s : Finset (LW.Bip.BGraph l n) => (s.card : ℝ))
    ext E
    simp [LW.Bip.Gm, crossEdgeFamily, leftDegree_finset, rightDegree_finset,
      funext_iff]
  · rw [bip_card_transport]
    apply congrArg (fun s : Finset (LW.Bip.BGraph l n) => (s.card : ℝ))
    ext E
    rw [Finset.mem_filter]
    simp [LW.Bip.Gm, crossEdgeFamily]

theorem probB_eq_bipartiteBinomialLaw {l n m : ℕ} (a : Fin l → ℕ) (b : Fin n → ℕ)
    (hm : m ≤ l*n) (ha : ∑ i, a i = m) (hb : ∑ j, b j = m) :
    LW.Bip.probB l n m a b = (bipartiteBinomialLaw (Fin l) (Fin n) m).real {(a,b)} := by
  rw [bipartiteBinomialLaw_atom m a b (by simpa using hm) ha hb]
  simp only [LW.Bip.probB, Fintype.card_fin]
  ring

end MajorityDynamics.Literature.LWAdapters
