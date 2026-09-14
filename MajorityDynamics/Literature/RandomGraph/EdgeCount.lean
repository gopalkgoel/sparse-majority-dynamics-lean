import MajorityDynamics.Probability.RandomGraph.Basic
import MajorityDynamics.Literature.Concentration.SetBernoulli
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Counts of prescribed random-graph edges

The graph law is Mathlib's actual Bernoulli measure on unordered non-loop
edges. Restricting that measure to any fixed edge family gives a binomial
count. These elementary law identifications support the discrepancy argument
for Krivelevich--Sudakov, *Pseudo-random graphs*, Corollary 2.3 (2006),
https://arxiv.org/abs/math/0503745v1 . This is a new Lean proof, not an import
of a previously formalized jumbledness theorem.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace MajorityDynamics.Literature.RandomGraph

open MajorityDynamics.Paper
attribute [local instance] Classical.propDecidable

instance graph_measurableSingletonClass (V : Type*) [Countable V] :
    MeasurableSingletonClass (SimpleGraph V) where
  measurableSet_singleton G := by
    have he : ({G} : Set (SimpleGraph V)) = SimpleGraph.edgeSet ⁻¹' {G.edgeSet} := by
      ext H
      simp [SimpleGraph.edgeSet_injective.eq_iff]
    rw [he]
    exact SimpleGraph.measurable_edgeSet (measurableSet_singleton _)

/-- Number of present unordered edges in a prescribed family. -/
def edgeCount {V : Type*} (s : Set (Sym2 V)) (G : SimpleGraph V) : ℕ :=
  (s ∩ G.edgeSet).ncard

lemma edgeCount_le {V : Type*} [Fintype V] (s : Set (Sym2 V)) (G : SimpleGraph V) :
    edgeCount s G ≤ s.ncard := Set.ncard_mono Set.inter_subset_left

lemma edgeCount_fromEdgeSet {V : Type*} (s E : Set (Sym2 V))
    (hs : s ⊆ Sym2.diagSetᶜ) :
    edgeCount s (SimpleGraph.fromEdgeSet E) = (s ∩ E).ncard := by
  unfold edgeCount
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  congr 1
  ext e
  simp only [Set.mem_inter_iff, Set.mem_sdiff]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hs h.1⟩⟩

/-- Exact law of an arbitrary prescribed non-loop edge count. -/
lemma map_edgeCount {V : Type*} [Fintype V] (s : Set (Sym2 V))
    (hs : s ⊆ Sym2.diagSetᶜ) (p : unitInterval) :
    (SimpleGraph.binomialRandom V p).map (edgeCount s) = binomial s.ncard p := by
  rw [SimpleGraph.binomialRandom_eq_map,
    Measure.map_map (.of_discrete) SimpleGraph.measurable_fromEdgeSet]
  have he : edgeCount s ∘ SimpleGraph.fromEdgeSet = fun E => (s ∩ E).ncard := by
    funext E
    exact edgeCount_fromEdgeSet s E hs
  rw [he]
  exact Concentration.map_inter_ncard_setBernoulli _ s p hs

lemma edgeCount_apply {V : Type*} [Fintype V] (s : Set (Sym2 V))
    (hs : s ⊆ Sym2.diagSetᶜ) (p : unitInterval) (event : Set ℕ) :
    SimpleGraph.binomialRandom V p {G | edgeCount s G ∈ event} =
      binomial s.ncard p event := by
  rw [← map_edgeCount s hs p, Measure.map_apply (.of_discrete) (.of_discrete)]
  rfl

def incidentTrials {N : ℕ} (v : Fin N) : Set (Sym2 (Fin N)) :=
  (⊤ : Graph N).incidenceSet v

lemma incidentTrials_subset {N : ℕ} (v : Fin N) :
    incidentTrials v ⊆ Sym2.diagSetᶜ :=
  ((⊤ : Graph N).incidenceSet_subset v).trans (by simp)

lemma incidentTrials_card {N : ℕ} (v : Fin N) :
    (incidentTrials v).ncard = N - 1 := by
  classical
  rw [incidentTrials, Set.ncard_eq_toFinset_card']
  change ((⊤ : Graph N).incidenceFinset v).card = N - 1
  rw [SimpleGraph.card_incidenceFinset_eq_degree]
  simp

lemma edgeCount_incidentTrials {N : ℕ} (v : Fin N) (G : Graph N) :
    edgeCount (incidentTrials v) G = G.degree v := by
  classical
  have he : incidentTrials v ∩ G.edgeSet = G.incidenceSet v := by
    ext e
    induction e using Sym2.inductionOn with
    | _ a b =>
      simp only [Set.mem_inter_iff, incidentTrials, SimpleGraph.mk'_mem_incidenceSet_iff,
        SimpleGraph.mem_edgeSet, SimpleGraph.top_adj]
      exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.ne, h.2⟩, h.1⟩⟩
  rw [edgeCount, he, Set.ncard_eq_toFinset_card', Set.toFinset_card,
    SimpleGraph.card_incidenceSet_eq_degree]

lemma map_degree {N : ℕ} (v : Fin N) (p : unitInterval) :
    (graphLaw N p).map (fun G => G.degree v) = binomial (N - 1) p := by
  have he : (fun G : Graph N => G.degree v) = edgeCount (incidentTrials v) := by
    funext G
    exact (edgeCount_incidentTrials v G).symm
  rw [he, graphLaw, map_edgeCount _ (incidentTrials_subset v), incidentTrials_card]

end MajorityDynamics.Literature.RandomGraph
