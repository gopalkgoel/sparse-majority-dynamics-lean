import MajorityDynamics.Paper.MajorityStep
import MajorityDynamics.Literature.Chernoff
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! # The degree event in Mathlib's Bernoulli random graph -/

noncomputable section
open Set MeasureTheory ProbabilityTheory

namespace MajorityDynamics.Paper

attribute [local instance] Classical.propDecidable

instance graph_measurableSingleton (N : ℕ) : MeasurableSingletonClass (Graph N) where
  measurableSet_singleton G := by
    have he : ({G} : Set (Graph N)) = SimpleGraph.edgeSet ⁻¹' {G.edgeSet} := by
      ext H
      simp [SimpleGraph.edgeSet_injective.eq_iff]
    rw [he]
    exact SimpleGraph.measurable_edgeSet (measurableSet_singleton _)

def incidentTrials {N : ℕ} (v : Fin N) : Set (Sym2 (Fin N)) :=
  (⊤ : Graph N).incidenceSet v

theorem incidentTrials_subset {N : ℕ} (v : Fin N) :
    incidentTrials v ⊆ Sym2.diagSetᶜ := by
  exact ((⊤ : Graph N).incidenceSet_subset v).trans (by simp)

theorem incidentTrials_card {N : ℕ} (v : Fin N) :
    (incidentTrials v).ncard = N - 1 := by
  classical
  rw [incidentTrials, Set.ncard_eq_toFinset_card']
  change ((⊤ : Graph N).incidenceFinset v).card = N - 1
  rw [SimpleGraph.card_incidenceFinset_eq_degree]
  simp

theorem degreeInto_univ_eq_degree {N : ℕ} (G : Graph N) (v : Fin N) :
    orderedEdgeCount G {v} Finset.univ = G.degree v := by
  classical
  rw [orderedEdgeCount_singleton, degreeInto]
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext w
  simp

theorem fromEdgeSet_degree_count {N : ℕ} (v : Fin N) (selected : Set (Sym2 (Fin N))) :
    orderedEdgeCount (SimpleGraph.fromEdgeSet selected) {v} Finset.univ =
      (incidentTrials v ∩ selected).ncard := by
  classical
  have he : (SimpleGraph.fromEdgeSet selected).incidenceSet v = incidentTrials v ∩ selected := by
    ext e
    induction e using Sym2.inductionOn with
    | _ a b => simp [incidentTrials, SimpleGraph.mk'_mem_incidenceSet_iff,
        SimpleGraph.fromEdgeSet_adj, and_assoc, and_left_comm, and_comm]
  rw [← he, Set.ncard_eq_toFinset_card', Set.toFinset_card,
    SimpleGraph.card_incidenceSet_eq_degree, degreeInto_univ_eq_degree]
  unfold SimpleGraph.degree
  congr 1
  ext w
  simp

/-- Applying the generic Bernoulli inequality to the `N-1` incident edges. -/
theorem degree_lower_tail_of_chernoff (hChernoff : Literature.BernoulliLowerTail)
    (N : ℕ) (hN : 20 ≤ N) (p : unitInterval) (hp : 0 < (p : ℝ)) (v : Fin N) :
    graphLaw N p {G | (orderedEdgeCount G {v} Finset.univ : ℝ) <
      (9 / 10 : ℝ) * (p : ℝ) * N} ≤
      ENNReal.ofReal (Real.exp (-((p : ℝ) * N) / 1000)) := by
  let μ : ℝ := (N - 1 : ℕ) * (p : ℝ)
  have hNr : (20 : ℝ) ≤ N := by exact_mod_cast hN
  have hμeq : μ = ((N : ℝ) - 1) * (p : ℝ) := by
    simp only [μ, Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
  have hμ : 0 < μ := by rw [hμeq]; exact mul_pos (by linarith) hp
  have hlow : (19 / 20 : ℝ) * ((p : ℝ) * N) ≤ μ := by
    rw [hμeq]
    nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hNr)]
  have hthreshold : (9 / 10 : ℝ) * (p : ℝ) * N ≤ μ - μ / 20 := by
    nlinarith
  have htail := hChernoff (Sym2 (Fin N)) Sym2.diagSetᶜ (incidentTrials v) p
    (incidentTrials_subset v)
  rw [incidentTrials_card] at htail
  have htail' := htail hμ (μ / 20) (by positivity)
  have hexp : -(μ / 20) ^ 2 / (2 * μ) = -μ / 800 := by
    field_simp
    ring
  rw [hexp] at htail'
  rw [graphLaw, SimpleGraph.binomialRandom_eq_map,
    Measure.map_apply SimpleGraph.measurable_fromEdgeSet (Set.toFinite _).measurableSet]
  refine (measure_mono (fun selected hselected => ?_)).trans
    (htail'.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)))
  · change (orderedEdgeCount (SimpleGraph.fromEdgeSet selected) {v} Finset.univ : ℝ) < _
      at hselected
    change ((incidentTrials v ∩ selected).ncard : ℝ) ≤ μ - μ / 20
    rw [← fromEdgeSet_degree_count]
    exact hselected.le.trans hthreshold
  · nlinarith

/-- The paper's union bound over vertices, with an explicit uniform error. -/
theorem minimumDegree_failure_bound_of_chernoff
    (hChernoff : Literature.BernoulliLowerTail) (N : ℕ) (hN : 20 ≤ N)
    (p : unitInterval) (hp : 0 < (p : ℝ)) :
    graphLaw N p {G | minimumDegree G p}ᶜ ≤
      ENNReal.ofReal ((N : ℝ) * Real.exp (-((p : ℝ) * N) / 1000)) := by
  have he : {G : Graph N | minimumDegree G p}ᶜ =
      ⋃ v : Fin N, {G | (orderedEdgeCount G {v} Finset.univ : ℝ) <
        (9 / 10 : ℝ) * (p : ℝ) * N} := by
    ext G
    simp [minimumDegree, not_forall]
  rw [he]
  refine (measure_iUnion_le _).trans ?_
  calc
    _ ≤ ∑' _ : Fin N, ENNReal.ofReal (Real.exp (-((p : ℝ) * N) / 1000)) :=
      ENNReal.tsum_le_tsum fun v => degree_lower_tail_of_chernoff hChernoff N hN p hp v
    _ = _ := by simp [tsum_fintype, ENNReal.ofReal_mul]

end MajorityDynamics.Paper
