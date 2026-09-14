import MajorityDynamics.Probability.FixedDegreeSampling.GraphRemoval
import MajorityDynamics.Probability.FixedDegreeSampling.BipartiteRemoval
import MajorityDynamics.Probability.FixedDegreeSampling.FiniteLaw
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace MajorityDynamics.Probability.FixedDegreeSampling
variable {V L R : Type*} [Fintype V] [Fintype L] [Fintype R]

theorem fixedDegreeLaw_normalized (d : V → ℕ) (h : (graphFamily d).Nonempty) :
    IsProbabilityMeasure (fixedDegreeLaw d) :=
  isProbabilityMeasure_uniformOn (Set.toFinite _) h

theorem fixedDegreeLaw_singleton (d : V → ℕ) (G : SimpleGraph V) :
    fixedDegreeLaw d {G} = if G ∈ graphFamily d then (graphCount d : ℝ≥0∞)⁻¹ else 0 :=
  uniform_singleton _ _

theorem fixedDegreeLaw_integral (d : V → ℕ) (f : SimpleGraph V → ℝ) :
    ∫ G, f G ∂fixedDegreeLaw d =
      (∑ G ∈ (graphFamily d).toFinset, f G) / (graphCount d : ℝ) := uniform_integral _ _

theorem graph_neighborhood_probability (d : V → ℕ) (v : V) (S : Finset V)
    (h : graphAdmissible d v S) :
    fixedDegreeLaw d {G | G.neighborFinset v = S} =
      (graphCount (residualDegree d v S) : ℝ≥0∞) / graphCount d := by
  rw [fixedDegreeLaw, uniform_apply]
  congr 2
  exact Nat.card_congr (graph_neighborhood_removal_equiv d v S h)

theorem graph_invalid_neighborhood (d : V → ℕ) (v : V) (S : Finset V)
    (h : ¬ graphAdmissible d v S) :
    fixedDegreeLaw d {G | G.neighborFinset v = S} = 0 := by
  apply (uniformOn_eq_zero_iff (Set.toFinite _)).mpr
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro G hG
  exact h (neighborhood_admissible d v S ⟨G, hG⟩)

theorem bipartiteFixedDegreeLaw_normalized (a : L → ℕ) (b : R → ℕ)
    (h : (bipartiteFamily a b).Nonempty) :
    IsProbabilityMeasure (bipartiteFixedDegreeLaw a b) :=
  isProbabilityMeasure_uniformOn (Set.toFinite _) h

theorem bipartiteFixedDegreeLaw_singleton (a : L → ℕ) (b : R → ℕ) (E : CrossEdges L R) :
    bipartiteFixedDegreeLaw a b {E} =
      if E ∈ bipartiteFamily a b then (bipartiteCount a b : ℝ≥0∞)⁻¹ else 0 :=
  uniform_singleton _ _

theorem bipartiteFixedDegreeLaw_integral (a : L → ℕ) (b : R → ℕ) (f : CrossEdges L R → ℝ) :
    ∫ E, f E ∂bipartiteFixedDegreeLaw a b =
      (∑ E ∈ (bipartiteFamily a b).toFinset, f E) / (bipartiteCount a b : ℝ) :=
  uniform_integral _ _

theorem bipartite_neighborhood_probability (a : L → ℕ) (b : R → ℕ) (v : L)
    (S : Finset R) (h : bipartiteAdmissible a b v S) :
    bipartiteFixedDegreeLaw a b {E | leftNeighbors E v = S} =
      (bipartiteCount (fun u : Remaining v => a u) (residualRightDegree b S) : ℝ≥0∞) /
        bipartiteCount a b := by
  rw [bipartiteFixedDegreeLaw, uniform_apply]
  congr 2
  exact Nat.card_congr (bipartite_neighborhood_removal_equiv a b v S h)

theorem bipartite_invalid_neighborhood (a : L → ℕ) (b : R → ℕ) (v : L)
    (S : Finset R) (h : ¬ bipartiteAdmissible a b v S) :
    bipartiteFixedDegreeLaw a b {E | leftNeighbors E v = S} = 0 := by
  apply (uniformOn_eq_zero_iff (Set.toFinite _)).mpr
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro E hE
  exact h (bipartite_neighborhood_admissible a b v S ⟨E, hE⟩)
end MajorityDynamics.Probability.FixedDegreeSampling
