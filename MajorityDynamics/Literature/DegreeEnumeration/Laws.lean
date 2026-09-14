import MajorityDynamics.Probability.FixedDegreeSampling.Laws
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Probability.Distributions.Binomial
import Mathlib.MeasureTheory.Constructions.Pi

/-! Concrete fixed-edge degree laws and independently sampled binomial comparison
laws from `def:graph_deg_seq` and `def:bigraph_deg_seq`. No enumeration assumptions
are used in this file. Empty conditioning events use the standard zero measure. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace MajorityDynamics.Literature.DegreeEnumeration
open MajorityDynamics.Probability.FixedDegreeSampling
variable {V L R : Type*} [Fintype V] [Fintype L] [Fintype R]

def graphEdgeFamily (V : Type*) [Fintype V] (m : ℕ) : Set (SimpleGraph V) :=
  {G | G.edgeFinset.card = m}

def fixedEdgeGraphLaw (V : Type*) [Fintype V] (m : ℕ) : Measure (SimpleGraph V) :=
  uniformOn (graphEdgeFamily V m)

def graphDegreeLaw (V : Type*) [Fintype V] (m : ℕ) : Measure (V → ℕ) :=
  (fixedEdgeGraphLaw V m).map (fun G v => G.degree v)

def crossEdgeFamily (L R : Type*) [Fintype L] [Fintype R] (m : ℕ) :
    Set (CrossEdges L R) := {E | E.ncard = m}

def fixedEdgeBipartiteLaw (L R : Type*) [Fintype L] [Fintype R] (m : ℕ) :
    Measure (CrossEdges L R) := uniformOn (crossEdgeFamily L R m)

def bipartiteDegreeLaw (L R : Type*) [Fintype L] [Fintype R] (m : ℕ) :
    Measure ((L → ℕ) × (R → ℕ)) :=
  (fixedEdgeBipartiteLaw L R m).map (fun E => (leftDegree E, rightDegree E))

def halfProbability : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

def independentBinomials (V : Type*) [Fintype V] (k : ℕ) : Measure (V → ℕ) :=
  Measure.pi (fun _ => binomial k halfProbability)

instance (V : Type*) [Fintype V] (k : ℕ) :
    IsProbabilityMeasure (independentBinomials V k) := by
  unfold independentBinomials
  infer_instance

def graphBinomialLaw (V : Type*) [Fintype V] (m : ℕ) : Measure (V → ℕ) :=
  cond (independentBinomials V (Fintype.card V - 1)) {d | ∑ i, d i = 2 * m}

def bipartiteIndependentLaw (L R : Type*) [Fintype L] [Fintype R] :
    Measure ((L → ℕ) × (R → ℕ)) :=
  (independentBinomials L (Fintype.card R)).prod
    (independentBinomials R (Fintype.card L))

def bipartiteBinomialLaw (L R : Type*) [Fintype L] [Fintype R] (m : ℕ) :
    Measure ((L → ℕ) × (R → ℕ)) :=
  cond (bipartiteIndependentLaw L R) {d | (∑ i, d.1 i) = m ∧ (∑ j, d.2 j) = m}

theorem graphFamily_subset_edgeFamily (d : V → ℕ) (m : ℕ)
    (hs : ∑ i, d i = 2 * m) : graphFamily d ⊆ graphEdgeFamily V m := by
  intro G hG
  have h := G.sum_degrees_eq_twice_card_edges
  simp only [graphFamily, Set.mem_ofPred_eq] at hG
  simp_rw [hG] at h
  dsimp [graphEdgeFamily]
  omega

theorem graphDegreeLaw_atom_count (d : V → ℕ) (m : ℕ)
    (hs : ∑ i, d i = 2 * m) :
    graphDegreeLaw V m {d} =
      (graphCount d : ℝ≥0∞) / (graphEdgeFamily V m).ncard := by
  rw [graphDegreeLaw, Measure.map_apply .of_discrete (measurableSet_singleton _),
    fixedEdgeGraphLaw, uniform_apply]
  congr 2
  have he : (fun G : SimpleGraph V => fun v => G.degree v) ⁻¹' {d} = graphFamily d := by
    ext G
    simp [graphFamily, funext_iff]
  rw [he, Set.inter_eq_right.mpr (graphFamily_subset_edgeFamily d m hs)]
  rfl

end MajorityDynamics.Literature.DegreeEnumeration
