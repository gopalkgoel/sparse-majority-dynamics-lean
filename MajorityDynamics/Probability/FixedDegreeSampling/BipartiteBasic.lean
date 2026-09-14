import MajorityDynamics.Probability.FixedDegreeSampling.Basic
import MajorityDynamics.Probability.DegreeConcentration.Basic
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace MajorityDynamics.Probability.FixedDegreeSampling
variable {L R : Type*} [Fintype L] [Fintype R]

abbrev CrossEdges (L R : Type*) := Set (L × R)
def leftNeighbors (E : CrossEdges L R) (v : L) : Finset R :=
  Finset.univ.filter fun w => (v, w) ∈ E
def rightNeighbors (E : CrossEdges L R) (w : R) : Finset L :=
  Finset.univ.filter fun v => (v, w) ∈ E
def leftDegree (E : CrossEdges L R) (v : L) : ℕ := (leftNeighbors E v).card
def rightDegree (E : CrossEdges L R) (w : R) : ℕ := (rightNeighbors E w).card
def bipartiteFamily (a : L → ℕ) (b : R → ℕ) : Set (CrossEdges L R) :=
  {E | (∀ v, leftDegree E v = a v) ∧ ∀ w, rightDegree E w = b w}
def bipartiteCount (a : L → ℕ) (b : R → ℕ) : ℕ := (bipartiteFamily a b).ncard
def bipartiteFixedDegreeLaw (a : L → ℕ) (b : R → ℕ) : Measure (CrossEdges L R) :=
  uniformOn (bipartiteFamily a b)
def bipartiteBernoulliLaw (p : unitInterval) : Measure (CrossEdges L R) :=
  setBer((Set.univ : Set (L × R)), p)
def bipartiteAdmissible (a : L → ℕ) (b : R → ℕ) (v : L) (S : Finset R) : Prop :=
  S.card = a v ∧ ∀ w ∈ S, 1 ≤ b w
def residualRightDegree (b : R → ℕ) (S : Finset R) (w : R) : ℕ :=
  b w - if w ∈ S then 1 else 0
def bipartiteNeighborhoodFiber (a : L → ℕ) (b : R → ℕ) (v : L) (S : Finset R) :=
  {E : CrossEdges L R // E ∈ bipartiteFamily a b ∧ leftNeighbors E v = S}

/-- Same cross-edge realization as A.10, for arbitrary finite vertex types. -/
def bipartiteGraph (E : CrossEdges L R) : SimpleGraph (L ⊕ R) :=
  SimpleGraph.fromEdgeSet ((fun x : L × R => s(Sum.inl x.1, Sum.inr x.2)) '' E)

theorem bipartiteGraph_fin {ℓ n : ℕ} (E : CrossEdges (Fin ℓ) (Fin n)) :
    bipartiteGraph E = DegreeConcentration.bipartiteGraph E := rfl

theorem bipartiteBernoulliLaw_fin (ℓ n : ℕ) (p : unitInterval) :
    bipartiteBernoulliLaw (L := Fin ℓ) (R := Fin n) p =
      DegreeConcentration.bipartiteLaw ℓ n p := rfl
/-- Exact cross-edge counterpart of the neighborhood probability target. -/
def BipartiteNeighborhoodProbabilityTheorem : Prop :=
  ∀ (a : L → ℕ) (b : R → ℕ) (v : L) (S : Finset R), bipartiteAdmissible a b v S →
    bipartiteFixedDegreeLaw a b {E | leftNeighbors E v = S} =
      (bipartiteCount (fun u : Remaining v => a u) (residualRightDegree b S) : ℝ≥0∞) /
        bipartiteCount a b

/-- Actual Bernoulli cross-edge conditioning, including event positivity. -/
def BipartiteConditionalLawTheorem : Prop :=
  ∀ (a : L → ℕ) (b : R → ℕ), (bipartiteFamily a b).Nonempty →
    ∀ (p : unitInterval), 0 < (p : ℝ) → (p : ℝ) < 1 →
      0 < bipartiteBernoulliLaw p (bipartiteFamily a b) ∧
      cond (bipartiteBernoulliLaw p) (bipartiteFamily a b) = bipartiteFixedDegreeLaw a b

end MajorityDynamics.Probability.FixedDegreeSampling
