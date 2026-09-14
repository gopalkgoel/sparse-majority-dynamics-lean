import MajorityDynamics.Literature.DegreeEnumeration.Graph
import MajorityDynamics.Literature.DegreeEnumeration.Bipartite

/-! Exact model/atom checks. These do not assert any application of enumeration
to the sparse reference-density window of Lemma C.4. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
namespace MajorityDynamics.Literature.DegreeEnumeration
open MajorityDynamics.Probability.FixedDegreeSampling

example (n m : ℕ) (d : Fin n → ℕ) (hd : ∑ i, d i = 2 * m) :
    ((uniformOn {G : SimpleGraph (Fin n) | G.edgeFinset.card = m}).map
      (fun G i => G.degree i)) {d} =
      (({G : SimpleGraph (Fin n) | ∀ i, G.degree i = d i}).ncard : ℝ≥0∞) /
        ((n.choose 2).choose m : ℕ) := by
  simpa [graphDegreeLaw, fixedEdgeGraphLaw, graphEdgeFamily, graphCount, graphFamily]
    using graphDegreeLaw_atom d m hd

example (n m : ℕ) (d : Fin n → ℕ)
    (hm : 2 * m ≤ n * (n - 1)) (hd : ∑ i, d i = 2 * m) :
    (cond (Measure.pi (fun _ : Fin n => binomial (n - 1) halfProbability))
      {d | ∑ i, d i = 2 * m}).real {d} =
      (∏ i, ((n - 1).choose (d i) : ℝ)) / ((n * (n - 1)).choose (2 * m) : ℝ) := by
  simpa [graphBinomialLaw, independentBinomials] using graphBinomialLaw_atom m d
    (by simpa using hm) hd

example (ell n m : ℕ) (a : Fin ell → ℕ) (b : Fin n → ℕ) (ha : ∑ i, a i = m) :
    ((uniformOn {E : Set (Fin ell × Fin n) | E.ncard = m}).map
      (fun E => (leftDegree E, rightDegree E))) {(a, b)} =
      (({E : Set (Fin ell × Fin n) |
        (∀ i, leftDegree E i = a i) ∧ ∀ j, rightDegree E j = b j}).ncard : ℝ≥0∞) /
          ((ell * n).choose m : ℕ) := by
  simpa [bipartiteDegreeLaw, fixedEdgeBipartiteLaw, crossEdgeFamily,
    bipartiteCount, bipartiteFamily] using bipartiteDegreeLaw_atom a b m ha

example (ell n m : ℕ) (a : Fin ell → ℕ) (b : Fin n → ℕ)
    (hm : m ≤ ell * n) (ha : ∑ i, a i = m) (hb : ∑ j, b j = m) :
    (cond ((Measure.pi (fun _ : Fin ell => binomial n halfProbability)).prod
      (Measure.pi (fun _ : Fin n => binomial ell halfProbability)))
      {d | (∑ i, d.1 i) = m ∧ (∑ j, d.2 j) = m}).real {(a, b)} =
      (∏ i, (n.choose (a i) : ℝ)) * (∏ j, (ell.choose (b j) : ℝ)) /
        ((ell * n).choose m : ℝ) ^ 2 := by
  simpa [bipartiteBinomialLaw, bipartiteIndependentLaw, independentBinomials]
    using bipartiteBinomialLaw_atom m a b (by simpa using hm) ha hb

/-- No correction or error has been absorbed into either reference probability law. -/
example (n m : ℕ) (d : Fin n → ℕ) :
    graphCorrection m d = Real.exp (1 / 4 -
      ((∑ i, ((d i : ℝ) - 2 * (m : ℝ) / n) ^ 2) / ((n : ℝ) - 1) ^ 2) ^ 2 /
        (4 * (2 * (m : ℝ) / n / ((n : ℝ) - 1)) ^ 2 *
          (1 - 2 * (m : ℝ) / n / ((n : ℝ) - 1)) ^ 2)) := rfl

example (ell n m : ℕ) (a : Fin ell → ℕ) (b : Fin n → ℕ) :
    bipartiteCorrection m a b = Real.exp (-1 / 2 *
      (1 - ((∑ i, ((a i : ℝ) - (m : ℝ) / ell) ^ 2) / ell) /
        ((m : ℝ) / ell * (1 - (m : ℝ) / ((ell : ℝ) * n)))) *
      (1 - ((∑ j, ((b j : ℝ) - (m : ℝ) / n) ^ 2) / n) /
        ((m : ℝ) / n * (1 - (m : ℝ) / ((ell : ℝ) * n))))) := rfl

end MajorityDynamics.Literature.DegreeEnumeration

/- Exact transitive trust boundaries: finite law bridges are foundational-only. -/
/--
info: 'MajorityDynamics.Literature.DegreeEnumeration.graphDegreeLaw_atom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Literature.DegreeEnumeration.graphDegreeLaw_atom

/--
info: 'MajorityDynamics.Literature.DegreeEnumeration.graphBinomialLaw_atom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Literature.DegreeEnumeration.graphBinomialLaw_atom

/--
info: 'MajorityDynamics.Literature.DegreeEnumeration.bipartiteDegreeLaw_atom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Literature.DegreeEnumeration.bipartiteDegreeLaw_atom

/--
info: 'MajorityDynamics.Literature.DegreeEnumeration.bipartiteBinomialLaw_atom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MajorityDynamics.Literature.DegreeEnumeration.bipartiteBinomialLaw_atom

/--
info: 'MajorityDynamics.Literature.DegreeEnumeration.liebenau_wormald_graph' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Literature.DegreeEnumeration.liebenau_wormald_graph

/--
info: 'MajorityDynamics.Literature.DegreeEnumeration.liebenau_wormald_bipartite' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Literature.DegreeEnumeration.liebenau_wormald_bipartite
