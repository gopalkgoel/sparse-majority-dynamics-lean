import MajorityDynamics.Probability.NeighborhoodBulk.Relabel
import MajorityDynamics.Literature.DegreeEnumeration.Consequences

noncomputable section
open MeasureTheory
open scoped Classical BigOperators
namespace MajorityDynamics.GraphProcess.EnumerationComparison
open MajorityDynamics.Literature.DegreeEnumeration
open MajorityDynamics.Probability.NeighborhoodBulk
variable {V W L L' R R' : Type*}
  [Fintype V] [Fintype W] [Fintype L] [Fintype L'] [Fintype R] [Fintype R']

theorem graphDegreeLaw_real_relabel (e : V ≃ W) (d : V → ℕ) (m : ℕ)
    (hs : ∑ i, d i = 2*m) :
    (graphDegreeLaw V m).real {d} =
      (graphDegreeLaw W m).real {fun w => d (e.symm w)} := by
  have hs' : ∑ w, d (e.symm w) = 2*m := by rw [e.symm.sum_comp]; exact hs
  rw [graphDegreeLaw_real_atom d m hs, graphDegreeLaw_real_atom _ m hs',
    graphCount_relabel, Fintype.card_congr e]

theorem graphBinomialLaw_real_relabel (e : V ≃ W) (d : V → ℕ) (m : ℕ)
    (hm : 2*m ≤ Fintype.card V * (Fintype.card V-1))
    (hs : ∑ i, d i = 2*m) :
    (graphBinomialLaw V m).real {d} =
      (graphBinomialLaw W m).real {fun w => d (e.symm w)} := by
  have hs' : ∑ w, d (e.symm w) = 2*m := by rw [e.symm.sum_comp]; exact hs
  have hm' : 2*m ≤ Fintype.card W * (Fintype.card W-1) := by
    simpa only [Fintype.card_congr e] using hm
  rw [graphBinomialLaw_atom m d hm hs, graphBinomialLaw_atom m _ hm' hs',
    Fintype.card_congr e,
    e.symm.prod_comp (fun i => ((Fintype.card W - 1).choose (d i) : ℝ))]

theorem bipartiteDegreeLaw_real_relabel (e : L ≃ L') (f : R ≃ R')
    (a : L → ℕ) (b : R → ℕ) (m : ℕ) (hs : ∑ i, a i = m) :
    (bipartiteDegreeLaw L R m).real {(a,b)} =
      (bipartiteDegreeLaw L' R' m).real
        {(fun v => a (e.symm v), fun w => b (f.symm w))} := by
  have hs' : ∑ v, a (e.symm v) = m := by rw [e.symm.sum_comp]; exact hs
  rw [bipartiteDegreeLaw_real_atom a b m hs, bipartiteDegreeLaw_real_atom _ _ m hs',
    bipartiteCount_relabel, Fintype.card_congr e, Fintype.card_congr f]

theorem bipartiteBinomialLaw_real_relabel (e : L ≃ L') (f : R ≃ R')
    (a : L → ℕ) (b : R → ℕ) (m : ℕ)
    (hm : m ≤ Fintype.card L * Fintype.card R)
    (ha : ∑ i, a i = m) (hb : ∑ j, b j = m) :
    (bipartiteBinomialLaw L R m).real {(a,b)} =
      (bipartiteBinomialLaw L' R' m).real
        {(fun v => a (e.symm v), fun w => b (f.symm w))} := by
  have ha' : ∑ v, a (e.symm v) = m := by rw [e.symm.sum_comp]; exact ha
  have hb' : ∑ w, b (f.symm w) = m := by rw [f.symm.sum_comp]; exact hb
  have hm' : m ≤ Fintype.card L' * Fintype.card R' := by
    simpa only [Fintype.card_congr e, Fintype.card_congr f] using hm
  rw [bipartiteBinomialLaw_atom m a b hm ha hb,
    bipartiteBinomialLaw_atom m _ _ hm' ha' hb',
    Fintype.card_congr e, Fintype.card_congr f,
    e.symm.prod_comp (fun i => ((Fintype.card R').choose (a i) : ℝ)),
    f.symm.prod_comp (fun j => ((Fintype.card L').choose (b j) : ℝ))]

end MajorityDynamics.GraphProcess.EnumerationComparison
