import MajorityDynamics.Literature.LWAdapters.BipartiteEnumeration
import MajorityDynamics.Literature.LWAdapters.FixedDegreeLaws
import MajorityDynamics.Literature.LWAdapters.Reindex
import MajorityDynamics.Literature.Goals.BipartiteEdgeProbability.Statement

noncomputable section
open Filter MeasureTheory
open scoped Classical Topology
namespace MajorityDynamics.Literature.LWAdapters
open MajorityDynamics.Probability.FixedDegreeSampling
open EdgeProbabilities
universe u v

theorem bipartite_var_eq {n m : ℕ} (a : Fin n → ℕ) (ha : ∑ i, a i = m) :
    LW.Bip.var a = degreeVariance a ((m:ℝ)/n) := by
  simp [LW.Bip.var, bipartite_mean_eq a ha, degreeVariance]

theorem bipartite_edge_probability : BipartiteEdgeProbabilityTheorem.{u,v} := by
  obtain ⟨μ₀,hμ₀,hsource⟩ := LW.Bip.theorem_1_5
  refine ⟨μ₀,hμ₀,?_⟩
  intro α hαlo hαhi l n m hn _hl hdensity hpowers hlogs
  obtain ⟨ω,hω,hgrowth⟩ := bipartite_slow_growth l n m hn α hpowers hlogs
  obtain ⟨C,N,hbound⟩ := hsource α hαlo hαhi ω hω
  refine ⟨max C 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  filter_upwards [hdensity,hgrowth,hn.eventually_ge_atTop N] with k hk hg hNk
  intro L R _ _ a b hd i j
  let e : L ≃ Fin (l k) := Fintype.equivFinOfCardEq hd.card_left
  let f : R ≃ Fin (n k) := Fintype.equivFinOfCardEq hd.card_right
  let a' := a ∘ e.symm
  let b' := b ∘ f.symm
  have ha : ∑ i, a' i = m k := (Equiv.sum_comp e.symm a).trans hd.total_left
  have hb : ∑ j, b' j = m k := (Equiv.sum_comp f.symm b).trans hd.total_right
  have hIn : LW.Bip.InD α (l k) (n k) (m k) a' b' :=
    ⟨ha,hb,fun i => hd.spread_left (e.symm i),fun j => hd.spread_right (f.symm j)⟩
  obtain ⟨θ,hθ,hEq⟩ := hbound (n k) hNk (l k) (m k)
    (by simpa only [bipartiteDensity,mul_comm] using hk) hg.1 hg.2 a' b' hIn (e i) (f j)
  have hr : (bipartiteFamily a' b').Nonempty := by
    obtain ⟨E,hE⟩ := hd.realizable
    exact ⟨crossEquiv e f E,(bipartite_family_reindex e f a b E).mp hE⟩
  have hbr : LW.Bip.edgeBracket (l k) (n k) (m k) a' b' (e i) (f j) =
      bipartiteBracket (l k) (n k) (m k) a b i j := by
    rw [LW.Bip.edgeBracket, bipartite_var_eq a' ha, bipartite_var_eq b' hb]
    simp only [a',b',degreeVariance_reindex,Function.comp_apply,Equiv.symm_apply_apply,
      bipartiteBracket,leftAverage,rightAverage]
  have hprob : (bipartiteFixedDegreeLaw a b).real {E | (i,j) ∈ E} =
      LW.Bip.probEdge (l k) (n k) (m k) a' b' (e i) (f j) :=
    (bipartite_law_reindex e f a b i j).trans (bipartite_edge_law a' b' ha hr (e i) (f j))
  rw [hprob,hEq,hbr]
  simp only [a',b',Function.comp_apply,Equiv.symm_apply_apply]
  have hp0 : 0 ≤ bipartitePrefactor (m k) (a i) (b j) := by unfold bipartitePrefactor; positivity
  calc
    _ = bipartitePrefactor (m k) (a i) (b j)*|θ| := by
      rw [show (a i:ℝ)*b j/m k*(bipartiteBracket (l k) (n k) (m k) a b i j+θ)-
        bipartiteApproximation (l k) (n k) (m k) a b i j =
        bipartitePrefactor (m k) (a i) (b j)*θ by
          unfold bipartiteApproximation bipartitePrefactor; ring,
        abs_mul,abs_of_nonneg hp0]
    _ ≤ bipartitePrefactor (m k) (a i) (b j) *
        (max C 1 * bipartiteErrorScale (l k) (n k) (m k) α) := by
      apply mul_le_mul_of_nonneg_left _ hp0
      apply hθ.trans
      apply mul_le_mul_of_nonneg_right (le_max_left _ _)
      unfold LW.Bip.err15
      positivity

end MajorityDynamics.Literature.LWAdapters
