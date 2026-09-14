import MajorityDynamics.Literature.LWAdapters.GraphError
import MajorityDynamics.Literature.LWAdapters.FixedDegreeLaws
import MajorityDynamics.Literature.LWAdapters.Reindex
import MajorityDynamics.Literature.Goals.GraphEdgeProbability.Statement

noncomputable section
open Filter MeasureTheory
open scoped Classical Topology
namespace MajorityDynamics.Literature.LWAdapters
open MajorityDynamics.Probability.FixedDegreeSampling
open EdgeProbabilities
universe u

theorem graph_edge_probability : GraphEdgeProbabilityTheorem.{u} := by
  obtain ⟨μ₀,hμ₀,hsource⟩ := LW.theorem_1_6
  refine ⟨min μ₀ (1/4), lt_min hμ₀ (by norm_num), ?_⟩
  intro α hαlo hαhi n m hn hdensity hlogs
  obtain ⟨ω,hω,hgrowth⟩ := graph_slow_growth n m hn hlogs
  obtain ⟨C,N,hbound⟩ := hsource α hαlo hαhi ω hω
  let C' := max C 1
  have hC' : 0 < C' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  refine ⟨8*(8+C'), by positivity, ?_⟩
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hn)).eventually_ge_atTop 1
  filter_upwards [hdensity,hgrowth,hn.eventually_ge_atTop N,hn.eventually_ge_atTop 4,
    graph_log_lower n m hn hlogs 0,hlog] with k hk hg hNk hn4 hDlow hlog1
  intro V _ d hd a b hab
  have hn4' : (4:ℝ) ≤ n k := by exact_mod_cast hn4
  have hnm1 : (0:ℝ) < (n k : ℝ)-1 := by linarith
  have hsmall : graphAverage (n k) (m k) ≤ (n k : ℝ)/4 := by
    have hh := (div_le_iff₀ hnm1).mp (hk.trans (min_le_right _ _))
    linarith
  have hsourceD : graphAverage (n k) (m k) ≤ μ₀*(n k : ℝ) := by
    have hh := (div_le_iff₀ hnm1).mp (hk.trans (min_le_left _ _))
    nlinarith
  change 1 ≤ Real.log (n k) at hlog1
  have hD : 1 ≤ graphAverage (n k) (m k) := by
    norm_num [DegreeEnumeration.graphAverage, graphAverage] at hDlow ⊢
    linarith
  let e : V ≃ Fin (n k) := Fintype.equivFinOfCardEq hd.card_eq
  let d' := d ∘ e.symm
  have hs : ∑ i, d' i = 2*m k := (Equiv.sum_comp e.symm d).trans hd.total
  have hIn : LW.InD α (n k) (m k) d' := ⟨hs,fun i => hd.spread (e.symm i)⟩
  obtain ⟨θ,hθ,hEq⟩ := hbound (n k) hNk (m k) hg hsourceD d' hIn (e a) (e b)
    (fun h => hab (e.injective h))
  have hr : (graphFamily d').Nonempty := by
    obtain ⟨G,hG⟩ := hd.realizable
    exact ⟨graphEquiv e G,(graph_family_reindex e d G).mp hG⟩
  have hθ' : |θ| ≤ C'*LW.err16 α (n k) (2*m k/n k) := by
    apply hθ.trans
    apply mul_le_mul_of_nonneg_right (le_max_left _ _)
    unfold LW.err16
    positivity
  have he := corrected_graph_error d' hIn hαhi hn4' hD hsmall hC'.le hθ' (e a) (e b)
  rw [graph_law_reindex e d a b, graph_edge_law d' hs hr (e a) (e b)
    (fun h => hab (e.injective h)),hEq]
  simpa only [d',Function.comp_apply,Equiv.symm_apply_apply,graphErrorScale,graphAverage] using he

end MajorityDynamics.Literature.LWAdapters
