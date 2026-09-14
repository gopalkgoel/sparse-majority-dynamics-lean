import MajorityDynamics.Literature.LWAdapters.BipartiteLaws
import MajorityDynamics.Literature.LWAdapters.Growth
import MajorityDynamics.Literature.LWFormal.Bip.Final

noncomputable section
open Filter
open scoped Topology
namespace MajorityDynamics.Literature.LWAdapters
open DegreeEnumeration

theorem bipartite_mean_eq {n m : ℕ} (a : Fin n → ℕ) (hs : ∑ i, a i = m) :
    LW.Bip.mean a = (m : ℝ)/n := by
  have hh : ∑ i, (a i : ℝ) = m := by exact_mod_cast hs
  simp [LW.Bip.mean, hh]

theorem bipartite_density_eq {l n m : ℕ} (a : Fin l → ℕ) (b : Fin n → ℕ)
    (ha : ∑ i, a i = m) (hb : ∑ j, b j = m) :
    LW.Bip.muN a b = bipartiteDensity l n m := by
  have ha' : ∑ i, (a i : ℝ) = m := by exact_mod_cast ha
  have hb' : ∑ i, (b i : ℝ) = m := by exact_mod_cast hb
  simp only [LW.Bip.muN, ha', hb', bipartiteDensity, div_eq_mul_inv, mul_inv_rev]
  norm_num
  ring

theorem bipartite_correction_eq {l n m : ℕ} (a : Fin l → ℕ) (b : Fin n → ℕ)
    (ha : ∑ i, a i = m) (hb : ∑ j, b j = m) :
    LW.Bip.Htilde a b = bipartiteCorrection m a b := by
  simp only [LW.Bip.Htilde, LW.Bip.var, bipartite_mean_eq a ha, bipartite_mean_eq b hb,
    bipartite_density_eq a b ha hb, bipartiteCorrection, leftVariance, rightVariance,
    leftAverage, rightAverage]
  congr 1
  ring

theorem bipartite_enumeration : BipartiteEnumerationTheorem := by
  obtain ⟨μ₀, hμ₀, hsource⟩ := LW.Bip.theorem_1_1
  refine ⟨μ₀, hμ₀, ?_⟩
  intro α hαlo hαhi l m hcap hpowers hlogs
  obtain ⟨ω,hω,hgrowth⟩ := bipartite_slow_growth l id m tendsto_id α hpowers hlogs
  obtain ⟨C,N,hbound⟩ := hsource α hαlo hαhi ω hω
  refine ⟨max C 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  filter_upwards [hcap,hgrowth,eventually_ge_atTop N] with n hc hg hn
  intro a b hd
  obtain ⟨e,he,hEq⟩ := hbound n hn (l n) (m n)
    (by simpa only [bipartiteDensity, mul_comm] using hc.2.2) hg.1 hg.2 a b
    ⟨hd.2.2.1,hd.2.2.2.1,hd.2.2.2.2.1,hd.2.2.2.2.2⟩
  refine ⟨e, ?_, ?_⟩
  · apply he.trans
    apply mul_le_mul_of_nonneg_right (le_max_left _ _)
    unfold LW.Bip.err11
    positivity
  · rw [probG_eq_bipartiteDegreeLaw, bipartite_correction_eq a b hd.2.2.1 hd.2.2.2.1,
      probB_eq_bipartiteBinomialLaw a b hc.2.1 hd.2.2.1 hd.2.2.2.1] at hEq
    exact hEq

end MajorityDynamics.Literature.LWAdapters
