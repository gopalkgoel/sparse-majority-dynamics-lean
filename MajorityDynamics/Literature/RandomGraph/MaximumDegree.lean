import MajorityDynamics.Literature.RandomGraph.EdgeCount
import MajorityDynamics.Literature.Concentration.BinomialUpperTail

noncomputable section
open MeasureTheory ProbabilityTheory
open MajorityDynamics.Paper
open scoped unitInterval

namespace MajorityDynamics.Literature.RandomGraph
attribute [local instance] Classical.propDecidable

def DegreeBound {N : ℕ} (G : Graph N) (p : unitInterval) : Prop :=
  ∀ v, (G.degree v : ℝ) ≤ 2 * (p : ℝ) * N

lemma degree_upper_tail {N : ℕ} (hN : 2 ≤ N) (p : unitInterval)
    (hp : 0 < (p : ℝ)) (v : Fin N) :
    graphLaw N p {G | 2 * (p : ℝ) * N < (G.degree v : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-((p : ℝ) * N) / 3)) := by
  let d : ℝ := (p : ℝ) * N
  let μ : ℝ := (N - 1 : ℕ) * (p : ℝ)
  have hd : 0 < d := mul_pos hp (by exact_mod_cast (by omega : 0 < N))
  have hμ : 0 < μ := mul_pos (by exact_mod_cast (by omega : 0 < N - 1)) hp
  have hμd : μ ≤ d := by
    have h : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
    dsimp [μ, d]
    nlinarith
  have ht := Concentration.binomial_upper_tail (N - 1) p hμ d hd.le
  have hmap := map_degree v p
  have he : graphLaw N p {G | μ + d ≤ (G.degree v : ℝ)} =
      binomial (N - 1) p {k | μ + d ≤ (k : ℝ)} := by
    rw [← hmap, Measure.map_apply (.of_discrete) (.of_discrete)]
    rfl
  refine (measure_mono (show {G : Graph N | 2 * (p : ℝ) * N < (G.degree v : ℝ)} ⊆
      {G | μ + d ≤ (G.degree v : ℝ)} from fun G hG => by
        change 2 * (p : ℝ) * N < (G.degree v : ℝ) at hG
        change μ + d ≤ (G.degree v : ℝ)
        dsimp [d] at hμd ⊢
        linarith)).trans ?_
  rw [he, ← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  apply ENNReal.ofReal_le_ofReal
  refine ht.trans (Real.exp_le_exp.mpr ?_)
  change -(d ^ 2) / (2 * μ + 2 * d / 3) ≤ -d / 3
  apply (div_le_iff₀ (by positivity : 0 < 2 * μ + 2 * d / 3)).mpr
  nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hμd)]

lemma maximumDegree_failure {N : ℕ} (hN : 2 ≤ N) (p : unitInterval)
    (hp : 0 < (p : ℝ)) :
    graphLaw N p {G | DegreeBound G p}ᶜ ≤
      ENNReal.ofReal ((N : ℝ) * Real.exp (-((p : ℝ) * N) / 3)) := by
  have he : {G : Graph N | DegreeBound G p}ᶜ =
      ⋃ v : Fin N, {G | 2 * (p : ℝ) * N < (G.degree v : ℝ)} := by
    ext G
    simp [DegreeBound, not_forall]
  rw [he]
  refine (measure_iUnion_le _).trans ?_
  calc
    _ ≤ ∑' _ : Fin N, ENNReal.ofReal (Real.exp (-((p : ℝ) * N) / 3)) :=
      ENNReal.tsum_le_tsum fun v => degree_upper_tail hN p hp v
    _ = _ := by simp [tsum_fintype, ENNReal.ofReal_mul]

end MajorityDynamics.Literature.RandomGraph
