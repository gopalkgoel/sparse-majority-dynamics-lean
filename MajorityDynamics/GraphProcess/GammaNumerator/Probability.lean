import MajorityDynamics.GraphProcess.GammaNumerator.Statistics
import MajorityDynamics.GraphProcess.GammaNumerator.Regime
import MajorityDynamics.Probability.DegreeConcentration.Main

/-! A.10 on the actual restrictions, then a finite union bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.GammaNumerator
open Universal Probability.DegreeConcentration
universe u
variable {V : Type u} [Fintype V] {n : ℕ}

/-- Common block rate; the spare unit absorbs the fixed number of pairs. -/
def blockRate (T K : ℝ) : ℝ := T*(K+1)

/-- One Gamma constant for both A.10 models. -/
def numeratorConstant (T K : ℝ) : ℝ := max 1 (gammaConstant T (blockRate T K))

theorem numeratorConstant_ge_one (T K : ℝ) : 1 ≤ numeratorConstant T K :=
  le_max_left _ _

theorem block_rate_comparison {N a T K : ℝ} (hT : 0 < T) (hK : 0 ≤ K)
    (ha : N/T ≤ a) :
    Real.exp (-blockRate T K*a) ≤ Real.exp (-(K+1)*N) := by
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left ((div_le_iff₀ hT).mp ha)
    (show 0 ≤ K+1 by linarith)
  dsimp [blockRate]
  nlinarith

/-- Every actual block bad event has the A.10 bound at its actual size. -/
theorem block_probability (π : V → History (n+1)) (p : unitInterval)
    {T K : ℝ} (hT : 1 < T) (hK : 0 ≤ K) (hp : 0 < (p : ℝ))
    (hs2 : ∀ s, 2 ≤ Local.partSizes π s)
    (hratio : ∀ s t, sizeRange T (Local.partSizes π t) (Local.partSizes π s))
    (s t : History (n+1)) :
    (SimpleGraph.binomialRandom V p).real (blockBad π (numeratorConstant T K) p s t) ≤
      Real.exp (-blockRate T K * (Local.partSizes π t : ℝ)) := by
  have hcG : 160*(blockRate T K+2) ≤ numeratorConstant T K :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hcB : 20*T^2*(blockRate T K+T) ≤ numeratorConstant T K :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hT0 : 0 < T := by linarith
  have hrate : 0 ≤ blockRate T K := by dsimp [blockRate]; positivity
  by_cases hst : s = t
  · subst t
    have hh := graph_bound (n := blockSize π s) (by simpa using (show 0 < Local.partSizes π s by have := hs2 s; omega))
      p hp (numeratorConstant T K) (blockRate T K) hcG
    rw [← internal_law π s p, Measure.map_apply (measurable_of_countable _)
      (Set.toFinite _).measurableSet] at hh
    have ht := ENNReal.toReal_mono (by simp [failureBound]) hh
    simpa only [blockBad, if_pos rfl, ite_true, measureReal_def, failureBound,
      ENNReal.toReal_ofReal (Real.exp_nonneg _), blockSize_eq] using ht
  · have hh := bipartite_bound (n := blockSize π t) (ℓ := blockSize π s)
      (by simpa using hs2 t) p hp T hT (by simpa using hratio s t)
      (numeratorConstant T K) (blockRate T K) hrate hcB
    rw [← cross_law π s t hst p, Measure.map_apply (measurable_of_countable _)
      (Set.toFinite _).measurableSet] at hh
    have ht := ENNReal.toReal_mono (by simp [failureBound]) hh
    simpa only [blockBad, if_neg hst, measureReal_def, failureBound,
      ENNReal.toReal_ofReal (Real.exp_nonneg _), blockSize_eq] using ht

/-- Before absorbing the fixed number of ordered pairs, the original bad event
costs at most h² times one block failure. -/
theorem graph_numerator_bound (π : V → History (n+1)) (p : unitInterval)
    {N : ℕ} {T K : ℝ} (hT : 1 < T) (hK : 0 ≤ K) (hp : 0 < (p : ℝ))
    (_hcard : Fintype.card V = N)
    (hsizes : ∀ s, (N : ℝ)/T ≤ (Local.partSizes π s : ℝ))
    (hs2 : ∀ s, 2 ≤ Local.partSizes π s)
    (hratio : ∀ s t, sizeRange T (Local.partSizes π t) (Local.partSizes π s))
    (htol : ∀ s, ((p : ℝ)*Fintype.card V)^((4:ℝ)/7) ≤
      (p : ℝ)*(Local.partSizes π s : ℝ)) :
    (SimpleGraph.binomialRandom V p).real {G |
      ¬ RowArray.Gamma π (RowArray.totals (RowArray.graphArray π G))
        (numeratorConstant T K) p (RowArray.graphArray π G) ∧
      RowArray.Regular p (RowArray.graphArray π G)} ≤
      (Fintype.card (History (n+1)) : ℝ)^2 * Real.exp (-(K+1)*(N : ℝ)) := by
  have hC : 0 ≤ numeratorConstant T K := le_trans (by norm_num) (numeratorConstant_ge_one T K)
  refine (measureReal_mono (event_subset_iUnion π _ p hp hC htol)).trans ?_
  refine (measureReal_iUnion_fintype_le _).trans ?_
  calc
    ∑ s, (SimpleGraph.binomialRandom V p).real (⋃ t, blockBad π (numeratorConstant T K) p s t) ≤
        ∑ s, ∑ t, (SimpleGraph.binomialRandom V p).real (blockBad π (numeratorConstant T K) p s t) := by
      exact Finset.sum_le_sum fun s _ => measureReal_iUnion_fintype_le _
    _ ≤ ∑ _s : History (n+1), ∑ _t : History (n+1), Real.exp (-(K+1)*(N : ℝ)) := by
      apply Finset.sum_le_sum
      intro s _
      apply Finset.sum_le_sum
      intro t _
      exact (block_probability π p hT hK hp hs2 hratio s t).trans
        (block_rate_comparison (by linarith) hK (hsizes t))
    _ = _ := by simp; ring

end MajorityDynamics.GraphProcess.GammaNumerator
