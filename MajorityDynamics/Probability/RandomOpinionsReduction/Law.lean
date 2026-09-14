import MajorityDynamics.Probability.RandomOpinionsReduction.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Tactic

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace MajorityDynamics.Probability.RandomOpinionsReduction

theorem coloring_singleton (N : ℕ) (c : Paper.Coloring N) :
    uniformColoringLaw N {c} = (2 : ℝ≥0∞)⁻¹ ^ N := by
  simp [uniformColoringLaw, Measure.pi_singleton, fairBitLaw_singleton, one_div]

theorem coloring_uniform (N : ℕ) :
    uniformColoringLaw N = (PMF.uniformOfFintype (Paper.Coloring N)).toMeasure := by
  apply Measure.ext_of_singleton
  intro c
  simp [coloring_singleton, PMF.uniformOfFintype_apply, Paper.Coloring, ENNReal.inv_pow]

def coloringFinsetEquiv (N : ℕ) : Paper.Coloring N ≃ Finset (Fin N) where
  toFun c := Finset.univ.filter (fun v => c v = false)
  invFun s := fun v => if v ∈ s then false else true
  left_inv c := by
    classical
    funext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases c v <;> simp
  right_inv s := by
    classical
    ext v
    simp

theorem plusCount_flip {N : ℕ} (c : Paper.Coloring N) :
    Paper.plusCount (flip c) = N - Paper.plusCount c := by
  classical
  have h : Finset.univ.filter (fun v => flip c v = false) =
      Finset.univ \ Finset.univ.filter (fun v => c v = false) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, flip]
    cases hcv : c v <;> simp [hcv]
  unfold Paper.plusCount
  rw [h, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
  simp

theorem count_fiber_card (N a : ℕ) :
    Fintype.card {c : Paper.Coloring N // Paper.plusCount c = a} = N.choose a := by
  classical
  let e : {c : Paper.Coloring N // Paper.plusCount c = a} ≃
      {s : Finset (Fin N) // s.card = a} :=
    (coloringFinsetEquiv N).subtypeEquiv (fun c => Iff.rfl)
  rw [Fintype.card_congr e, Fintype.card_finset_len, Fintype.card_fin]

theorem plusCount_probability (N a : ℕ) :
    uniformColoringLaw N {c | Paper.plusCount c = a} =
      (N.choose a : ℝ≥0∞) / (2 : ℝ≥0∞)^N := by
  classical
  rw [coloring_uniform, PMF.toMeasure_uniformOfFintype_apply _ (Set.toFinite _).measurableSet]
  have hc : (Finset.univ.filter (fun c : Paper.Coloring N => Paper.plusCount c = a)).card =
      N.choose a := by
    simpa only [Fintype.card_subtype] using count_fiber_card N a
  simp [hc, Paper.Coloring]

theorem graph_coloring_independent (N : ℕ) (p : unitInterval) :
    ProbabilityTheory.IndepFun Prod.fst Prod.snd (jointLaw N p) := by
  exact ProbabilityTheory.indepFun_prod (X := id) (Y := id) measurable_id measurable_id

end MajorityDynamics.Probability.RandomOpinionsReduction
