import MajorityDynamics.Analysis.GaussianTail
import Mathlib.Probability.Independence.Basic

/-! # Exact Gaussian laws and small-ball bounds for finite linear forms -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace MajorityDynamics.Analysis

theorem gaussian_sum_law {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ι → Ω → ℝ) (m : ι → ℝ) (v : ι → ℝ≥0)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = gaussianReal (m i) (v i)) (S : Finset ι) :
    P.map (fun ω => ∑ i ∈ S, X i ω) = gaussianReal (∑ i ∈ S, m i) (∑ i ∈ S, v i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    have hsum : (∑ j ∈ S, X j) = (fun ω => ∑ j ∈ S, X j ω) := by ext ω; simp
    rw [← hsum] at ih
    have h := gaussianReal_add_gaussianReal_of_indepFun
      (hind.indepFun_finsetSum_of_notMem hX hi).symm (hlaw i) ih
    rw [show (X i + ∑ j ∈ S, X j) = (fun ω => X i ω + ∑ j ∈ S, X j ω) from
      by ext ω; simp] at h
    exact h

theorem gaussian_linear_law {ι : Type*} [Fintype ι]
    (m a : ι → ℝ) (v : ι → ℝ≥0) :
    (Measure.pi (fun i => gaussianReal (m i) (v i))).map (fun x => ∑ i, a i * x i) =
      gaussianReal (∑ i, a i * m i) (∑ i, NNReal.mk (a i ^ 2) (sq_nonneg _) * v i) := by
  let P := Measure.pi (fun i => gaussianReal (m i) (v i))
  have hcoord (i : ι) : P.map (fun x => a i * x i) =
      gaussianReal (a i * m i) (NNReal.mk (a i ^ 2) (sq_nonneg _) * v i) := by
    have heval := (measurePreserving_eval (fun j => gaussianReal (m j) (v j)) i).map_eq
    have hmap := gaussianReal_map_const_mul (μ := m i) (v := v i) (a i)
    rw [← heval, Measure.map_map (show Measurable (fun y : ℝ => a i * y) by fun_prop) (show Measurable (Function.eval i) from measurable_pi_apply i)] at hmap
    exact hmap
  exact gaussian_sum_law P (fun i x => a i * x i) (fun i => a i * m i)
    (fun i => NNReal.mk (a i ^ 2) (sq_nonneg _) * v i) (fun _ => by fun_prop)
    (iIndepFun_pi (fun _ => by fun_prop)) hcoord Finset.univ

theorem gaussian_linear_strip {ι : Type*} [Fintype ι]
    (m a : ι → ℝ) (v : ι → ℝ≥0)
    (hv : 0 < ∑ i, NNReal.mk (a i ^ 2) (sq_nonneg _) * v i) (b R : ℝ) (hR : 0 ≤ R) :
    (Measure.pi (fun i => gaussianReal (m i) (v i))).real
      {x | |(∑ i, a i * x i) - b| ≤ R} ≤
        2 * R / Real.sqrt (2 * Real.pi * (∑ i, a i ^ 2 * (v i : ℝ))) := by
  have h := gaussian_interval_le (∑ i, a i * m i)
    (∑ i, NNReal.mk (a i ^ 2) (sq_nonneg _) * v i) hv (b - R) (b + R) (by linarith)
  rw [← gaussian_linear_law m a v, map_measureReal_apply (by fun_prop) measurableSet_Icc] at h
  have heq : (fun x : ι → ℝ => ∑ i, a i * x i) ⁻¹' Set.Icc (b - R) (b + R) =
      {x | |(∑ i, a i * x i) - b| ≤ R} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_ofPred_eq, abs_le]
    constructor <;> intro hh <;> constructor <;> linarith [hh.1, hh.2]
  rw [heq] at h
  simpa only [NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_mk, show b + R - (b - R) = 2 * R by ring] using h

end MajorityDynamics.Analysis
