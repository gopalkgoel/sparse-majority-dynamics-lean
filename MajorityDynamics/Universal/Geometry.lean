import MajorityDynamics.Universal.Histories
import MajorityDynamics.Analysis.ConditionalGaussian.Cones

/-! # Nonempty history cones and their behavior under refinement -/

noncomputable section

open Set
open MajorityDynamics.Analysis
open scoped Matrix RealInnerProductSpace

namespace MajorityDynamics.Universal

variable {k n : ℕ}

def characterVector (r : Fin k) : Row k := WithLp.toLp 2 (character r)

theorem imbalance_eq_inner (r : Fin k) (x : Row k) :
    imbalance r x = ⟪characterVector r, x⟫ := by
  simp [imbalance, characterVector, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

def imbalanceCLM (r : Fin k) : Row k →L[ℝ] ℝ := innerSL ℝ (characterVector r)

@[simp] theorem imbalanceCLM_apply (r : Fin k) (x : Row k) :
    imbalanceCLM r x = imbalance r x := (imbalance_eq_inner r x).symm

theorem imbalance_continuous (r : Fin k) : Continuous (imbalance r) :=
  by
  have h : (imbalance r) = fun x => imbalanceCLM r x := funext fun x => (imbalanceCLM_apply r x).symm
  rw [h]
  exact (imbalanceCLM r).continuous

def synthesize (a : Fin k → ℝ) : Row k :=
  WithLp.toLp 2 (fun t => ∑ r, a r * character r t)

theorem imbalance_synthesize (r : Fin k) (a : Fin k → ℝ) :
    imbalance r (synthesize a) = (Fintype.card (History k) : ℝ) * a r := by
  change (∑ t, character r t * ∑ q, a q * character q t) = _
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have he (q : Fin k) : (∑ t, character r t * (a q * character q t)) =
      a q * ∑ t, character r t * character q t := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  simp_rw [he, character_orthogonal]
  simp [mul_comm]

theorem characterVector_ne_zero (r : Fin k) : characterVector r ≠ 0 := by
  intro h
  have hs := character_orthogonal r r
  have hz : ∀ t, character r t = 0 := fun t => congrArg (fun x : Row k => x t) h
  simp only [hz, mul_zero, Finset.sum_const_zero] at hs
  exact (history_card_pos k).ne' hs.symm

theorem mem_historyCone (s : History (n + 1)) (x : Row (n + 1)) :
    x ∈ historyCone s ↔ ∀ r : Fin n,
      0 < sign (bits (n + 1) s r.succ) * imbalance r.castSucc x := by
  simp only [historyCone, ConditionalGaussian.cone, mem_ofPred_eq, Matrix.mulVec,
    dotProduct, historyMatrix, imbalance, Finset.mul_sum, mul_assoc]

theorem historyCone_isOpen (s : History (n + 1)) : IsOpen (historyCone s) :=
  ConditionalGaussian.cone_isOpen _

theorem historyCone_convex (s : History (n + 1)) : Convex ℝ (historyCone s) :=
  ConditionalGaussian.cone_convex _

theorem childCone_isOpen (s : History (n + 1)) (b : Bool) : IsOpen (childCone s b) :=
  (historyCone_isOpen s).inter (isOpen_lt continuous_const
    (continuous_const.mul (imbalance_continuous _)))

theorem childCone_convex (s : History (n + 1)) (b : Bool) : Convex ℝ (childCone s b) := by
  apply (historyCone_convex s).inter
  simpa only [LinearMap.smul_apply, ContinuousLinearMap.coe_coe, imbalanceCLM_apply,
    smul_eq_mul] using
    convex_halfSpace_gt ((sign b) • (imbalanceCLM (Fin.last n)).toLinearMap).isLinear 0

/-- Orthogonal characters realize arbitrary signs of all `k` history forms. -/
theorem childCone_nonempty (s : History (n + 1)) (b : Bool) : (childCone s b).Nonempty := by
  let a : Fin (n + 1) → ℝ := Fin.snoc (fun r => sign (bits (n + 1) s r.succ)) (sign b)
  refine ⟨synthesize a, ?_, ?_⟩
  · rw [mem_historyCone]
    intro r
    rw [imbalance_synthesize]
    simp only [a, Fin.snoc_castSucc]
    nlinarith [history_card_pos (n + 1), sign_sq (bits (n + 1) s r.succ)]
  · change 0 < sign b * imbalance (Fin.last n) (synthesize a)
    rw [imbalance_synthesize]
    simp only [a, Fin.snoc_last]
    nlinarith [history_card_pos (n + 1), sign_sq b]

theorem historyCone_nonempty (s : History (n + 1)) : (historyCone s).Nonempty :=
  (childCone_nonempty s false).mono inter_subset_left

@[simp] theorem historyCone_one (s : History 1) : historyCone s = univ :=
  ConditionalGaussian.cone_zero_rows _

/-- The children-sum identity transports strict inequalities to the next level. -/
theorem historyCone_of_children (s : History (n + 1)) (b : Bool)
    (x : Row (n + 2)) (y : Row (n + 1))
    (hxy : ∀ t, x (append t false) + x (append t true) = y t)
    (hy : y ∈ childCone s b) : x ∈ historyCone (append s b) := by
  have he : WithLp.toLp 2 (fun t => x (append t false) + x (append t true)) = y := by
    ext t
    exact hxy t
  rw [mem_historyCone]
  intro r
  rw [imbalance_children, he]
  refine Fin.lastCases ?_ (fun i => ?_) r
  · simpa using hy.2
  · simpa only [← Fin.castSucc_succ, bits_append_castSucc] using (mem_historyCone s y).mp hy.1 i

@[simp] theorem rowFlip_mem_historyCone (s : History (n + 1)) (x : Row (n + 1)) :
    rowFlip x ∈ historyCone (flip s) ↔ x ∈ historyCone s := by
  simp [mem_historyCone, imbalance_rowFlip]

@[simp] theorem rowFlip_mem_childCone (s : History (n + 1)) (b : Bool) (x : Row (n + 1)) :
    rowFlip x ∈ childCone (flip s) (!b) ↔ x ∈ childCone s b := by
  simp [childCone, imbalance_rowFlip]

theorem covariance_posDef (ν : History k → ℝ) (hν : ∀ t, 0 < ν t) :
    (covariance ν).PosDef := Matrix.PosDef.diagonal hν

end MajorityDynamics.Universal
