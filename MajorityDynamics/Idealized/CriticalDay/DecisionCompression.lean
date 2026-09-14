import MajorityDynamics.Idealized.CriticalDay.GaussianGain
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! A rank-one compression changes only the last imbalance. Its determinant
is exactly the compression factor; all history inequalities are unchanged. -/
noncomputable section
open Set MeasureTheory
open scoped Matrix
open MajorityDynamics.Universal MajorityDynamics.Analysis
namespace MajorityDynamics.Idealized.CriticalDay
variable {n : ℕ}

def decisionProjection (n : ℕ) : Row (n + 1) →L[ℝ] Row (n + 1) :=
  ConditionalGaussian.matrixCLM
    (Matrix.replicateCol Unit (fun t => character (Fin.last n) t /
      (Fintype.card (History (n + 1)) : ℝ)) *
      Matrix.replicateRow Unit (character (Fin.last n)))

theorem decisionProjection_apply (x : Row (n + 1)) (t : History (n + 1)) :
    decisionProjection n x t = imbalance (Fin.last n) x /
      (Fintype.card (History (n + 1)) : ℝ) * character (Fin.last n) t := by
  change (∑ j, (∑ _i : Unit, (character (Fin.last n) t /
    (Fintype.card (History (n + 1)) : ℝ)) * character (Fin.last n) j) * x j) = _
  simp only [Finset.univ_unique, Finset.sum_singleton]
  unfold imbalance
  rw [Finset.sum_div, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem imbalance_decisionProjection (r : Fin (n + 1)) (x : Row (n + 1)) :
    imbalance r (decisionProjection n x) =
      if r = Fin.last n then imbalance (Fin.last n) x else 0 := by
  unfold imbalance
  simp_rw [decisionProjection_apply]
  have he : (∑ t, character r t *
      (imbalance (Fin.last n) x / (Fintype.card (History (n + 1)) : ℝ) *
        character (Fin.last n) t)) =
      (imbalance (Fin.last n) x / (Fintype.card (History (n + 1)) : ℝ)) *
        ∑ t, character r t * character (Fin.last n) t := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [he, character_orthogonal]
  split_ifs <;> simp [imbalance]

def decisionCompression (n : ℕ) (u : ℝ) : Row (n + 1) →L[ℝ] Row (n + 1) :=
  ContinuousLinearMap.id ℝ (Row (n + 1)) + (u - 1) • decisionProjection n

theorem imbalance_decisionCompression (r : Fin (n + 1)) (x : Row (n + 1)) (u : ℝ) :
    imbalance r (decisionCompression n u x) =
      if r = Fin.last n then u * imbalance r x else imbalance r x := by
  change imbalance r (x + (u - 1) • decisionProjection n x) = _
  rw [← imbalanceCLM_apply, map_add, map_smul]
  simp only [imbalanceCLM_apply, smul_eq_mul, imbalance_decisionProjection]
  split_ifs with h
  · subst r
    ring
  · ring

theorem decisionCompression_det (n : ℕ) (u : ℝ) :
    LinearMap.det (decisionCompression n u).toLinearMap = u := by
  let D : ℝ := Fintype.card (History (n + 1))
  let v : History (n + 1) → ℝ := fun t => (u - 1) * character (Fin.last n) t / D
  let w : History (n + 1) → ℝ := character (Fin.last n)
  let A := 1 + Matrix.replicateCol Unit v * Matrix.replicateRow Unit w
  have heq : decisionCompression n u = ConditionalGaussian.matrixCLM A := by
    ext x t
    change x t + (u - 1) * decisionProjection n x t = _
    rw [decisionProjection_apply]
    change _ = ((1 + Matrix.replicateCol Unit v * Matrix.replicateRow Unit w) *ᵥ x.ofLp) t
    rw [Matrix.add_mulVec, Matrix.one_mulVec]
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Matrix.replicateCol_apply, Matrix.replicateRow_apply, Finset.univ_unique,
      Finset.sum_singleton]
    dsimp [v, w, D]
    unfold imbalance
    rw [Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  change LinearMap.det (Matrix.toLin (EuclideanSpace.basisFun _ ℝ).toBasis
    (EuclideanSpace.basisFun _ ℝ).toBasis A) = u
  rw [LinearMap.det_toLin]
  dsimp [A]
  rw [Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hdot : w ⬝ᵥ v = u - 1 := by
    change (∑ t, character (Fin.last n) t * ((u - 1) * character (Fin.last n) t / D)) = _
    calc
      _ = ((u - 1) / D) * ∑ t, character (Fin.last n) t * character (Fin.last n) t := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        ring
      _ = u - 1 := by rw [character_orthogonal]; simp [D]
  rw [hdot]
  ring

theorem decisionCompression_slab (s : History (n + 1)) {u : ℝ} (hu : 0 < u) :
    decisionCompression n u '' gainSlab s 1 ⊆ gainSlab s u := by
  rintro y ⟨x, hx, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [mem_historyCone]
    intro r
    rw [imbalance_decisionCompression, if_neg (Fin.castSucc_ne_last r)]
    exact (mem_historyCone s x).mp hx.1 r
  · change -u < imbalance (Fin.last n) (decisionCompression n u x) ∧
      imbalance (Fin.last n) (decisionCompression n u x) < 0
    rw [imbalance_decisionCompression, if_pos rfl]
    constructor <;> nlinarith [mul_pos hu (show 0 < imbalance (Fin.last n) x + 1 by
      linarith [hx.2.1]), mul_neg_of_pos_of_neg hu hx.2.2]

end MajorityDynamics.Idealized.CriticalDay
