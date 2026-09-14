import MajorityDynamics.Probability.RandomOpinionsReduction.Basic
import Mathlib.Tactic

/-! # Opinion reversal and permanent consensus (`cor:random-opinions`)
The zero-neighborhood-sum case is retained throughout, including isolated vertices.
-/
noncomputable section
open scoped BigOperators
namespace MajorityDynamics.Probability.RandomOpinionsReduction

@[simp] theorem opinion_not (b : Bool) : Paper.opinion (!b) = -Paper.opinion b := by
  cases b <;> norm_num [Paper.opinion]

theorem neighborSum_flip {N : ℕ} (G : Paper.Graph N) (c : Paper.Coloring N) (v : Fin N) :
    Paper.neighborSum G (flip c) v = -Paper.neighborSum G c v := by
  classical
  simp only [Paper.neighborSum, flip, opinion_not, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro w _
  split_ifs <;> simp

theorem nextColoring_flip {N : ℕ} (G : Paper.Graph N) (c : Paper.Coloring N) :
    Paper.nextColoring G (flip c) = flip (Paper.nextColoring G c) := by
  funext v
  simp only [Paper.nextColoring, neighborSum_flip, flip]
  split_ifs <;> simp_all
  omega

theorem coloringOnDay_flip {N : ℕ} (G : Paper.Graph N) (c : Paper.Coloring N) (t : ℕ) :
    Paper.coloringOnDay G (flip c) t = flip (Paper.coloringOnDay G c t) := by
  unfold Paper.coloringOnDay
  generalize t - 1 = n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply', ih, nextColoring_flip]

theorem nextColoring_constant {N : ℕ} (G : Paper.Graph N) (b : Bool) :
    Paper.nextColoring G (fun _ => b) = (fun _ => b) := by
  classical
  have hp (v : Fin N) : 0 ≤ Paper.neighborSum G (fun _ => false) v := by
    unfold Paper.neighborSum
    apply Finset.sum_nonneg
    intro w _
    split_ifs <;> norm_num [Paper.opinion]
  have hm (v : Fin N) : Paper.neighborSum G (fun _ => true) v ≤ 0 := by
    have h := neighborSum_flip G (fun _ => false) v
    change Paper.neighborSum G (fun _ => true) v = -Paper.neighborSum G (fun _ => false) v at h
    linarith [hp v]
  funext v
  cases b
  · have hv := hp v
    simp [Paper.nextColoring, not_lt.mpr hv]
  · have hv := hm v
    simp [Paper.nextColoring, not_lt.mpr hv]

theorem iterate_constant {N : ℕ} (G : Paper.Graph N) (b : Bool) (n : ℕ) :
    (Paper.nextColoring G)^[n] (fun _ => b) = (fun _ => b) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Function.iterate_succ_apply', ih, nextColoring_constant]

theorem consensus_persistence {N : ℕ} (G : Paper.Graph N) (c : Paper.Coloring N)
    (k t : ℕ) (hkt : k ≤ t) (b : Bool)
    (h : ∀ v, Paper.coloringOnDay G c k v = b) :
    ∀ v, Paper.coloringOnDay G c t v = b := by
  have hh : Paper.coloringOnDay G c k = (fun _ => b) := funext h
  have hi : t - 1 = (t - 1 - (k - 1)) + (k - 1) := by omega
  unfold Paper.coloringOnDay at hh ⊢
  rw [hi, Function.iterate_add_apply, hh, iterate_constant]
  intro v
  rfl

theorem consensusEvent_iff {N : ℕ} (θ : ℝ) (c : Paper.Coloring N) (G : Paper.Graph N) :
    (c, G) ∈ consensusEvent N θ ↔
      ∃ b : Bool, ∀ v, Paper.coloringOnDay G c (Paper.convergenceDay θ) v = b := by
  constructor
  · rintro ⟨b, h⟩
    exact ⟨b, h _ le_rfl⟩
  · rintro ⟨b, h⟩
    exact ⟨b, fun t ht => consensus_persistence G c _ t ht b h⟩

theorem flip_success_probability {N : ℕ} (θ : ℝ) (p : unitInterval) (c : Paper.Coloring N) :
    Paper.graphLaw N p (Paper.successEvent θ (flip c)) =
      Paper.graphLaw N p {G | ∀ v, Paper.coloringOnDay G c (Paper.convergenceDay θ) v = true} := by
  congr 1
  ext G
  simp [Paper.successEvent, coloringOnDay_flip, flip]

end MajorityDynamics.Probability.RandomOpinionsReduction
