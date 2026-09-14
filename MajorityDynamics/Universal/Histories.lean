import MajorityDynamics.Universal.Basic

/-! # Binary history coordinates, splitting and sign cancellation -/

noncomputable section

open Set

namespace MajorityDynamics.Universal

variable {k n : ℕ}

@[simp] theorem sign_false : sign false = 1 := rfl
@[simp] theorem sign_true : sign true = -1 := rfl
@[simp] theorem sign_not (b : Bool) : sign (!b) = -sign b := by cases b <;> norm_num [sign]
@[simp] theorem sign_sq (b : Bool) : sign b * sign b = 1 := by cases b <;> norm_num [sign]
theorem sign_ne_zero (b : Bool) : sign b ≠ 0 := by cases b <;> norm_num [sign]

@[simp] theorem bits_append_castSucc (s : History k) (b : Bool) (r : Fin k) :
    bits (k + 1) (append s b) r.castSucc = bits k s r := by simp [append]

@[simp] theorem bits_append_last (s : History k) (b : Bool) :
    bits (k + 1) (append s b) (Fin.last k) = b := by simp [append]

@[simp] theorem parent_append (s : History k) (b : Bool) : parent (append s b) = s := by
  simp [parent, append]

@[simp] theorem last_append (s : History k) (b : Bool) : last (append s b) = b := by
  simp [last]

@[simp] theorem append_parent_last (s : History (k + 1)) : append (parent s) (last s) = s := by
  simp [append, parent, last]

def appendEquiv (k : ℕ) : History k × Bool ≃ History (k + 1) where
  toFun p := append p.1 p.2
  invFun s := (parent s, last s)
  left_inv p := by simp
  right_inv := append_parent_last

theorem sum_children (f : History (k + 1) → ℝ) :
    ∑ u, f u = ∑ s : History k, (f (append s false) + f (append s true)) := by
  rw [← (appendEquiv k).sum_comp, Fintype.sum_prod_type]
  simp [appendEquiv, add_comm]

@[simp] theorem bits_flip (s : History k) (r : Fin k) :
    bits k (flip s) r = !(bits k s r) := by simp [flip]

@[simp] theorem flip_flip (s : History k) : flip (flip s) = s := by
  apply (bits k).injective
  ext r
  simp

def flipEquiv (k : ℕ) : Equiv.Perm (History k) :=
  ⟨flip, flip, flip_flip, flip_flip⟩

@[simp] theorem flip_append (s : History k) (b : Bool) :
    flip (append s b) = append (flip s) (!b) := by
  apply (bits (k + 1)).injective
  ext r
  refine Fin.lastCases ?_ (fun i => ?_) r <;> simp

@[simp] theorem character_flip (r : Fin k) (t : History k) :
    character r (flip t) = -character r t := by simp [character]

@[simp] theorem bits_bitFlip (r i : Fin k) (s : History k) :
    bits k (bitFlip r s) i = if i = r then !(bits k s r) else bits k s i := by
  simp [bitFlip, Function.update_apply]

@[simp] theorem bitFlip_bitFlip (r : Fin k) (s : History k) :
    bitFlip r (bitFlip r s) = s := by
  apply (bits k).injective
  ext i
  by_cases h : i = r <;> simp [h]

def bitFlipEquiv (r : Fin k) : Equiv.Perm (History k) :=
  ⟨bitFlip r, bitFlip r, bitFlip_bitFlip r, bitFlip_bitFlip r⟩

theorem character_orthogonal (r q : Fin k) :
    ∑ t : History k, character r t * character q t =
      if r = q then (Fintype.card (History k) : ℝ) else 0 := by
  by_cases h : r = q
  · subst q
    simp [character, sign_sq]
  · rw [if_neg h]
    have hs := Equiv.sum_comp (bitFlipEquiv r) (fun t => character r t * character q t)
    have he : ∀ t, character r (bitFlip r t) * character q (bitFlip r t) =
        -(character r t * character q t) := by
      intro t
      simp [character, Ne.symm h]
    change (∑ t, character r (bitFlip r t) * character q (bitFlip r t)) = _ at hs
    simp_rw [he, Finset.sum_neg_distrib] at hs
    linarith

theorem sum_character_of_flip_invariant (ν : History k → ℝ)
    (hν : ∀ t, ν (flip t) = ν t) (r : Fin k) :
    ∑ t, character r t * ν t = 0 := by
  have h := Equiv.sum_comp (flipEquiv k) (fun t => character r t * ν t)
  change (∑ t, character r (flip t) * ν (flip t)) = _ at h
  simp_rw [character_flip, hν, neg_mul, Finset.sum_neg_distrib] at h
  linarith

@[simp] theorem character_append_castSucc (r : Fin k) (t : History k) (b : Bool) :
    character r.castSucc (append t b) = character r t := by simp [character]

theorem imbalance_children (r : Fin k) (x : Row (k + 1)) :
    imbalance r.castSucc x =
      imbalance r (WithLp.toLp 2 (fun t => x (append t false) + x (append t true))) := by
  rw [imbalance, sum_children]
  simp only [character_append_castSucc, imbalance]
  apply Finset.sum_congr rfl
  intro t _
  ring

@[simp] theorem rowFlip_apply (x : Row k) (t : History k) : rowFlip x t = x (flip t) := rfl
@[simp] theorem rowFlip_rowFlip (x : Row k) : rowFlip (rowFlip x) = x := by ext t; simp

theorem imbalance_rowFlip (r : Fin k) (x : Row k) :
    imbalance r (rowFlip x) = -imbalance r x := by
  have h := Equiv.sum_comp (flipEquiv k) (fun t => character r t * x (flip t))
  change (∑ t, character r (flip t) * x (flip (flip t))) = _ at h
  simpa [imbalance, neg_mul, Finset.sum_neg_distrib] using h.symm

@[simp] theorem history_card (k : ℕ) : Fintype.card (History k) = 2 ^ k := by
  simp [History]

theorem history_card_pos (k : ℕ) : 0 < (Fintype.card (History k) : ℝ) := by
  rw [history_card]
  positivity

end MajorityDynamics.Universal
