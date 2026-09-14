import MajorityDynamics.Universal.Recursion
import MajorityDynamics.Universal.GaussianSymmetry

/-! # Bit-flip symmetry of the constructed universal sequences -/

noncomputable section

open Set

namespace MajorityDynamics.Universal

variable {n : ℕ}

theorem Level.weightedRow_flip (a : Level n) (hf : a.FlipInvariant) (s : History (n + 1)) :
    a.weightedRow (flip s) = rowFlip (a.weightedRow s) := by
  ext t
  change a.ν t * a.μ (flip s) t = a.ν (flip t) * a.μ s (flip t)
  rw [hf.ν_flip]
  have hm := hf.μ_flip s (flip t)
  simpa only [flip_flip] using congrArg (fun z => a.ν t * z) hm

/-- Inverse equivariance follows from the proved forward map and its injectivity. -/
theorem Level.gamma_flip (a : Level n) (h : a.Valid) (hf : a.FlipInvariant)
    (s : History (n + 1)) : a.gamma h (flip s) = rowFlip (a.gamma h s) := by
  apply (meanBijection (flip s) a.ν h.positive).bijOn.injOn (mem_univ _) (mem_univ _)
  rw [meanBijection_toFun, a.gamma_defining h,
    meanMap_flip s a.ν h.positive hf.ν_flip, a.gamma_defining h]
  exact a.weightedRow_flip hf s

theorem Level.next_flipInvariant (a : Level n) (h : a.Valid) (hf : a.FlipInvariant) :
    (a.next h).FlipInvariant where
  ν_flip u := by
    obtain ⟨⟨s, b⟩, rfl⟩ := (appendEquiv (n + 1)).surjective u
    change (a.next h).ν (flip (append s b)) = (a.next h).ν (append s b)
    rw [flip_append, a.next_ν_append, a.next_ν_append, hf.ν_flip, a.gamma_flip h hf,
      branchProbability_flip s a.ν h.positive hf.ν_flip]
  μ_flip u v := by
    obtain ⟨⟨s, b⟩, rfl⟩ := (appendEquiv (n + 1)).surjective u
    obtain ⟨⟨t, c⟩, rfl⟩ := (appendEquiv (n + 1)).surjective v
    change (a.next h).μ (flip (append s b)) (flip (append t c)) =
      (a.next h).μ (append s b) (append t c)
    rw [flip_append, flip_append, a.next_μ_append, a.next_μ_append,
      a.gamma_flip h hf s, a.gamma_flip h hf t,
      branchMean_flip s a.ν h.positive hf.ν_flip,
      branchMean_flip t a.ν h.positive hf.ν_flip]
    simp only [rowFlip_apply, flip_flip, hf.ν_flip, hf.μ_flip]

theorem initialLevel_flipInvariant : initialLevel.FlipInvariant where
  ν_flip _ := rfl
  μ_flip _ _ := rfl

/-- `lem:universal-symmetry` for all levels of the concrete recursion. -/
theorem universal_flipInvariant (n : ℕ) : (universal n).FlipInvariant := by
  induction n with
  | zero => exact initialLevel_flipInvariant
  | succ n ih =>
    rw [universal_succ]
    exact (universal n).next_flipInvariant (universal_valid n) ih

theorem ν_flip (n : ℕ) (s : History (n + 1)) : ν n (flip s) = ν n s :=
  (universal_flipInvariant n).ν_flip s

theorem μ_flip (n : ℕ) (s t : History (n + 1)) : μ n (flip s) (flip t) = μ n s t :=
  (universal_flipInvariant n).μ_flip s t

theorem γ_flip (n : ℕ) (s t : History (n + 1)) : γ n (flip s) (flip t) = γ n s t := by
  have h := (universal n).gamma_flip (universal_valid n) (universal_flipInvariant n) s
  have ht := congrArg (fun x : Row (n + 1) => x (flip t)) h
  simpa only [γ, rowFlip_apply, flip_flip] using ht

/-- The last consequence of `lem:universal-symmetry`. -/
theorem ν_signed_sum (n : ℕ) (r : Fin (n + 1)) : ∑ t, character r t * ν n t = 0 :=
  sum_character_of_flip_invariant (ν n) (ν_flip n) r

end MajorityDynamics.Universal
