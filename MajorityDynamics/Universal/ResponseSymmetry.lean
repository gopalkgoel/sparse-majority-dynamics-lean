import MajorityDynamics.Universal.ResponseAlgebra

/-!
# Bit-complement antisymmetry of the linear response

The probability laws are transported by the coordinate permutation before the
covariance system and the response recursion are compared. Conditioning is
therefore on the actual history and child events used by the paper.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open MajorityDynamics.Analysis

namespace MajorityDynamics.Universal

variable {k : ℕ}

theorem γ_flip_row (n : ℕ) (s : History (n + 1)) :
    γ n (flip s) = rowFlip (γ n s) := by
  ext t
  simpa only [rowFlip_apply, flip_flip] using γ_flip n s (flip t)

theorem dayLaw_map_flip (n : ℕ) (s : History (n + 1)) :
    (dayLaw n s).map rowFlip = dayLaw n (flip s) := by
  rw [dayLaw, dayLaw, γ_flip_row]
  exact rowLaw_map_flip _ (ν_positive n) (ν_flip n) _

theorem historyLaw_flip (n : ℕ) (s : History (n + 1)) :
    historyLaw n (flip s) = (historyLaw n s).map rowFlip := by
  unfold historyLaw dayLaw
  rw [history_condition_eq _ _ (ν_positive n), history_condition_eq _ _ (ν_positive n),
    γ_flip_row, ← rowLaw_map_flip _ (ν_positive n) (ν_flip n),
    condition_map_flip _ _ (historyCone_isOpen _).measurableSet,
    historyCone_preimage_flip]

theorem childLaw_flip (n : ℕ) (s : History (n + 1)) (b : Bool) :
    childLaw n (flip s) (!b) = (childLaw n s b).map rowFlip := by
  unfold childLaw dayLaw
  rw [child_condition_eq _ _ _ (ν_positive n),
    child_condition_eq _ _ _ (ν_positive n), γ_flip_row,
    ← rowLaw_map_flip _ (ν_positive n) (ν_flip n),
    condition_map_flip _ _ (childCone_isOpen _ _).measurableSet,
    childCone_preimage_flip]

/-- The centered conditional covariance transforms by simultaneous permutation. -/
theorem conditionalCovariance_flip (n : ℕ) (s t u : History (n + 1)) :
    conditionalCovariance n (flip s) (flip t) (flip u) = conditionalCovariance n s t u := by
  unfold conditionalCovariance ConditionalGaussian.covMatrix
  rw [historyLaw_flip, covariance_map]
  · simp only [Function.comp_def, rowFlip_apply, flip_flip]
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · exact rowFlip_measurable.aemeasurable

theorem responseLinear_flip (b : History k → ℝ) (x : Row k) :
    responseLinear (fun t => -b (flip t)) (rowFlip x) = -responseLinear b x := by
  simp only [responseLinear, rowFlip_apply, neg_mul, Finset.sum_neg_distrib]
  congr 1
  exact Equiv.sum_comp (flipEquiv k) (fun t => b t * x t)

theorem integral_responseLinear_flip (ρ : Measure (Row k)) (b : History k → ℝ) :
    (∫ x, responseLinear (fun t => -b (flip t)) x ∂ρ.map rowFlip) =
      -(∫ x, responseLinear b x ∂ρ) := by
  rw [integral_map rowFlip_measurable.aemeasurable
    (Measurable.aestronglyMeasurable (by unfold responseLinear; fun_prop))]
  simp only [responseLinear_flip, integral_neg]

/-- Uniqueness of the covariance system gives the transformed coefficient vector. -/
theorem betaFor_flip_eq (n : ℕ) (s : History (n + 1)) (e : History (n + 1) → ℝ)
    (he : ∀ t, e (flip t) = -e t) :
    betaFor n (flip s) e = fun t => -betaFor n s e (flip t) := by
  symm
  apply betaFor_unique
  ext u
  change (∑ t, -betaFor n s e (flip t) * conditionalCovariance n (flip s) t u) = e u
  have hc (t : History (n + 1)) :
      conditionalCovariance n (flip s) t u = conditionalCovariance n s (flip t) (flip u) := by
    simpa only [flip_flip] using conditionalCovariance_flip n s (flip t) (flip u)
  simp_rw [hc, neg_mul]
  rw [Finset.sum_neg_distrib]
  calc
    -(∑ t, betaFor n s e (flip t) * conditionalCovariance n s (flip t) (flip u)) =
        -(∑ t, betaFor n s e t * conditionalCovariance n s t (flip u)) := by
      congr 1
      exact Equiv.sum_comp (flipEquiv (n + 1))
        (fun t => betaFor n s e t * conditionalCovariance n s t (flip u))
    _ = -e (flip u) := congrArg (fun f => -f (flip u)) (betaFor_spec n s e)
    _ = e u := by rw [he, neg_neg]

theorem betaFor_flip (n : ℕ) (s t : History (n + 1)) (e : History (n + 1) → ℝ)
    (he : ∀ u, e (flip u) = -e u) :
    betaFor n (flip s) e (flip t) = -betaFor n s e t := by
  simpa only [flip_flip] using congrFun (betaFor_flip_eq n s e he) (flip t)

/-- A response update preserves antisymmetry under complementing every bit. -/
theorem responseStep_flip (n : ℕ) (e : History (n + 1) → ℝ)
    (he : ∀ t, e (flip t) = -e t) (u : History (n + 2)) :
    responseStep n e (flip u) = -responseStep n e u := by
  obtain ⟨⟨s, b⟩, rfl⟩ := (appendEquiv (n + 1)).surjective u
  change responseStep n e (flip (append s b)) = -responseStep n e (append s b)
  have hν : ν (n + 1) (append (flip s) (!b)) = ν (n + 1) (append s b) := by
    rw [← flip_append, ν_flip]
  simp only [flip_append, responseStep, parent_append, last_append, hν]
  rw [childLaw_flip, historyLaw_flip, betaFor_flip_eq n s e he,
    integral_responseLinear_flip, integral_responseLinear_flip]
  ring

/-- `lem:epsilon-symmetry`: the actual response is antisymmetric at every level. -/
theorem ε_flip (n : ℕ) (s : History (n + 1)) : ε n (flip s) = -ε n s := by
  induction n with
  | zero => simp only [ε_zero, last, bits_flip, sign_not]
  | succ n ih => exact responseStep_flip n (ε n) ih s

/-- `lem:epsilon-symmetry`: the actual regression coefficients are antisymmetric. -/
theorem β_flip (n : ℕ) (s t : History (n + 1)) :
    β n (flip s) (flip t) = -β n s t :=
  betaFor_flip n s t (ε n) (ε_flip n)

end MajorityDynamics.Universal
