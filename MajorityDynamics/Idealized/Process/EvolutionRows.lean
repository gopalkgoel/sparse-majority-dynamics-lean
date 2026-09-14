import MajorityDynamics.Idealized.Process.EvolutionGaussian
import MajorityDynamics.Idealized.Process.EvolutionAlgebra

/-! The two row asymptotics that drive the actual local template. -/

noncomputable section
open scoped BigOperators

namespace MajorityDynamics.Idealized.Process
open Universal Local RowLimits
variable {n : ℕ}

structure RowAsymptotics (N : ℕ) (p : Binomial.Probability)
    (sizes : Local.Sizes n) (q : Local.Tilt n) (ε : ℝ) : Prop where
  split : ∀ s b,
    |splitProbability sizes q s b - branchProbability s (ν n) (γ n s) b| ≤ ε
  child_mean : ∀ s b t,
    |(childMean sizes q s b t - (p : ℝ) * sizes t) / Real.sqrt ((p : ℝ) * N) -
      branchMean s (ν n) (γ n s) b t| ≤ ε

/-- E.3 at the solved tilts, followed by E.2 in the mean parameter, gives the
row estimates with the exact universal coefficients used by the recursion. -/
theorem row_asymptotics_of_estimates (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (N : ℕ) (p : Binomial.Probability) (sizes : Local.Sizes n)
      (σ : History (n + 1) → Row (n + 1)) (C K ρ : ℝ),
      0 ≤ K → 0 ≤ ρ →
      (∀ s t, |σ s t| ≤ R) → (∀ s t, |γ n s t| ≤ R) →
      (∀ s t, |σ s t - γ n s t| ≤ K * ρ) →
      (∀ s, Estimates N p sizes s (σ s) 0 C ρ) →
      RowAsymptotics N p sizes (fun s => rowTilt N p (σ s)) ((C + A * K) * ρ) := by
  obtain ⟨A, hA, hLip⟩ := gaussian_branch_lipschitz n R hR
  refine ⟨A, hA, ?_⟩
  intro N p sizes σ C K ρ hK hρ hσ hγ hclose hest
  have he := fun s => hLip s (σ s) (γ n s) (hσ s) (hγ s) (K * ρ)
    (mul_nonneg hK hρ) (hclose s)
  constructor
  · intro s b
    have hp := (hest s).split_probability b
    rw [shiftedChildEvent_zero, gaussian_branch_probability] at hp
    change |binomialSplit N p sizes s b (σ s) - branchProbability s (ν n) (γ n s) b| ≤ _
    exact (abs_sub_le _ (branchProbability s (ν n) (σ s) b) _).trans
      ((add_le_add hp ((he s).1 b)).trans_eq (by ring))
  · intro s b t
    have hm := (hest s).child_mean b t
    rw [shiftedChildEvent_zero, gaussianMean_child_eq_branchMean] at hm
    rw [childMean_eq_binomialMean]
    exact (abs_sub_le _ (branchMean s (ν n) (σ s) b t) _).trans
      ((add_le_add hm ((he s).2 b t)).trans_eq (by ring))

end MajorityDynamics.Idealized.Process
