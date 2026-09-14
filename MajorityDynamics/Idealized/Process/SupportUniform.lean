import MajorityDynamics.Idealized.Process.Support
import MajorityDynamics.Idealized.Process.TargetBounds

/-! Uniform eventual full affine support for the actual approximate states. -/

noncomputable section
open Filter Topology

namespace MajorityDynamics.Idealized.Process
open Universal Binomial Binomial.Approximation
variable {n : ℕ}

/-- Any fixed coordinate lower bound holds uniformly for all approximately
universal states. No symmetry or balance hypothesis is needed. -/
theorem eventually_level_sizes_ge (θ T : ℝ) (ell K : ℕ)
    (hθ : θ < 1) (hT : 0 < T) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Probability, Density θ T N p →
      ∀ x : State n, LevelEstimates N p ell x → ∀ t, K ≤ x.sizes t := by
  have hlarge : ∀ᶠ N : ℕ in atTop, ∀ t : History (n + 1),
      2 * (K : ℝ) / ν n t ≤ (N : ℝ) :=
    Filter.eventually_all.mpr fun t =>
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
        (eventually_ge_atTop (2 * (K : ℝ) / ν n t))
  filter_upwards [eventually_level_sizes (n := n) θ T ell hθ hT, hlarge]
    with N hsize hlarge
  intro p hp x hx t
  have hlo := (hsize.2 p hp x hx t).2.1
  have hv := ν_positive n t
  have hn := (div_le_iff₀ hv).mp (hlarge t)
  have hK : (K : ℝ) ≤ x.sizes t := by linarith
  exact_mod_cast hK

/-- The hypothesis used by every support/uniqueness endpoint holds beyond one
threshold, chosen before the density and the varying approximate state. -/
theorem eventually_support_sizes (θ T : ℝ) (ell : ℕ)
    (hθ : θ < 1) (hT : 0 < T) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Probability, Density θ T N p →
      ∀ x : State n, LevelEstimates N p ell x → ∀ t, 2 * n + 5 ≤ x.sizes t :=
  eventually_level_sizes_ge θ T ell (2 * n + 5) hθ hT

theorem eventually_fullAffineSupport (θ T : ℝ) (ell : ℕ)
    (hθ : θ < 1) (hT : 0 < T) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Probability, Density θ T N p →
      ∀ x : State n, LevelEstimates N p ell x →
        (∀ s, Analysis.FiniteTilt.FullAffineSupport
          (Local.historySupport x.sizes s) Binomial.vector) ∧
        ∀ s b, Analysis.FiniteTilt.FullAffineSupport
          (Local.childSupport x.sizes s b) Binomial.vector := by
  filter_upwards [eventually_support_sizes (n := n) θ T ell hθ hT] with N hN
  intro p hp x hx
  have hsize := hN p hp x hx
  exact ⟨historySupport_fullAffineSupport x.sizes hsize,
    childSupport_fullAffineSupport x.sizes hsize⟩

end MajorityDynamics.Idealized.Process
