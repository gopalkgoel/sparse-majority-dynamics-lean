import MajorityDynamics.Idealized.LinearResponse.Basic
import MajorityDynamics.Idealized.Process.OneStep

/-! The reference row of the Theorem 5.2 process: E.3 at the solved tilt. -/

noncomputable section
open scoped BigOperators

namespace MajorityDynamics.Idealized.LinearResponse

open MajorityDynamics.Universal
open MajorityDynamics.Idealized.RowLimits
open MajorityDynamics.Idealized.Process
open MajorityDynamics.Binomial.Approximation (Density scale)

/-- Uniformly for the actual reference process, every row tilt is the logit
tilt of a bounded Gaussian parameter close to `γ`, with all E.3 estimates at
error `log^L N / √(pN)`. This is Theorem 5.2's solvability step, exported. -/
theorem reference_row_data (θ T : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (n ell : ℕ) (hell : 1 ≤ ell) :
    ∃ L : ℕ, ∃ R₀ : ℝ, 0 < R₀ ∧ (∀ s t, |γ n s t| ≤ R₀) ∧ ∃ C₀ : ℝ, 0 < C₀ ∧
      ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ p : Binomial.Probability, Density θ T N p →
      ∀ a : Process.Data, ∀ D : ℕ, Process.Specification N p D ell a → n + 1 < D →
      ∀ s : History (n + 1), ∃ σ : Row (n + 1),
        (∀ t, |σ t| ≤ R₀) ∧
        (∀ t, |σ t - γ n s t| ≤ C₀ * (Real.log (N : ℝ) ^ L / scale N p)) ∧
        rowTilt N p σ = a.tilt n s ∧
        Estimates N p (a.state n).sizes s σ 0 C₀ (Real.log (N : ℝ) ^ L / scale N p) := by
  obtain ⟨L, _, R₀, hR₀, hγR, C₀, hC₀, N₀, hN₀, hsolve⟩ :=
    solvable_rows θ T hθlo hθhi hT n ell hell
  refine ⟨L, R₀, hR₀, hγR, C₀, hC₀, N₀, hN₀, ?_⟩
  intro N hN p hp a D hspec hnD s
  have hn : n < D := Nat.lt_of_succ_lt hnD
  obtain ⟨σ, hσR, hσγ, hsolves, hest⟩ :=
    hsolve N hN p hp (a.state n) (hspec.symmetry n hn) (hspec.estimates n hn)
  have htilt : (fun u => rowTilt N p (σ u)) = a.tilt n :=
    (hspec.solvable n hnD).unique _ hsolves
  exact ⟨σ s, hσR s, hσγ s, congrFun htilt s, hest s⟩

end MajorityDynamics.Idealized.LinearResponse
