import MajorityDynamics.Idealized.LinearResponse.Reference
import MajorityDynamics.Idealized.Process.SparseSolvability
noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators
namespace MajorityDynamics.Idealized.LinearResponse
open Universal Process RowLimits Binomial.Approximation
variable {n : ℕ}
theorem reference_row_data_sparse (θ T : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (n ell : ℕ) (hell : 1 ≤ ell) :
    ∃ L : ℕ, ∃ R₀ : ℝ, 0 < R₀ ∧ (∀ s t, |γ n s t| ≤ R₀) ∧ ∃ C₀ : ℝ, 0 < C₀ ∧
      ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ p : Binomial.Probability, SparseRange θ T N p →
      ∀ a : Process.Data, ∀ D : ℕ, Process.Specification N p D ell a → n + 1 < D →
      ∀ s : History (n + 1), ∃ σ : Row (n + 1),
        (∀ t, |σ t| ≤ R₀) ∧
        (∀ t, |σ t - γ n s t| ≤ C₀ * (Real.log (N : ℝ) ^ L / scale N p)) ∧
        rowTilt N p σ = a.tilt n s ∧
        Estimates N p (a.state n).sizes s σ 0 C₀ (Real.log (N : ℝ) ^ L / scale N p) := by
  obtain ⟨L, _, R₀, hR₀, hγR, C₀, hC₀, N₀, hN₀, hsolve⟩ :=
    solvable_rows_sparse θ T hθlo hθhi hT n ell hell
  refine ⟨L, R₀, hR₀, hγR, C₀, hC₀, N₀, hN₀, ?_⟩
  intro N hN p hp a D hspec hnD s
  have hn : n < D := Nat.lt_of_succ_lt hnD
  obtain ⟨σ, hσR, hσγ, hsolves, hest⟩ :=
    hsolve N hN p hp (a.state n) (hspec.symmetry n hn) (hspec.estimates n hn)
  have htilt : (fun u => rowTilt N p (σ u)) = a.tilt n :=
    (hspec.solvable n hnD).unique _ hsolves
  exact ⟨σ s, hσR s, hσγ s, congrFun htilt s, hest s⟩

end MajorityDynamics.Idealized.LinearResponse
