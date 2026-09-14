import MajorityDynamics.Idealized.Process.EvolutionRows
import MajorityDynamics.Idealized.RowLimits.Geometry

/-! Uniform constants and size bounds for the quantitative idealized step. -/

noncomputable section
open Filter Topology
open scoped BigOperators

namespace MajorityDynamics.Idealized.Process
open Universal Local RowLimits Binomial.Approximation
variable {n : ℕ}

theorem finite_absolute_bound {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ i, |f i| ≤ B := by
  classical
  refine ⟨1 + ∑ i, |f i|, le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => abs_nonneg _)), ?_⟩
  intro i
  exact (Finset.single_le_sum (f := fun i => |f i|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ i)).trans (by linarith)

/-- Fixed finite universal coefficients have one common bound, which is
chosen before the density, sizes, edges, and tilt data vary. -/
theorem universal_evolution_bounds (n : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧
      (∀ t, 1 / ν n t ≤ B) ∧ (∀ u, 1 / ν (n + 1) u ≤ B) ∧
      (∀ s t, |μ n s t| ≤ B) ∧ (∀ u v, |μ (n + 1) u v| ≤ B) ∧
      ∀ s b t, |branchMean s (ν n) (γ n s) b t| ≤ B := by
  obtain ⟨B₁, hB₁, h₁⟩ := finite_absolute_bound (fun t : History (n + 1) => 1 / ν n t)
  obtain ⟨B₂, hB₂, h₂⟩ := finite_absolute_bound (fun t : History (n + 2) => 1 / ν (n + 1) t)
  obtain ⟨B₃, hB₃, h₃⟩ := finite_absolute_bound
    (fun st : History (n + 1) × History (n + 1) => μ n st.1 st.2)
  obtain ⟨B₄, hB₄, h₄⟩ := finite_absolute_bound
    (fun uv : History (n + 2) × History (n + 2) => μ (n + 1) uv.1 uv.2)
  obtain ⟨B₅, hB₅, h₅⟩ := finite_absolute_bound
    (fun sbt : History (n + 1) × Bool × History (n + 1) =>
      branchMean sbt.1 (ν n) (γ n sbt.1) sbt.2.1 sbt.2.2)
  refine ⟨B₁ + B₂ + B₃ + B₄ + B₅, by linarith, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    exact (le_abs_self _).trans ((h₁ t).trans (by linarith))
  · intro t
    exact (le_abs_self _).trans ((h₂ t).trans (by linarith))
  · intro s t
    exact (h₃ (s, t)).trans (by linarith)
  · intro u v
    exact (h₄ (u, v)).trans (by linarith)
  · intro s b t
    exact (h₅ (s, b, t)).trans (by linarith)

theorem universal_size_le_one (n : ℕ) (s : History (n + 1)) : ν n s ≤ 1 := by
  rw [← ν_total n]
  exact Finset.single_le_sum (f := ν n) (fun t _ => (ν_positive n t).le) (Finset.mem_univ s)

theorem universal_branch_le_one (s : History (n + 1)) (b : Bool) :
    |branchProbability s (ν n) (γ n s) b| ≤ 1 := by
  have hb₀ := branchProbability_pos s (ν n) (ν_positive n) (γ n s) false
  have hb₁ := branchProbability_pos s (ν n) (ν_positive n) (γ n s) true
  have hsum := branchProbability_add s (ν n) (ν_positive n) (γ n s)
  rw [abs_of_pos (branchProbability_pos s (ν n) (ν_positive n) (γ n s) b)]
  cases b <;> linarith

theorem universal_size_recursion (u : History (n + 2)) :
    ν (n + 1) u = ν n (parent u) *
      branchProbability (parent u) (ν n) (γ n (parent u)) (last u) := by
  simpa only [append_parent_last] using ν_recursion n (parent u) (last u)

theorem universal_edge_recursion (u v : History (n + 2)) :
    μ (n + 1) u v =
      branchMean (parent u) (ν n) (γ n (parent u)) (last u) (parent v) / ν n (parent v) +
      branchMean (parent v) (ν n) (γ n (parent v)) (last v) (parent u) / ν n (parent u) -
      μ n (parent u) (parent v) := by
  simpa only [append_parent_last] using μ_recursion n (parent u) (parent v) (last u) (last v)

theorem next_sizes_quantitative (N : ℕ) (p : Binomial.Probability)
    (x : State n) (q : Local.Tilt n) (ρ K : ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hK : 0 ≤ K) (hround : 1 ≤ (N : ℝ) * ρ)
    (hsize : ∀ s, |(x.sizes s : ℝ) - N * ν n s| ≤ N * ρ)
    (hrow : RowAsymptotics N p x.sizes q (K * ρ)) :
    ∀ u, |((nextState x q).sizes u : ℝ) - N * ν (n + 1) u| ≤
      (2 * K + 2) * N * ρ := by
  intro u
  have hsz : (x.sizes (parent u) : ℝ) ≤ 2 * N := by
    have hh := (abs_le.mp (hsize (parent u))).2
    have hv := universal_size_le_one n (parent u)
    nlinarith [mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg (α := ℝ) N),
      mul_le_mul_of_nonneg_left hρ1 (Nat.cast_nonneg (α := ℝ) N)]
  have hloc := split_size_error (Nat.cast_nonneg (α := ℝ) N) (Nat.cast_nonneg _) hsz hρ hK
    (universal_branch_le_one (parent u) (last u)) (hsize (parent u))
    (hrow.split (parent u) (last u))
  rw [← universal_size_recursion u] at hloc
  change |templateSizes x.sizes q u - (N : ℝ) * ν (n + 1) u| ≤ _ at hloc
  have hf := floor_size_error (templateSizes_nonneg x.sizes q u) hloc
  change |(⌊templateSizes x.sizes q u⌋₊ : ℝ) - _| ≤ _
  exact hf.trans (by nlinarith)

end MajorityDynamics.Idealized.Process
