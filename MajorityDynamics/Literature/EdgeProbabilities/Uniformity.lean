import MajorityDynamics.Literature.EdgeProbabilities.Basic
import Mathlib.Topology.Order.MonotoneConvergence

/-! Sequence uniformity: derive a finite uniform O bound without assuming a universal source constant. -/
noncomputable section
open Filter
open scoped Topology
namespace MajorityDynamics.Literature.EdgeProbabilities

/-- A bound holding eventually along every admissible size-diverging sequence has uniform
finite constants. The source constant may depend on the sequence. The contradiction sequence
chooses a single bad datum with size at least `j` and requested constant `j+1`; no finite maxima
or arbitrary filler data are used. -/
theorem uniform_bound_of_sequence_bound {X : Type*}
    (size : X → ℕ) (Valid : X → Prop) (error scale : X → ℝ)
    (hscale : ∀ x, Valid x → 0 ≤ scale x)
    (hsequence : ∀ x : ℕ → X, (∀ j, Valid (x j)) →
      Tendsto (fun j => size (x j)) atTop atTop →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ j in atTop, error (x j) ≤ C * scale (x j)) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
      ∀ x, N₀ ≤ size x → Valid x → error x ≤ C * scale x := by
  classical
  by_contra h
  push Not at h
  have hbad (j : ℕ) : ∃ x, j ≤ size x ∧ Valid x ∧
      ((j : ℝ) + 1) * scale x < error x := by
    simpa only [not_le] using h ((j : ℝ) + 1) (by positivity) j
  choose x hxsize hxvalid hxerror using hbad
  have hdiverge : Tendsto (fun j => size (x j)) atTop atTop :=
    tendsto_atTop_mono hxsize tendsto_id
  obtain ⟨C, _, hC⟩ := hsequence x hxvalid hdiverge
  obtain ⟨J, hJ⟩ := exists_nat_gt C
  obtain ⟨j, hj, hjC⟩ := (hC.and (eventually_ge_atTop J)).exists
  have hCj : C ≤ (j : ℝ) + 1 := by
    have : (J : ℝ) ≤ j := by exact_mod_cast hjC
    linarith
  have := mul_le_mul_of_nonneg_right hCj (hscale (x j) (hxvalid j))
  linarith [hxerror j]

end MajorityDynamics.Literature.EdgeProbabilities
