import MajorityDynamics.Analysis.GaussianRegularity.Moving
import MajorityDynamics.Analysis.GaussianRegularity.Positive
import MajorityDynamics.Analysis.GaussianRegularity.IntegralLocal

/-! # Appendix E.2: joint compact regularity of Gaussian functionals -/

noncomputable section

open Set MeasureTheory

namespace MajorityDynamics.Analysis.GaussianRegularity

open ConditionalGaussian

variable {d r : ℕ}

/-- Assemble moving-threshold regularity from the fixed-region analytic result. -/
theorem regularOn_of_fixedRaw (M : Matrix (Fin r) (Fin d) ℝ) (hM : M.rank = r)
    (hfixed : FixedRawRegularity M) {P : Set (Parameters d r)} (hP : IsCompact P)
    (hv : ∀ p ∈ P, positiveVariance p) : RegularOn M P := by
  obtain ⟨hmass, hfirst, hsecond⟩ := moving_raw_regular M hM hfixed
  have hPU : P ⊆ {p | positiveVariance p} := hv
  have hlower := compact_mass_lower_bound M hM P hP hv
    (hmass.continuousOn.mono hPU)
  exact regularOn_of_locallyLipschitz M hP hPU hlower
    (fun p hp => mass_pos M hM p hp) hmass hfirst hsecond

/-- Fixed-region mass and raw first/second moments are jointly locally Lipschitz. -/
theorem fixed_raw_regular (M : Matrix (Fin r) (Fin d) ℝ) :
    FixedRawRegularity M := by
  constructor
  · exact locallyLipschitzOn_weighted_law_integral (r := r) (event M 0) (f := fun _ => 1) continuous_const ⟨1, 0, by simp⟩
  · intro t
    apply locallyLipschitzOn_weighted_law_integral (r := r) (event M 0) (f := fun x => x t) (by fun_prop)
    exact ⟨1, 1, fun x => by simpa using PiLp.norm_apply_le x t⟩
  · intro t t'
    apply locallyLipschitzOn_weighted_law_integral (r := r) (event M 0) (f := fun x => x t * x t') (by fun_prop)
    refine ⟨1, 2, fun x => ?_⟩
    calc
      ‖x t * x t'‖ = ‖x t‖ * ‖x t'‖ := norm_mul _ _
      _ ≤ ‖x‖ * ‖x‖ := mul_le_mul (PiLp.norm_apply_le x t)
        (PiLp.norm_apply_le x t') (norm_nonneg _) (norm_nonneg _)
      _ = 1 * ‖x‖ ^ 2 := by ring

/-- Lemma E.2, proved for the actual Gaussian functionals with no imported axioms. -/
theorem gaussian_regularity : GaussianRegularityTheorem := by
  intro d r M hM P hP hv
  exact regularOn_of_fixedRaw M hM (fixed_raw_regular M) hP hv

end MajorityDynamics.Analysis.GaussianRegularity
