import MajorityDynamics.Analysis.GaussianRegularity.IntegralDensity
import MajorityDynamics.Analysis.GaussianRegularity.Law

/-! Gaussian parameter perturbation with a constant uniform over ALL events.
This avoids introducing an upper bound on a moving terminal threshold into
the Lipschitz constant. -/
noncomputable section
open Set MeasureTheory
namespace MajorityDynamics.Analysis.GaussianRegularity
open ConditionalGaussian

theorem gaussian_mass_uniform_events {d : ℕ} {M a b : ℝ}
    (hM : 0 ≤ M) (ha : 0 < a) (hb : 0 < b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m v m' v' : Space d,
      (∀ i, |m i| ≤ M) → (∀ i, a ≤ v i) → (∀ i, v i ≤ b) →
      (∀ i, |m' i| ≤ M) → (∀ i, a ≤ v' i) → (∀ i, v' i ≤ b) →
      ∀ O : Set (Space d),
      |(law ((m, v), (0 : Space 0))).real O -
        (law ((m', v'), (0 : Space 0))).real O| ≤ K * ‖(m, v) - (m', v')‖ := by
  obtain ⟨C, c, hC, hc, hbound, hdiff⟩ := density_uniform_envelopes (d := d) hM ha hb
  let B : Space d → ℝ := fun x => 2 * d * C * Real.exp (-c * ‖x‖ ^ 2)
  have hB : Integrable B := (integrable_gaussian_envelope hc).const_mul (2 * d * C)
  have hBpos (x : Space d) : 0 ≤ B x := by dsimp [B]; positivity
  refine ⟨∫ x, B x, integral_nonneg hBpos, ?_⟩
  intro m v m' v' hm hv hvb hm' hv' hvb' O
  have hInt (m v : Space d) (hm : ∀ i, |m i| ≤ M)
      (hv : ∀ i, a ≤ v i) (hvb : ∀ i, v i ≤ b) :
      Integrable (fun x : Space d => density m v x) := by
    apply ((integrable_gaussian_envelope (d := d) hc).const_mul C).mono'
      (by unfold density scalarDensity; fun_prop)
    exact ae_of_all _ fun x => hbound m v x hm hv hvb
  have hI := hInt m v hm hv hvb
  have hI' := hInt m' v' hm' hv' hvb'
  have hmass (m v : Space d) (hv : ∀ i, a ≤ v i) :
      (law ((m, v), (0 : Space 0))).real O = ∫ x in O, density m v x := by
    have h := setIntegral_law_eq_density ((m, v), (0 : Space 0))
      (fun i => ha.trans_le (hv i)) O (fun _ => (1 : ℝ))
    simpa only [integral_const, smul_eq_mul, mul_one, Measure.real,
      Measure.restrict_apply_univ] using h
  rw [hmass m v hv, hmass m' v' hv', ← integral_sub hI.restrict hI'.restrict]
  change ‖∫ x in O, density m v x - density m' v' x‖ ≤ _
  calc
    _ ≤ ∫ x in O, B x * ‖(m, v) - (m', v')‖ :=
      norm_integral_le_of_norm_le (hB.mul_const _).restrict
        (ae_of_all _ fun x => hdiff m v m' v' x hm hv hvb hm' hv' hvb')
    _ ≤ ∫ x, B x * ‖(m, v) - (m', v')‖ :=
      setIntegral_le_integral (hB.mul_const _)
        (ae_of_all _ fun x => mul_nonneg (hBpos x) (norm_nonneg _))
    _ = _ := integral_mul_const _ _

end MajorityDynamics.Analysis.GaussianRegularity
