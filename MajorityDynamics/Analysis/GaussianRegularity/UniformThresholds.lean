import MajorityDynamics.Analysis.GaussianRegularity.UniformEvents
import MajorityDynamics.Analysis.GaussianRegularity.Threshold

/-! Threshold perturbation independent of the absolute threshold. Only the
threshold difference translates the mean; large terminal shifts are allowed. -/
noncomputable section
open Set MeasureTheory
namespace MajorityDynamics.Analysis.GaussianRegularity
open ConditionalGaussian

theorem threshold_mass_translate_difference {d r : ℕ}
    (M : Space d →L[ℝ] Space r) (R : Space r →L[ℝ] Space d)
    (hR : M.comp R = ContinuousLinearMap.id ℝ (Space r))
    (S : Covariance d) (m : Space d) (u v : Space r) :
    (gaussianLaw S m).real (linearThreshold M u) =
      (gaussianLaw S (m + R (u - v))).real (linearThreshold M v) := by
  have hmeas : MeasurableSet (linearThreshold M v) := by
    simp only [linearThreshold, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le measurable_const (by fun_prop)
  rw [← gaussianLaw_map_add S m (R (u - v)),
    map_measureReal_apply (by fun_prop) hmeas]
  congr 1
  ext x
  have hRu : M (R (u - v)) = u - v :=
    congrArg (fun f : Space r →L[ℝ] Space r => f (u - v)) hR
  simp only [Set.mem_preimage, linearThreshold, Set.mem_ofPred_eq, map_add,
    hRu, PiLp.add_apply, PiLp.sub_apply]
  exact forall_congr' (fun i => by constructor <;> intro hh <;> linarith)

theorem gaussian_mass_uniform_thresholds {d r : ℕ}
    (A : Matrix (Fin r) (Fin d) ℝ) (hA : A.rank = r) {M a b : ℝ}
    (hM : 0 ≤ M) (ha : 0 < a) (hb : 0 < b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m v : Space d,
      (∀ i, |m i| ≤ M) → (∀ i, a ≤ v i) → (∀ i, v i ≤ b) →
      ∀ u u' : Space r, ‖u - u'‖ ≤ 1 →
      |mass A ((m, v), u) - mass A ((m, v), u')| ≤ K * ‖u - u'‖ := by
  obtain ⟨R, hR⟩ := exists_matrix_threshold_rightInverse A hA
  obtain ⟨C, hC, hbound⟩ := gaussian_mass_uniform_events
    (d := d) (M := M + ‖R‖) (by positivity) ha hb
  refine ⟨C * ‖R‖, mul_nonneg hC (norm_nonneg _), ?_⟩
  intro m v hm hv hvb u u' hu
  have hshift : ‖R (u - u')‖ ≤ ‖R‖ :=
    (R.le_opNorm _).trans (by simpa using mul_le_mul_of_nonneg_left hu (norm_nonneg R))
  have hm' (i : Fin d) : |(m + R (u - u')) i| ≤ M + ‖R‖ := by
    exact (abs_add_le _ _).trans (add_le_add (hm i)
      ((PiLp.norm_apply_le (R (u - u')) i).trans hshift))
  have hmm (i : Fin d) : |m i| ≤ M + ‖R‖ := (hm i).trans (le_add_of_nonneg_right (norm_nonneg _))
  have hh := hbound (m + R (u - u')) v m v hm' hv hvb hmm hv hvb (event A u')
  have heq : mass A ((m, v), u) =
      (law (((m + R (u - u')), v), (0 : Space 0))).real (event A u') :=
    threshold_mass_translate_difference (rectangularCLM A) R hR _ m u u'
  change |mass A ((m, v), u) - (law ((m, v), (0 : Space 0))).real (event A u')| ≤ _
  rw [heq]
  have hnorm : ‖(m + R (u - u'), v) - (m, v)‖ = ‖R (u - u')‖ := by
    simp
  rw [hnorm] at hh
  exact hh.trans (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left (R.le_opNorm (u - u')) hC)

/-- Joint parameter control with no bound on either absolute threshold. -/
theorem gaussian_mass_unbounded_threshold_parameters {d r : ℕ}
    (A : Matrix (Fin r) (Fin d) ℝ) (hA : A.rank = r) {M a b : ℝ}
    (hM : 0 ≤ M) (ha : 0 < a) (hb : 0 < b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m v m' v' : Space d,
      (∀ i, |m i| ≤ M) → (∀ i, a ≤ v i) → (∀ i, v i ≤ b) →
      (∀ i, |m' i| ≤ M) → (∀ i, a ≤ v' i) → (∀ i, v' i ≤ b) →
      ∀ u u' : Space r, ‖u - u'‖ ≤ 1 →
      |mass A ((m, v), u) - mass A ((m', v'), u')| ≤
        K * (‖(m, v) - (m', v')‖ + ‖u - u'‖) := by
  obtain ⟨C, hC, hc⟩ := gaussian_mass_uniform_events (d := d) hM ha hb
  obtain ⟨L, hL, hl⟩ := gaussian_mass_uniform_thresholds A hA hM ha hb
  refine ⟨C + L, add_nonneg hC hL, ?_⟩
  intro m v m' v' hm hv hvb hm' hv' hvb' u u' hu
  have h1 : |mass A ((m, v), u) - mass A ((m', v'), u)| ≤
      C * ‖(m, v) - (m', v')‖ := hc m v m' v' hm hv hvb hm' hv' hvb' (event A u)
  have h2 := hl m' v' hm' hv' hvb' u u' hu
  have hh := (abs_sub_le (mass A ((m, v), u)) (mass A ((m', v'), u))
    (mass A ((m', v'), u'))).trans (add_le_add h1 h2)
  have hn1 := norm_nonneg ((m, v) - (m', v'))
  have hn2 := norm_nonneg (u - u')
  nlinarith

end MajorityDynamics.Analysis.GaussianRegularity
