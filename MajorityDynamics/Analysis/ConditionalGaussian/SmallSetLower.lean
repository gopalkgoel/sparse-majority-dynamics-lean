import MajorityDynamics.Analysis.ConditionalGaussian.GaussianDensity
import MajorityDynamics.Analysis.ConditionalGaussian.Partition

/-! Polynomial lower bounds for small Gaussian sets. Shrinking in all ambient
dimensions loses the sharp linear slab rate, but is sufficient for an
inverse-logarithmic stopping threshold at a fixed history depth. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal Pointwise
namespace MajorityDynamics.Analysis.ConditionalGaussian

variable {d : ℕ}

theorem gaussianLaw_compact_density_lower (S : Covariance d) (hS : S.PosDef)
    (m : Space d) (K : Set (Space d)) (hK : IsCompact K) :
    ∃ c : ℝ, 0 < c ∧ ∀ A : Set (Space d), MeasurableSet A → A ⊆ K →
      c * volume.real A ≤ (gaussianLaw S m).real A := by
  obtain ⟨q, hq, hformula⟩ := gaussianDensityFormula S hS
  let f : Space d → ℝ := fun x => q * weight S 0 (x - m)
  have hf : Continuous f := continuous_const.mul
    ((continuous_weight S 0).comp (continuous_id.sub continuous_const))
  have hfpos (x : Space d) : 0 < f x := mul_pos hq (weight_pos S 0 _)
  by_cases hne : K.Nonempty
  · obtain ⟨z, _, hz⟩ := hK.exists_isMinOn hne hf.continuousOn
    refine ⟨f z, hfpos z, ?_⟩
    intro A hA hAK
    have hbound : ENNReal.ofReal (f z) * volume A ≤ gaussianLaw S m A := by
      rw [hformula m, withDensity_apply _ hA]
      calc
        _ = ∫⁻ _x in A, ENNReal.ofReal (f z) ∂volume := by simp
        _ ≤ _ := setLIntegral_mono' hA fun x hx => ENNReal.ofReal_le_ofReal (hz (hAK hx))
    have hreal := ENNReal.toReal_mono (measure_ne_top (gaussianLaw S m) A) hbound
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hfpos z).le,
      Measure.real] using hreal
  · refine ⟨1, by norm_num, ?_⟩
    intro A _ hAK
    have hA : A = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x hx => hne ⟨x, hAK hx⟩
    simp [hA]

theorem gaussianLaw_small_ball_lower (S : Covariance d) (hS : S.PosDef)
    (m x : Space d) {r : ℝ} (hr : 0 < r) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : ℝ, 0 < u → u ≤ 1 →
      c * u ^ d ≤ (gaussianLaw S m).real (u • Metric.ball x r) := by
  let R : ℝ := ‖x‖ + r
  obtain ⟨q, hq, hbound⟩ := gaussianLaw_compact_density_lower S hS m
    (Metric.closedBall 0 R) (isCompact_closedBall _ _)
  have hv : 0 < volume.real (Metric.ball x r) := by
    apply ENNReal.toReal_pos
    · exact (Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr hr)).ne'
    · exact ne_top_of_le_ne_top (isCompact_closedBall x r).measure_ne_top
        (measure_mono Metric.ball_subset_closedBall)
  refine ⟨q * volume.real (Metric.ball x r), mul_pos hq hv, ?_⟩
  intro u hu hu1
  have hsub : u • Metric.ball x r ⊆ Metric.closedBall (0 : Space d) R := by
    rintro y ⟨z, hz, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hu]
    have hzbound : ‖z‖ ≤ R := by
      exact norm_le_norm_add_const_of_dist_le (Metric.mem_ball.mp hz).le
    exact (mul_le_mul_of_nonneg_right hu1 (norm_nonneg z)).trans (by simpa using hzbound)
  have hmeas : MeasurableSet (u • Metric.ball x r) := by
    exact (Metric.isOpen_ball.smul₀ hu.ne').measurableSet
  have h := hbound _ hmeas hsub
  have hvol : volume.real (u • Metric.ball x r) = u ^ d * volume.real (Metric.ball x r) := by
    simp [Measure.real, Measure.addHaar_smul_of_nonneg volume hu.le,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hu.le d)]
  rw [hvol] at h
  convert h using 1
  ring

/-- Compressing only selected directions pays the determinant, not an ambient
dimension power. The density floor is uniform even as the map becomes singular. -/
theorem gaussianLaw_compressed_ball_lower (S : Covariance d) (hS : S.PosDef)
    (m x : Space d) {r : ℝ} (hr : 0 < r) (P : Space d →L[ℝ] Space d) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : ℝ, 0 < u → u ≤ 1 →
      let L := ContinuousLinearMap.id ℝ (Space d) + (u - 1) • P
      c * |LinearMap.det L.toLinearMap| ≤ (gaussianLaw S m).real (L '' Metric.ball x r) := by
  let R : ℝ := (1 + ‖P‖) * (‖x‖ + r)
  obtain ⟨q, hq, hbound⟩ := gaussianLaw_compact_density_lower S hS m
    (Metric.closedBall 0 R) (isCompact_closedBall _ _)
  have hv : 0 < volume.real (Metric.ball x r) := by
    apply ENNReal.toReal_pos
    · exact (Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr hr)).ne'
    · exact ne_top_of_le_ne_top (isCompact_closedBall x r).measure_ne_top
        (measure_mono Metric.ball_subset_closedBall)
  refine ⟨q * volume.real (Metric.ball x r), mul_pos hq hv, ?_⟩
  intro u hu hu1 L
  by_cases hdet : LinearMap.det L.toLinearMap = 0
  · simp only [hdet, abs_zero, mul_zero]
    exact measureReal_nonneg
  have hsub : L '' Metric.ball x r ⊆ Metric.closedBall (0 : Space d) R := by
    rintro y ⟨z, hz, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have hzbound : ‖z‖ ≤ ‖x‖ + r :=
      norm_le_norm_add_const_of_dist_le (Metric.mem_ball.mp hz).le
    have huabs : |u - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    calc
      ‖L z‖ ≤ ‖z‖ + ‖(u - 1) • P z‖ := norm_add_le _ _
      _ = ‖z‖ + |u - 1| * ‖P z‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖z‖ + 1 * (‖P‖ * ‖z‖) := by
        gcongr
        exact P.le_opNorm z
      _ = (1 + ‖P‖) * ‖z‖ := by ring
      _ ≤ R := mul_le_mul_of_nonneg_left hzbound (by positivity)
  let e := (L.toLinearMap.equivOfDetNeZero hdet).toContinuousLinearEquiv
  have hmeas : MeasurableSet (L '' Metric.ball x r) :=
    (e.toHomeomorph.isOpenMap _ Metric.isOpen_ball).measurableSet
  have h := hbound _ hmeas hsub
  have hvol : volume.real (L '' Metric.ball x r) =
      |LinearMap.det L.toLinearMap| * volume.real (Metric.ball x r) := by
    simp [Measure.real, Measure.addHaar_image_continuousLinearMap,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
  rw [hvol] at h
  convert h using 1
  ring

end MajorityDynamics.Analysis.ConditionalGaussian
