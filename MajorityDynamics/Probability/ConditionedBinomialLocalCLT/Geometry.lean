import MajorityDynamics.Probability.ConditionedBinomialFourier.HighFrequency
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace MajorityDynamics.Probability.ConditionedBinomialLocalCLT

namespace Geometry

def cube (d : ℕ) (R : ℝ) : Set (Fin d → ℝ) :=
  Set.Icc (fun _ => -R) (fun _ => R)

theorem mem_cube {d : ℕ} {R : ℝ} {t : Fin d → ℝ} :
    t ∈ cube d R ↔ ∀ i, |t i| ≤ R := by
  simp only [cube, Set.mem_Icc, Pi.le_def, abs_le]
  exact forall_and.symm

theorem norm_le_of_mem {d : ℕ} {R : ℝ} (hR : 0 ≤ R) {t : Fin d → ℝ}
    (ht : t ∈ cube d R) : ‖t‖ ≤ R := by
  exact (pi_norm_le_iff_of_nonneg hR).2 (fun i => by simpa [Real.norm_eq_abs] using (mem_cube.1 ht i))

theorem mem_of_norm_le {d : ℕ} {R : ℝ} {t : Fin d → ℝ}
    (ht : ‖t‖ ≤ R) : t ∈ cube d R := by
  apply mem_cube.2
  intro i
  have hi : |t i| ≤ ‖t‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm t i
  exact hi.trans ht

theorem mono {d : ℕ} {R S : ℝ} (h : R ≤ S) : cube d R ⊆ cube d S := by
  intro t ht
  exact mem_cube.2 fun i => (mem_cube.1 ht i).trans h

theorem measurableSet_cube (d : ℕ) (R : ℝ) : MeasurableSet (cube d R) :=
  measurableSet_Icc

theorem volume_lt_top (d : ℕ) (R : ℝ) : volume (cube d R) < ⊤ :=
  isCompact_Icc.measure_lt_top

theorem volume_cube (d : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    volume.real (cube d R) = (2 * R) ^ d := by
  change (volume (Set.Icc _ _)).toReal = _
  rw [Real.volume_Icc_pi_toReal]
  · simp [sub_neg_eq_add, two_mul]
  · intro i
    dsimp
    linarith

theorem fundamental_cube (d : ℕ) :
    cube d Real.pi = ConditionedBinomialFourier.HighFrequency.cube d :=
  (ConditionedBinomialFourier.HighFrequency.cube_eq_Icc d).symm

theorem partition {d N : ℕ} {p δ : ℝ}
    (_hR : 0 ≤ (N : ℝ)^δ / Real.sqrt ((N : ℝ)^2*p))
    (hπ : (N : ℝ)^δ / Real.sqrt ((N : ℝ)^2*p) ≤ Real.pi) :
    cube d ((N : ℝ)^δ / Real.sqrt ((N : ℝ)^2*p)) ∪
      ConditionedBinomialFourier.HighFrequency.region d N p δ =
      ConditionedBinomialFourier.HighFrequency.cube d := by
  ext t
  constructor
  · rintro (ht | ht)
    · rw [← fundamental_cube]
      exact mono hπ ht
    · exact ht.1
  · intro ht
    by_cases h : ‖t‖ ≤ (N : ℝ)^δ / Real.sqrt ((N : ℝ)^2*p)
    · exact Or.inl (mem_of_norm_le h)
    · exact Or.inr ⟨ht, lt_of_not_ge h⟩

theorem partition_disjoint {d N : ℕ} {p δ : ℝ}
    (hR : 0 ≤ (N : ℝ)^δ / Real.sqrt ((N : ℝ)^2*p)) :
    Disjoint (cube d ((N : ℝ)^δ / Real.sqrt ((N : ℝ)^2*p)))
      (ConditionedBinomialFourier.HighFrequency.region d N p δ) := by
  apply Set.disjoint_left.2
  intro t ht hh
  exact (not_lt_of_ge (norm_le_of_mem hR ht)) hh.2

theorem integrableOn_of_continuous {d : ℕ} {R : ℝ}
    {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) : IntegrableOn f (cube d R) :=
  hf.continuousOn.integrableOn_compact isCompact_Icc

theorem positive_integral_lower {d : ℕ} {R s a : ℝ}
    (hs : 0 ≤ s) (hsR : s ≤ R) {g : (Fin d → ℝ) → ℝ}
    (hg : Continuous g) (hg0 : ∀ t, 0 ≤ g t)
    (hsmall : ∀ t ∈ cube d s, a ≤ g t) :
    a * (2*s)^d ≤ ∫ t in cube d R, g t := by
  have hi := integrableOn_of_continuous (R := R) hg
  have his := hi.mono_set (mono hsR)
  calc
    a * (2*s)^d = ∫ _t in cube d s, a := by
      rw [setIntegral_const, volume_cube d hs]
      simp [smul_eq_mul, mul_comm]
    _ ≤ ∫ t in cube d s, g t :=
      setIntegral_mono_on (integrableOn_const (volume_lt_top d s).ne) his
        (measurableSet_cube d s) hsmall
    _ ≤ ∫ t in cube d R, g t :=
      setIntegral_mono_set hi (Filter.Eventually.of_forall fun t => hg0 t)
        (Filter.Eventually.of_forall fun _ ht => mono hsR ht)

/-- A positive comparison integral and pointwise low-frequency error give a
lower bound for the real part of the literal complete Fourier integral. -/
theorem fourier_integral_lower {d N : ℕ} {p δ s a E H : ℝ}
    (hR : 0 ≤ (N : ℝ)^δ / Real.sqrt ((N : ℝ)^2*p))
    (hπ : (N : ℝ)^δ / Real.sqrt ((N : ℝ)^2*p) ≤ Real.pi)
    (hs : 0 ≤ s) (hsR : s ≤ (N : ℝ)^δ / Real.sqrt ((N : ℝ)^2*p))
    {F : (Fin d → ℝ) → ℂ} {g : (Fin d → ℝ) → ℝ}
    (hF : IntegrableOn F (ConditionedBinomialFourier.HighFrequency.cube d))
    (hg : Continuous g) (hg0 : ∀ t, 0 ≤ g t)
    (hsmall : ∀ t ∈ cube d s, a ≤ g t)
    (herr : ∀ t ∈ cube d ((N : ℝ)^δ / Real.sqrt ((N : ℝ)^2*p)),
      ‖F t - (g t : ℂ)‖ ≤ E)
    (hhigh : ‖∫ t in ConditionedBinomialFourier.HighFrequency.region d N p δ, F t‖ ≤ H) :
    a*(2*s)^d - E*(2*((N : ℝ)^δ / Real.sqrt ((N : ℝ)^2*p)))^d - H ≤
      (∫ t in ConditionedBinomialFourier.HighFrequency.cube d, F t).re := by
  let R := (N : ℝ)^δ / Real.sqrt ((N : ℝ)^2*p)
  have hlow : cube d R ⊆ ConditionedBinomialFourier.HighFrequency.cube d := by
    rw [← fundamental_cube]
    exact mono hπ
  have hFl := hF.mono_set hlow
  have hFh : IntegrableOn F (ConditionedBinomialFourier.HighFrequency.region d N p δ) :=
    hF.mono_set (fun _ ht => ht.1)
  have hgl := integrableOn_of_continuous (R := R) hg
  have hconst : IntegrableOn (fun _ : Fin d → ℝ => E) (cube d R) :=
    integrableOn_const (volume_lt_top d R).ne
  have hreal : ∫ t in cube d R, g t - E ≤ ∫ t in cube d R, (F t).re := by
    apply setIntegral_mono_on (hgl.sub hconst) hFl.re (measurableSet_cube d R)
    intro t ht
    change g t - E ≤ (F t).re
    have hh := (Complex.abs_re_le_norm (F t - (g t : ℂ))).trans (herr t ht)
    simp only [Complex.sub_re, Complex.ofReal_re] at hh
    linarith [(abs_le.1 hh).1]
  rw [integral_sub hgl hconst, setIntegral_const, volume_cube d hR] at hreal
  simp only [smul_eq_mul] at hreal
  have hpos := positive_integral_lower hs hsR hg hg0 hsmall
  have hsplit := setIntegral_union (partition_disjoint hR)
    (ConditionedBinomialFourier.HighFrequency.measurableSet_region d N p δ) hFl hFh
  rw [partition hR hπ] at hsplit
  rw [hsplit, Complex.add_re]
  have hr := (Complex.abs_re_le_norm
    (∫ t in ConditionedBinomialFourier.HighFrequency.region d N p δ, F t)).trans hhigh
  have hre : (∫ t in cube d R, (F t).re) = (∫ t in cube d R, F t).re :=
    integral_re hFl
  rw [hre] at hreal
  dsimp [R] at hreal hpos
  nlinarith [(abs_le.1 hr).1]

end Geometry
end MajorityDynamics.Probability.ConditionedBinomialLocalCLT
