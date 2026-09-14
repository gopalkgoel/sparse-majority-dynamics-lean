import MajorityDynamics.Probability.ConditionedBinomialFourier.Characteristic

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace MajorityDynamics.Probability.ConditionedBinomialLocalCLT
open ConditionedBinomialFourier
variable {d : ℕ}

def centeredProjection (ρ : Measure (Fin d → ℕ)) (t : Fin d → ℝ)
    (x : Fin d → ℕ) : ℝ := dot t ((fun i => (x i : ℝ)) - mean ρ)

def varianceForm (ρ : Measure (Fin d → ℕ)) (t : Fin d → ℝ) : ℝ :=
  ∫ x, centeredProjection ρ t x ^ 2 ∂ρ

def thirdMoment (ρ : Measure (Fin d → ℕ)) (t : Fin d → ℝ) : ℝ :=
  ∫ x, |centeredProjection ρ t x| ^ 3 ∂ρ

def taylorConstant : ℝ := Real.exp 1 + 4

theorem taylorConstant_pos : 0 < taylorConstant := by
  unfold taylorConstant
  positivity

theorem imaginary_exp_cubic (u : ℝ) :
    ‖Complex.exp (Complex.I * (u : ℂ)) - (1 + Complex.I * (u : ℂ) - (u : ℂ)^2/2)‖
      ≤ taylorConstant * |u|^3 := by
  have hn : ‖Complex.I * (u : ℂ)‖ = |u| := by simp
  by_cases hu : |u| ≤ 1
  · have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (Complex.I * (u : ℂ)) 3
    have he : Real.exp |u| ≤ Real.exp 1 := Real.exp_le_exp.mpr hu
    have hp : (∑ m ∈ Finset.range 3, (Complex.I * (u : ℂ)) ^ m / (m.factorial : ℂ)) =
        1 + Complex.I * (u : ℂ) - (u : ℂ)^2/2 := by
      norm_num [Finset.sum_range_succ]
      ring_nf
      simp [Complex.I_sq]
      ring
    rw [hp, hn] at h
    calc
      _ ≤ |u|^3 * Real.exp |u| := h
      _ ≤ |u|^3 * Real.exp 1 := mul_le_mul_of_nonneg_left he (by positivity)
      _ ≤ taylorConstant * |u|^3 := by unfold taylorConstant; nlinarith [pow_nonneg (abs_nonneg u) 3]
  · have hu1 : 1 ≤ |u| := le_of_lt (lt_of_not_ge hu)
    have he : ‖Complex.exp (Complex.I * (u : ℂ))‖ = 1 := by simp [Complex.norm_exp]
    have hp : ‖(1 + Complex.I * (u : ℂ) - (u : ℂ)^2/2 : ℂ)‖ ≤ 1 + |u| + |u|^2/2 := by
      calc
        _ ≤ ‖(1 + Complex.I * (u : ℂ) : ℂ)‖ + ‖((u : ℂ)^2/2 : ℂ)‖ := norm_sub_le _ _
        _ ≤ (‖(1 : ℂ)‖ + ‖Complex.I * (u : ℂ)‖) + ‖((u : ℂ)^2/2 : ℂ)‖ := by gcongr; exact norm_add_le _ _
        _ = _ := by simp [norm_pow]
    have h := (norm_sub_le (Complex.exp (Complex.I * (u : ℂ))) _).trans (add_le_add (le_of_eq he) hp)
    have h2 : |u| ≤ |u|^2 := by nlinarith
    have h3 : |u|^2 ≤ |u|^3 := by nlinarith [sq_nonneg (|u|-1), mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu1), sq_abs u]
    have hc : 0 < Real.exp 1 := Real.exp_pos 1
    unfold taylorConstant
    nlinarith [mul_nonneg hc.le (pow_nonneg (abs_nonneg u) 3)]

theorem negative_exp_quadratic {s : ℝ} (hs : 0 ≤ s) :
    |Real.exp (-s) - (1-s)| ≤ 4*s^2 := by
  by_cases hsmall : s ≤ 1
  · have h := Real.norm_exp_sub_one_sub_id_le (x := -s) (by simpa [Real.norm_eq_abs, abs_of_nonneg hs] using hsmall)
    have he : Real.exp (-s) - 1 - -s = Real.exp (-s) - (1-s) := by ring
    rw [he, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, abs_of_nonneg hs] at h
    nlinarith [sq_nonneg s]
  · have hlarge : 1 ≤ s := le_of_lt (lt_of_not_ge hsmall)
    have he0 := (Real.exp_pos (-s)).le
    have he1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (s-1)]

theorem norm_pow_sub_pow_le (z w : ℂ) (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) (m : ℕ) :
    ‖z^m-w^m‖ ≤ (m:ℝ)*‖z-w‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have he : z^(m+1)-w^(m+1) = z*(z^m-w^m)+(z-w)*w^m := by ring
    rw [he]
    calc
      _ ≤ ‖z*(z^m-w^m)‖ + ‖(z-w)*w^m‖ := norm_add_le _ _
      _ = ‖z‖*‖z^m-w^m‖ + ‖z-w‖*‖w‖^m := by simp [norm_pow]
      _ ≤ 1*((m:ℝ)*‖z-w‖) + ‖z-w‖*1 := by
        gcongr
        exact pow_le_one₀ (norm_nonneg _) hw
      _ = ((m+1:ℕ):ℝ)*‖z-w‖ := by push_cast; ring


def centeredOneChi (ρ : Measure (Fin d → ℕ)) (t : Fin d → ℝ) : ℂ :=
  ∫ x, Complex.exp (Complex.I * (centeredProjection ρ t x : ℂ)) ∂ρ

theorem centeredPhase_integrable (ρ : Measure (Fin d → ℕ)) [IsFiniteMeasure ρ]
    (t : Fin d → ℝ) :
    Integrable (fun x => Complex.exp (Complex.I * (centeredProjection ρ t x : ℂ))) ρ := by
  refine (integrable_const (1 : ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x => by simp [Complex.norm_exp]

theorem centeredOneChi_norm_le (ρ : Measure (Fin d → ℕ)) [IsProbabilityMeasure ρ]
    (t : Fin d → ℝ) : ‖centeredOneChi ρ t‖ ≤ 1 := by
  simpa [centeredOneChi] using (norm_integral_le_of_norm_le_const (μ := ρ)
    (f := fun x => Complex.exp (Complex.I * (centeredProjection ρ t x : ℂ))))
    (Filter.Eventually.of_forall fun x => (show ‖Complex.exp (Complex.I * (centeredProjection ρ t x : ℂ))‖ ≤ 1 by simp [Complex.norm_exp]))

theorem varianceForm_nonneg (ρ : Measure (Fin d → ℕ)) (t : Fin d → ℝ) :
    0 ≤ varianceForm ρ t := integral_nonneg fun _ => sq_nonneg _

theorem thirdMoment_nonneg (ρ : Measure (Fin d → ℕ)) (t : Fin d → ℝ) :
    0 ≤ thirdMoment ρ t := integral_nonneg fun _ => by positivity

theorem centeredOneChi_quadratic (ρ : Measure (Fin d → ℕ)) [IsProbabilityMeasure ρ]
    (t : Fin d → ℝ)
    (hfirst : Integrable (centeredProjection ρ t) ρ)
    (hsecond : Integrable (fun x => centeredProjection ρ t x ^ 2) ρ)
    (hthird : Integrable (fun x => |centeredProjection ρ t x| ^ 3) ρ)
    (hzero : ∫ x, centeredProjection ρ t x ∂ρ = 0) :
    ‖centeredOneChi ρ t - (1-(varianceForm ρ t : ℂ)/2)‖ ≤
      taylorConstant * thirdMoment ρ t := by
  let U := centeredProjection ρ t
  let P : (Fin d → ℕ) → ℂ := fun x => 1 + Complex.I * (U x : ℂ) - (U x : ℂ)^2/2
  have hU : Integrable (fun x => (U x : ℂ)) ρ := hfirst.ofReal
  have hU2 : Integrable (fun x => (U x : ℂ)^2) ρ := by
    convert (hsecond.ofReal : Integrable (fun x => ((centeredProjection ρ t x ^2 : ℝ) : ℂ)) ρ) using 1; simp [U]
  have hP : Integrable P ρ := ((integrable_const _).add (hU.const_mul _)).sub (hU2.div_const _)
  have hPI : ∫ x, P x ∂ρ = 1-(varianceForm ρ t : ℂ)/2 := by
    dsimp [P]
    rw [integral_sub (f := fun x => (1 : ℂ) + Complex.I * (U x : ℂ)) (g := fun x => (U x : ℂ)^2/2)
      ((integrable_const (1 : ℂ)).add (hU.const_mul Complex.I)) (hU2.div_const (2 : ℂ)),
      integral_add (integrable_const (1 : ℂ)) (hU.const_mul Complex.I), integral_const_mul, integral_div]
    simp only [integral_const, probReal_univ, one_smul, integral_complex_ofReal, U, hzero,
      Complex.ofReal_zero, mul_zero, add_zero]
    rw [show (fun x => (centeredProjection ρ t x : ℂ)^2) =
        (fun x => ((centeredProjection ρ t x^2 : ℝ) : ℂ)) by ext; simp,
      integral_complex_ofReal]
    rfl
  have hi := (centeredPhase_integrable ρ t).sub hP
  calc
    _ = ‖∫ x, Complex.exp (Complex.I * (U x : ℂ)) - P x ∂ρ‖ := by
      rw [integral_sub (centeredPhase_integrable ρ t) hP, hPI]
      rfl
    _ ≤ ∫ x, ‖Complex.exp (Complex.I * (U x : ℂ)) - P x‖ ∂ρ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, taylorConstant * |U x|^3 ∂ρ :=
      integral_mono hi.norm (hthird.const_mul _) (fun x => imaginary_exp_cubic (U x))
    _ = _ := by rw [integral_const_mul]; rfl

theorem centeredOneChi_gaussian (ρ : Measure (Fin d → ℕ)) [IsProbabilityMeasure ρ]
    (t : Fin d → ℝ)
    (hfirst : Integrable (centeredProjection ρ t) ρ)
    (hsecond : Integrable (fun x => centeredProjection ρ t x ^ 2) ρ)
    (hthird : Integrable (fun x => |centeredProjection ρ t x| ^ 3) ρ)
    (hzero : ∫ x, centeredProjection ρ t x ∂ρ = 0) :
    ‖centeredOneChi ρ t - (Real.exp (-(varianceForm ρ t)/2) : ℂ)‖ ≤
      taylorConstant * thirdMoment ρ t + varianceForm ρ t ^ 2 := by
  have hq := varianceForm_nonneg ρ t
  have hs := negative_exp_quadratic (s := varianceForm ρ t / 2) (by positivity)
  have hp : ‖(1-(varianceForm ρ t : ℂ)/2) - (Real.exp (-(varianceForm ρ t)/2) : ℂ)‖
      ≤ varianceForm ρ t ^2 := by
    have he : (1-(varianceForm ρ t : ℂ)/2) - (Real.exp (-(varianceForm ρ t)/2) : ℂ) =
        ((1-varianceForm ρ t/2-Real.exp (-(varianceForm ρ t)/2) : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    rw [← neg_div] at hs
    nlinarith
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add (centeredOneChi_quadratic ρ t hfirst hsecond hthird hzero) hp)

theorem centeredOneChi_eq (ρ : Measure (Fin d → ℕ)) [IsProbabilityMeasure ρ]
    (t : Fin d → ℝ) : centeredOneChi ρ t = phase t (-mean ρ) * chi ρ t := by
  change (∫ x, phase t ((fun i => (x i : ℝ)) - mean ρ) ∂ρ) = _
  simp_rw [phase_sub]
  rw [integral_const_mul]
  rfl

theorem centeredChi_eq_pow (ρ : Measure (Fin d → ℕ)) [IsProbabilityMeasure ρ]
    (m : ℕ) (t : Fin d → ℝ) : centeredChi ρ m t = centeredOneChi ρ t ^m := by
  rw [centeredChi_eq_phase_mul_pow, centeredOneChi_eq, mul_pow]
  congr 1
  unfold phase
  rw [← Complex.exp_nat_mul]
  congr 1
  have hd : dot t (-(fun i => (m:ℝ)*mean ρ i)) = (m:ℝ)*dot t (-mean ρ) := by
    simp only [dot, Pi.neg_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hd]
  push_cast
  ring

theorem centeredChi_gaussian (ρ : Measure (Fin d → ℕ)) [IsProbabilityMeasure ρ]
    (m : ℕ) (t : Fin d → ℝ)
    (hfirst : Integrable (centeredProjection ρ t) ρ)
    (hsecond : Integrable (fun x => centeredProjection ρ t x ^ 2) ρ)
    (hthird : Integrable (fun x => |centeredProjection ρ t x| ^ 3) ρ)
    (hzero : ∫ x, centeredProjection ρ t x ∂ρ = 0) :
    ‖centeredChi ρ m t - (Real.exp (-(m:ℝ)*varianceForm ρ t/2) : ℂ)‖ ≤
      (m:ℝ)*(taylorConstant * thirdMoment ρ t + varianceForm ρ t ^ 2) := by
  have he : (Real.exp (-(m:ℝ)*varianceForm ρ t/2) : ℂ) =
      (Real.exp (-(varianceForm ρ t)/2) : ℂ)^m := by
    rw [show -(m:ℝ)*varianceForm ρ t/2 = (m:ℝ)*(-(varianceForm ρ t)/2) by ring,
      Real.exp_nat_mul, Complex.ofReal_pow]
  rw [centeredChi_eq_pow, he]
  apply (norm_pow_sub_pow_le _ _ (centeredOneChi_norm_le ρ t) ?_ m).trans
  · gcongr
    exact centeredOneChi_gaussian ρ t hfirst hsecond hthird hzero
  · simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by linarith [varianceForm_nonneg ρ t])


theorem centeredProjection_integrable (ρ : Measure (Fin d → ℕ)) [IsFiniteMeasure ρ]
    (t : Fin d → ℝ) (hcoord : ∀ i, Integrable (fun x : Fin d → ℕ => (x i : ℝ)) ρ) :
    Integrable (centeredProjection ρ t) ρ := by
  unfold centeredProjection dot
  exact integrable_finsetSum _ fun i _ => ((hcoord i).sub (integrable_const _)).const_mul _

theorem centeredProjection_integral_zero (ρ : Measure (Fin d → ℕ)) [IsProbabilityMeasure ρ]
    (t : Fin d → ℝ) (hcoord : ∀ i, Integrable (fun x : Fin d → ℕ => (x i : ℝ)) ρ) :
    ∫ x, centeredProjection ρ t x ∂ρ = 0 := by
  unfold centeredProjection dot
  simp only [Pi.sub_apply]
  rw [integral_finsetSum Finset.univ (μ := ρ) (f := fun i (x : Fin d → ℕ) => t i * ((x i : ℝ) - mean ρ i)) (fun i _ => ((hcoord i).sub (integrable_const (mean ρ i))).const_mul (t i))]
  apply Finset.sum_eq_zero
  intro i _
  rw [integral_const_mul, integral_sub (hcoord i) (integrable_const (mean ρ i))]
  simp [mean]

theorem centeredChi_gaussian_of_integrable_coordinates
    (ρ : Measure (Fin d → ℕ)) [IsProbabilityMeasure ρ]
    (m : ℕ) (t : Fin d → ℝ)
    (hcoord : ∀ i, Integrable (fun x : Fin d → ℕ => (x i : ℝ)) ρ)
    (hsecond : Integrable (fun x => centeredProjection ρ t x ^ 2) ρ)
    (hthird : Integrable (fun x => |centeredProjection ρ t x| ^ 3) ρ) :
    ‖centeredChi ρ m t - (Real.exp (-(m:ℝ)*varianceForm ρ t/2) : ℂ)‖ ≤
      (m:ℝ)*(taylorConstant * thirdMoment ρ t + varianceForm ρ t ^ 2) :=
  centeredChi_gaussian ρ m t (centeredProjection_integrable ρ t hcoord) hsecond hthird
    (centeredProjection_integral_zero ρ t hcoord)


theorem varianceForm_eq_sum (ρ : Measure (Fin d → ℕ))
    (hall : ∀ f : (Fin d → ℕ) → ℝ, Integrable f ρ) (t : Fin d → ℝ) :
    varianceForm ρ t = ∑ i, ∑ j, t i * t j *
      (∫ x, ((x i : ℝ) - mean ρ i) * ((x j : ℝ) - mean ρ j) ∂ρ) := by
  have he (x : Fin d → ℕ) : centeredProjection ρ t x ^2 =
      ∑ i, ∑ j, t i * t j * (((x i : ℝ) - mean ρ i) * ((x j : ℝ) - mean ρ j)) := by
    simp only [centeredProjection, dot, Pi.sub_apply, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold varianceForm
  simp_rw [he]
  rw [integral_finsetSum _ (fun _ _ => hall _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun _ _ => hall _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul]

theorem varianceForm_continuous (ρ : Measure (Fin d → ℕ))
    (hall : ∀ f : (Fin d → ℕ) → ℝ, Integrable f ρ) :
    Continuous (varianceForm ρ) := by
  have he := funext (varianceForm_eq_sum ρ hall)
  rw [he]
  fun_prop

theorem gaussianComparison_continuous (ρ : Measure (Fin d → ℕ))
    (hall : ∀ f : (Fin d → ℕ) → ℝ, Integrable f ρ) (m : ℕ) :
    Continuous (fun t => Real.exp (-(m:ℝ)*varianceForm ρ t/2)) :=
  Real.continuous_exp.comp (((varianceForm_continuous ρ hall).const_mul _).div_const _)


theorem centeredChi_gaussian_of_moment_bounds
    (ρ : Measure (Fin d → ℕ)) [IsProbabilityMeasure ρ]
    (hall : ∀ f : (Fin d → ℕ) → ℝ, Integrable f ρ)
    (m : ℕ) (t : Fin d → ℝ) (a b : ℝ)
    (ha : varianceForm ρ t ≤ a) (hb : thirdMoment ρ t ≤ b) :
    ‖centeredChi ρ m t - (Real.exp (-(m:ℝ)*varianceForm ρ t/2) : ℂ)‖ ≤
      (m:ℝ)*(taylorConstant*b+a^2) := by
  apply (centeredChi_gaussian_of_integrable_coordinates ρ m t (fun _ => hall _)
    (hall _) (hall _)).trans
  have hq := varianceForm_nonneg ρ t
  have hc := taylorConstant_pos
  gcongr

end MajorityDynamics.Probability.ConditionedBinomialLocalCLT
