import MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Taylor
import MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Scaling
import MajorityDynamics.Probability.ConditionedBinomialLocalCLT.Inversion

noncomputable section
open MeasureTheory ProbabilityTheory

namespace MajorityDynamics.Probability.ConditionedBinomialLocalCLT

open ConditionedBinomialFourier

/-- Uniform low-frequency Taylor error. Its hypotheses are genuine moments;
the original-data theorem below derives all of them from the binomial law. -/
theorem low_point_error {d N m : ℕ} {p δ C T : ℝ}
    (ρ : Measure (Fin d → ℕ)) [IsProbabilityMeasure ρ]
    (hN : 0 < (N : ℝ)) (hp : 0 < p) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hm : (m : ℝ) ≤ T*N)
    (hsmall : (N : ℝ)^(δ-1/2) ≤ 1)
    (hfirst : ∀ t, Integrable (centeredProjection ρ t) ρ)
    (hsecond : ∀ t, Integrable (fun x => centeredProjection ρ t x ^ 2) ρ)
    (hthird : ∀ t, Integrable (fun x => |centeredProjection ρ t x| ^ 3) ρ)
    (hzero : ∀ t, ∫ x, centeredProjection ρ t x ∂ρ = 0)
    (hQ : ∀ t, varianceForm ρ t ≤ C*(Real.sqrt (p*N))^2*‖t‖^2)
    (hM : ∀ t, thirdMoment ρ t ≤ C*(Real.sqrt (p*N))^3*‖t‖^3)
    {t : Fin d → ℝ}
    (ht : t ∈ Geometry.cube d ((N : ℝ)^δ / Real.sqrt ((N : ℝ)^2*p))) :
    ‖centeredChi ρ m t - (Real.exp (-(m:ℝ)*varianceForm ρ t/2) : ℂ)‖ ≤
      (T*(taylorConstant*C+C^2))*(N : ℝ)^(3*δ-1/2) := by
  let s := Real.sqrt (p*N)
  let R := (N : ℝ)^δ / Real.sqrt ((N : ℝ)^2*p)
  let y := s*‖t‖
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hy : 0 ≤ y := mul_nonneg hs (norm_nonneg _)
  have hys : y ≤ s*R := mul_le_mul_of_nonneg_left (Geometry.norm_le_of_mem hR ht) hs
  have hscale : s*R = (N : ℝ)^(δ-1/2) := Scaling.scaled_radius hN hp
  have hy1 : y ≤ 1 := hys.trans (hscale ▸ hsmall)
  have hq : varianceForm ρ t ≤ C*y^2 := by
    simpa [y, s, mul_pow, mul_assoc] using hQ t
  have hq2 : varianceForm ρ t ^ 2 ≤ C^2*y^3 := by
    have hh := (sq_le_sq₀ (varianceForm_nonneg ρ t) (by positivity : 0 ≤ C*y^2)).2 hq
    have hy4 : y^4 ≤ y^3 := by nlinarith [mul_le_mul_of_nonneg_left hy1 (pow_nonneg hy 3)]
    calc
      _ ≤ (C*y^2)^2 := hh
      _ = C^2*y^4 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hy4 (sq_nonneg C)
  have hmom : thirdMoment ρ t ≤ C*y^3 := by
    simpa [y, s, mul_pow, mul_assoc] using hM t
  have hD : 0 ≤ taylorConstant*C+C^2 := by
    have := taylorConstant_pos
    positivity
  calc
    _ ≤ (m:ℝ)*(taylorConstant*thirdMoment ρ t+varianceForm ρ t^2) :=
      centeredChi_gaussian ρ m t (hfirst t) (hsecond t) (hthird t) (hzero t)
    _ ≤ (m:ℝ)*((taylorConstant*C+C^2)*y^3) := by
      gcongr
      nlinarith [mul_le_mul_of_nonneg_left hmom taylorConstant_pos.le]
    _ ≤ (T*N)*((taylorConstant*C+C^2)*(s*R)^3) := by
      apply mul_le_mul hm _ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy hys 3) hD
    _ = (T*(taylorConstant*C+C^2))*(N : ℝ)^(3*δ-1/2) := by
      rw [hscale]
      have hpow : ((N : ℝ)^(δ-1/2))^3 = (N : ℝ)^(3*(δ-1/2)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
        congr 1
        ring
      rw [hpow]
      calc
        _ = (T*(taylorConstant*C+C^2))*((N : ℝ)^(1:ℝ)*(N : ℝ)^(3*(δ-1/2))) := by rw [Real.rpow_one]; ring
        _ = _ := by
          rw [← Real.rpow_add hN]
          congr 2
          ring

def localConstant (d : ℕ) (T C : ℝ) : ℝ :=
  (Real.exp (-T*C/2)*(2:ℝ)^d)/(2*(2*Real.pi)^d)

theorem localConstant_pos (d : ℕ) (T C : ℝ) : 0 < localConstant d T C := by
  unfold localConstant
  positivity

/-- The lower local CLT under explicit genuine moment and high-frequency
estimates. The next theorem closes these premises for the original data. -/
theorem uniform_atom_lower (d : ℕ) (θ T C : ℝ)
    (hθ : θ < 1) (hT : 0 < T) (hC : 1 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p →
      ∀ (ρ : Measure (Fin d → ℕ)) [IsProbabilityMeasure ρ] (m : ℕ),
      (m:ℝ) ≤ T*N →
      (∀ f : (Fin d → ℕ) → ℝ, Integrable f ρ) →
      (∀ t, varianceForm ρ t ≤ C*(Real.sqrt (p*N))^2*‖t‖^2) →
      (∀ t, thirdMoment ρ t ≤ C*(Real.sqrt (p*N))^3*‖t‖^3) →
      ‖∫ t in HighFrequency.region d N p (Scaling.delta d), centeredChi ρ m t‖ ≤
        (N:ℝ)^(-1:ℝ)*((N:ℝ)^2*p)^(-(d:ℝ)/2) →
      ∀ z : Fin d → ℤ, (∀ i, (z i : ℝ) = (m:ℝ)*mean ρ i) →
      localConstant d T C * ((N:ℝ)^2*p)^(-(d:ℝ)/2) ≤
        (copyLaw ρ m).real {x | integerSum x = z} := by
  let a := Real.exp (-T*C/2)*(2:ℝ)^d
  let D := T*(taylorConstant*C+C^2)
  have ha : 0 < a := by dsimp [a]; positivity
  have hC0 : 0 ≤ C := by linarith
  have hD : 0 < D := by
    dsimp [D]
    have := taylorConstant_pos
    positivity
  obtain ⟨N₁, h₁⟩ := Scaling.radius_eventually θ T (Scaling.delta d) hθ hT
    (Scaling.delta_lt_half d)
  obtain ⟨N₂, h₂⟩ := Scaling.integrated_error_eventually d D a hD ha
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN p hlo ρ _ m hm hall hQ hM hhigh z hz
  obtain ⟨hN1, hp, hπ⟩ := h₁ N ((le_max_left _ _).trans hN) p hlo
  obtain ⟨_, herr, hhighsmall⟩ := h₂ N ((le_max_right _ _).trans hN) p hp
  have hn : 0 < (N:ℝ) := by exact_mod_cast hN1
  have hn1 : (1:ℝ) ≤ N := by exact_mod_cast hN1
  let R := (N:ℝ)^(Scaling.delta d)/Real.sqrt ((N:ℝ)^2*p)
  let s := 1/Real.sqrt ((N:ℝ)^2*p)
  let g := fun t => Real.exp (-(m:ℝ)*varianceForm ρ t/2)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hsR : s ≤ R := by
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact Real.one_le_rpow hn1 (Scaling.delta_pos d).le
  have hsmall : ∀ t ∈ Geometry.cube d s, Real.exp (-T*C/2) ≤ g t := by
    intro t ht
    apply Real.exp_le_exp.2
    have hnorm := Geometry.norm_le_of_mem hs ht
    have hh := mul_le_mul_of_nonneg_left (hQ t) (Nat.cast_nonneg m : 0 ≤ (m:ℝ))
    have hsq := pow_le_pow_left₀ (norm_nonneg t) hnorm 2
    have hbound := Scaling.small_gaussian_scale hn hp hm
    have hscale : (m:ℝ)*(p*N)*s^2 ≤ T := hbound
    have hsqrt : (Real.sqrt (p*N))^2 = p*N := Real.sq_sqrt (by positivity)
    rw [hsqrt] at hh
    have hh' : (m:ℝ)*(C*(p*N)*‖t‖^2) ≤ C*((m:ℝ)*(p*N)*s^2) := by
      calc
        _ ≤ (m:ℝ)*(C*(p*N)*s^2) := by gcongr
        _ = _ := by ring
    have hcscale := mul_le_mul_of_nonneg_left hscale hC0
    nlinarith
  have hFl : IntegrableOn (centeredChi ρ m) (HighFrequency.cube d) := by
    rw [HighFrequency.cube_eq_Icc]
    exact (centeredChi_continuous ρ m).continuousOn.integrableOn_compact isCompact_Icc
  have hlow (t : Fin d → ℝ) (ht : t ∈ Geometry.cube d R) :
      ‖centeredChi ρ m t - (g t : ℂ)‖ ≤ D*(N:ℝ)^(3*Scaling.delta d-1/2) :=
    low_point_error (δ := Scaling.delta d) ρ hn hp hC0 hT.le hm
      (Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith [Scaling.delta_lt_half d]))
      (fun _ => hall _) (fun _ => hall _) (fun _ => hall _)
      (fun t => centeredProjection_integral_zero ρ t (fun _ => hall _)) hQ hM ht
  have hout := Geometry.fourier_integral_lower hR hπ hs hsR hFl
    (gaussianComparison_continuous ρ hall m) (fun _ => Real.exp_nonneg _) hsmall
    hlow hhigh
  rw [Scaling.small_cube_scale d hn hp] at hout
  have hatom : 0 ≤ ((N:ℝ)^2*p)^(-(d:ℝ)/2) := by positivity
  have hhigh' := mul_le_mul_of_nonneg_right hhighsmall hatom
  have hfinal : (a/2)*((N:ℝ)^2*p)^(-(d:ℝ)/2) ≤
      (∫ t in HighFrequency.cube d, centeredChi ρ m t).re := by
    dsimp [a, D, R, s] at *
    nlinarith
  rw [integerSum_probability ρ m z hz]
  apply (le_div_iff₀ (by positivity : 0 < (2*Real.pi)^d)).2
  calc
    localConstant d T C * ((N:ℝ)^2*p)^(-(d:ℝ)/2) * (2*Real.pi)^d =
        (a/2)*((N:ℝ)^2*p)^(-(d:ℝ)/2) := by
      dsimp [localConstant, a]
      field_simp
    _ ≤ _ := hfinal

end MajorityDynamics.Probability.ConditionedBinomialLocalCLT
