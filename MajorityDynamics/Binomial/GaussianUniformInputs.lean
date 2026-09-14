import MajorityDynamics.Binomial.GaussianErrorBounds
import MajorityDynamics.Binomial.GaussianWindowComparison

/-! # Uniform inputs for the Gaussian comparison on the common window -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace MajorityDynamics.Binomial.Approximation
variable {d : ℕ}

theorem gaussian_window_error_bound (p : Probability) (η : Fin d → ℕ) (T n s l : ℝ)
    (hT : 1 ≤ T) (hn : 0 < n) (hs : 0 < s) (hl : 1 ≤ l)
    (hscale : s ^ 2 = (p : ℝ) * n) (hps : (p : ℝ) * s ≤ 1)
    (hμ : ∀ i, s ^ 2 / T ≤ (p : ℝ) * η i)
    (hrem : ∀ i, n / (2 * T) ≤ (η i : ℝ) - (p : ℝ) * η i) :
    gaussianWindowError p η (fun _ => s * l) ≤ 16 * d * T ^ 2 * l ^ 3 / s := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
    gaussian_step_error_bound (η i) ((p : ℝ) * η i) T n p s l hT hn p.property.1 hs hl hscale hps (hμ i) (hrem i))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  unfold gaussianWindowError
  simpa only [show (d : ℝ) * (16 * T ^ 2 * l ^ 3 / s) = 16 * d * T ^ 2 * l ^ 3 / s by ring] using h

theorem gaussian_uniform_cell_error (p : Probability) (η : Fin d → ℕ) (α : Fin d → ℝ)
    (T s l : ℝ) (hT : 1 ≤ T) (hs : 0 < s) (hl : T ^ 2 ≤ l)
    (hL : 1 ≤ s * l) (hsmall : 8 * T * l / s ≤ 1 / 2)
    (hμ : ∀ i, s ^ 2 / T ≤ (p : ℝ) * η i)
    (hσ : ∀ i, Real.sqrt ((p : ℝ) * η i) ≤ T * s) (hα : ∀ i, |α i| ≤ T) :
    ∀ a ∈ rectangleWindow (fun i => (p : ℝ) * η i) (fun _ => s * l), ∀ i,
      |(gaussianReal (gaussianMean p η α i) (gaussianVariance p η i)).real
        (Ico (centered p η a i) (centered p η a i + 1)) -
        gaussianPDFReal (gaussianMean p η α i) (gaussianVariance p η i) (centered p η a i)| ≤
      (8 * T * l / s) * gaussianPDFReal (gaussianMean p η α i) (gaussianVariance p η i) (centered p η a i) := by
  intro a ha i
  have hT0 : 0 < T := by linarith
  have hl0 : 0 ≤ l := (sq_nonneg T).trans hl
  have hv : 0 < (p : ℝ) * η i := (by positivity : 0 < s ^ 2 / T).trans_le (hμ i)
  have hmean : |gaussianMean p η α i| ≤ T ^ 2 * s := by
    dsimp [gaussianMean]
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have h := mul_le_mul (hσ i) (hα i) (abs_nonneg _) (by positivity : 0 ≤ T * s)
    nlinarith only [h]
  have hx : |centered p η a i - gaussianMean p η α i| ≤ 2 * s * l := by
    have hb := (mem_rectangleWindow _ _ _).mp ha i
    change |centered p η a i| ≤ s * l at hb
    have h := (abs_sub _ _).trans (add_le_add hb hmean)
    nlinarith [mul_le_mul_of_nonneg_left hl hs.le]
  have herr : (2 * (2 * s * l) + 1) / (2 * ((p : ℝ) * η i)) ≤ 4 * T * l / s := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hm := (div_le_iff₀ hT0).mp (hμ i)
    have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ 8 * l / s by positivity)
    have hid : 8 * l / s * s ^ 2 = 8 * s * l := by field_simp
    rw [hid] at hh
    simp only [div_eq_mul_inv] at hh ⊢
    nlinarith only [hh, hL]
  have hmass := Analysis.gaussian_cell_mass_error (gaussianMean p η α i) (gaussianVariance p η i)
    (show 0 < gaussianVariance p η i from hv) (centered p η a i) (2 * s * l) (by positivity) hx
    (show (2 * (2 * s * l) + 1) / (2 * (gaussianVariance p η i : ℝ)) ≤ 1 by
      change (2 * (2 * s * l) + 1) / (2 * ((p : ℝ) * η i)) ≤ 1
      simp only [div_eq_mul_inv] at herr hsmall ⊢
      linarith)
  apply hmass.trans
  apply mul_le_mul_of_nonneg_right _ (gaussianPDFReal_nonneg _ _ _)
  change 2 * ((2 * (2 * s * l) + 1) / (2 * ((p : ℝ) * η i))) ≤ 8 * T * l / s
  simp only [div_eq_mul_inv] at herr ⊢
  linarith

theorem gaussian_uniform_binomial_tail (p : Probability) (η : Fin d → ℕ) (α : Fin d → ℝ)
    (hη : ∀ i, 0 < η i) (T s l : ℝ) (hT : 0 < T) (hs : 0 < s)
    (hl : 8 * T ^ 2 ≤ l) (hls : l ≤ s)
    (hshift : ∀ i, |(η i : ℝ) * (gaussianTilt p η α i : ℝ) - (p : ℝ) * η i| ≤ 4 * T ^ 2 * s)
    (hmean : ∀ i, (η i : ℝ) * (gaussianTilt p η α i : ℝ) ≤ 2 * T * s ^ 2) :
    (law η (gaussianTilt p η α)).real (rectangle (fun i => (p : ℝ) * η i) (fun _ => s * l))ᶜ ≤
      2 * d * Real.exp (-(l ^ 2) / (32 * T + 4)) := by
  have htail (i : Fin d) := centered_tail_scaled (η i) (gaussianTilt p η α i) (hη i)
    ((p : ℝ) * η i) s l (4 * T) hs ((by positivity : 0 ≤ 8 * T ^ 2).trans hl) (by positivity)
    (show |(η i : ℝ) * (gaussianTilt p η α i : ℝ) - (p : ℝ) * η i| ≤ s * l / 2 by
      have h := hshift i
      nlinarith [mul_le_mul_of_nonneg_left hl hs.le])
    ((hmean i).trans (by nlinarith [sq_nonneg s])) hls
  have h := rectangle_tail_le η (gaussianTilt p η α) (fun i => (p : ℝ) * η i) (fun _ => s * l)
    (fun _ => 2 * Real.exp (-(l ^ 2) / (32 * T + 4))) (fun i => by simpa only [show 8 * (4 * T) + 4 = 32 * T + 4 by ring] using htail i)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    show (d : ℝ) * (2 * Real.exp (-(l ^ 2) / (32 * T + 4))) = 2 * d * Real.exp (-(l ^ 2) / (32 * T + 4)) by ring] using h

/-- The quantitative inputs consumed by the actual-measure comparison. -/
structure GaussianWindowInputs (p : Probability) (η : Fin d → ℕ) (α : Fin d → ℝ)
    (T n s l : ℝ) : Prop where
  hη : ∀ i, 0 < η i
  hηR : ∀ i, (η i : ℝ) ≤ T * n
  hL : 2 ≤ s * l
  hcomp : ∀ i, s * l ≤ ((η i : ℝ) - (p : ℝ) * η i) / 2
  hsucc : ∀ i, s * l ≤ ((p : ℝ) * η i) / 2
  hpointBound : gaussianWindowError p η (fun _ => s * l) ≤ 16 * d * T ^ 2 * l ^ 3 / s
  hpointSmall : gaussianWindowError p η (fun _ => s * l) ≤ 1 / 4
  epsSmall : 8 * T * l / s ≤ 1 / 2
  cellSmall : 4 * d * (8 * T * l / s) ≤ 1 / 4
  hcell : ∀ a ∈ rectangleWindow (fun i => (p : ℝ) * η i) (fun _ => s * l), ∀ i,
    |(gaussianReal (gaussianMean p η α i) (gaussianVariance p η i)).real
      (Ico (centered p η a i) (centered p η a i + 1)) -
      gaussianPDFReal (gaussianMean p η α i) (gaussianVariance p η i) (centered p η a i)| ≤
    (8 * T * l / s) * gaussianPDFReal (gaussianMean p η α i) (gaussianVariance p η i) (centered p η a i)
  hvarlo : ∀ i, s ^ 2 / T ≤ (p : ℝ) * η i
  hvarhi : ∀ i, (p : ℝ) * η i ≤ T * s ^ 2
  hsqrt : ∀ i, Real.sqrt ((p : ℝ) * η i) ≤ T * s
  htailBin : (law η (gaussianTilt p η α)).real
    (rectangle (fun i => (p : ℝ) * η i) (fun _ => s * l))ᶜ ≤
      2 * d * Real.exp (-(l ^ 2) / (32 * T + 4))
  htailGauss : (gaussianLaw p η α).real (gaussianCellWindow p η (s * l))ᶜ ≤
      2 * d * Real.exp (-(l ^ 2) / (32 * T + 4))

def gaussianWindowConstant (d : ℕ) (T : ℝ) : ℝ := 1024 * ((d : ℝ) + 1) * (T + 1) ^ 2

set_option maxHeartbeats 800000 in
theorem gaussian_uniform_inputs (p : Probability) (η : Fin d → ℕ) (α : Fin d → ℝ)
    (T n s l : ℝ) (hd : 1 ≤ d) (hT : 1 ≤ T) (hn : 0 < n) (hs : 0 < s)
    (hl : 1 + 8 * T ^ 2 + 128 * d * T ≤ l)
    (hscale : s ^ 2 = (p : ℝ) * n) (hps : (p : ℝ) * s ≤ 1) (hp : (p : ℝ) ≤ 1 / 8)
    (hlarge : gaussianWindowConstant d T * l ^ 3 ≤ s)
    (hηlo : ∀ i, n / T ≤ (η i : ℝ)) (hηhi : ∀ i, (η i : ℝ) ≤ T * n)
    (hα : ∀ i, |α i| ≤ T) : GaussianWindowInputs p η α T n s l := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hT0 : 0 < T := by linarith
  have hT2 : T ≤ T ^ 2 := by nlinarith
  have hl8 : 8 * T ^ 2 ≤ l := by nlinarith
  have hl1 : 1 ≤ l := by nlinarith
  have hl0 : 0 ≤ l := by linarith
  have hl13 : l ≤ l ^ 3 := by nlinarith [mul_nonneg (sq_nonneg l) (show 0 ≤ l - 1 by linarith)]
  have hK1 : 1 ≤ gaussianWindowConstant d T := by
    unfold gaussianWindowConstant
    nlinarith [sq_nonneg (T + 1), mul_nonneg hd0 (sq_nonneg (T + 1))]
  have hK : 128 * ((d : ℝ) + 1) * T ^ 2 ≤ gaussianWindowConstant d T := by
    unfold gaussianWindowConstant
    nlinarith [mul_nonneg (show 0 ≤ (d : ℝ) + 1 by positivity) (show 0 ≤ (T + 1) ^ 2 - T ^ 2 by nlinarith)]
  have hsbound : 128 * ((d : ℝ) + 1) * T ^ 2 * l ^ 3 ≤ s :=
    (mul_le_mul_of_nonneg_right hK (by positivity)).trans hlarge
  have hls3 : l ^ 3 ≤ s := by
    have h := mul_le_mul_of_nonneg_right hK1 (show 0 ≤ l ^ 3 by positivity)
    nlinarith only [h, hlarge]
  have hls : l ≤ s := hl13.trans hls3
  have hgeom : 16 * T ^ 2 * l ≤ s := by
    have h := mul_le_mul_of_nonneg_left hl13 (show 0 ≤ 16 * T ^ 2 by positivity)
    have h' : 16 * T ^ 2 * l ^ 3 ≤ 128 * ((d : ℝ) + 1) * T ^ 2 * l ^ 3 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith [mul_nonneg hd0 (sq_nonneg T)]
    exact h.trans (h'.trans hsbound)
  have hscalar (i : Fin d) := gaussian_scalar_geometry (η i) p T n s l (α i) hT hn hs hl8
    hscale (by linarith) (hηlo i) (hηhi i) hgeom (hα i)
  have heta : ∀ i, 0 < η i := by
    intro i
    have hi := (div_pos hn hT0).trans_le (hηlo i)
    exact_mod_cast hi
  have hμ := fun i => (hscalar i).1
  have hvar := fun i => (hscalar i).2.1
  have hrem := fun i => (hscalar i).2.2.1
  have hsucc := fun i => (hscalar i).2.2.2.1
  have hσ := fun i => (hscalar i).2.2.2.2.1
  have hshift := fun i => (hscalar i).2.2.2.2.2.2.1
  have hmean := fun i => (hscalar i).2.2.2.2.2.2.2
  have hlog := logarithmic_window_conditions (d : ℝ) T n p s l 0 hdR hT hn p.property.1
    p.property.2.le hs hscale hl hls3 hps (by norm_num) (by positivity)
  have hL : 2 ≤ s * l := by nlinarith
  have hcomp (i : Fin d) : s * l ≤ ((η i : ℝ) - (p : ℝ) * η i) / 2 := by
    have h := hlog.2.2.2.1
    have hr := hrem i
    have hid : n / (2 * T) = 4 * (n / (8 * T)) := by ring
    rw [hid] at hr
    linarith
  have hpoint := gaussian_window_error_bound p η T n s l hT hn hs hl1 hscale hps hμ hrem
  have hpointnum : 16 * d * T ^ 2 * l ^ 3 / s ≤ 1 / 4 := by
    apply (div_le_iff₀ hs).mpr
    have h : 64 * d * T ^ 2 * l ^ 3 ≤ 128 * ((d : ℝ) + 1) * T ^ 2 * l ^ 3 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith [mul_nonneg hd0 (sq_nonneg T)]
    linarith
  have hepsnum : 128 * ((d : ℝ) + 1) * T * l ≤ s := by
    have h := mul_le_mul hT2 hl13 hl0 (sq_nonneg T)
    have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ 128 * ((d : ℝ) + 1) by positivity)
    nlinarith only [hh, hsbound]
  have heps : 8 * T * l / s ≤ 1 / 2 := by
    apply (div_le_iff₀ hs).mpr
    nlinarith [mul_nonneg hd0 (show 0 ≤ T * l by positivity)]
  have hcellsmall : 4 * d * (8 * T * l / s) ≤ 1 / 4 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hs).mpr
    nlinarith only [hepsnum, mul_nonneg (show 0 ≤ T by linarith) hl0]
  have hcell := gaussian_uniform_cell_error p η α T s l hT hs (by linarith) (by linarith)
    heps hμ hσ hα
  have htailBin := gaussian_uniform_binomial_tail p η α heta T s l hT0 hs hl8 hls hshift hmean
  have hgauss := gaussianCellWindow_tail p η α heta T s l hT0 hs hl0 hL
    (fun i => by have h := hsucc i; have hpμ := mul_nonneg p.property.1.le (Nat.cast_nonneg (η i)); linarith)
    (fun i => by
      dsimp [gaussianMean]
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      have h := mul_le_mul (hσ i) (hα i) (abs_nonneg _) (by positivity : 0 ≤ T * s)
      nlinarith [mul_le_mul_of_nonneg_left hl8 hs.le]) hvar
  have htailGauss : (gaussianLaw p η α).real (gaussianCellWindow p η (s * l))ᶜ ≤
      2 * d * Real.exp (-(l ^ 2) / (32 * T + 4)) := by
    apply hgauss.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div]
    apply neg_le_neg
    exact div_le_div_of_nonneg_left (sq_nonneg l) (by positivity) (by linarith)
  exact ⟨heta, hηhi, hL, hcomp, hsucc, hpoint, hpoint.trans hpointnum, heps, hcellsmall,
    hcell, hμ, hvar, hσ, htailBin, htailGauss⟩

end MajorityDynamics.Binomial.Approximation
