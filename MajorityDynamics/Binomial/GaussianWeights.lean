import MajorityDynamics.Binomial.WindowExpansion

/-! # The Gaussian lattice weights and the normalized binomial comparison -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace MajorityDynamics.Binomial.Approximation
open Analysis.FiniteTiltEstimate
variable {d : ℕ}

theorem log_windowSlope_gaussian (m : ℕ) (hm : 0 < m) (p : Probability) (α : ℝ) :
    Real.log (windowSlope m ((p : ℝ) * m)
      (Idealized.logistic (logOdds p + α / Real.sqrt ((p : ℝ) * m)))) =
      α / Real.sqrt ((p : ℝ) * m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hμ : 0 < (p : ℝ) * m := mul_pos p.property.1 hm0
  have hcomp : (p : ℝ) * m < m := by nlinarith [p.property.2]
  rw [log_windowSlope hμ hcomp, Idealized.logOdds_logistic]
  have heq : (m : ℝ) - (p : ℝ) * m = (1 - (p : ℝ)) * m := by ring
  rw [heq, Real.log_mul (sub_pos.mpr p.property.2).ne' hm0.ne',
    Real.log_mul p.property.1.ne' hm0.ne', logOdds]
  ring

def gaussianLatticeWeight (p : Probability) (η : Fin d → ℕ) (α : Fin d → ℝ)
    (a : Fin d → ℕ) : ℝ :=
  ∏ i, Real.exp (-(((a i : ℝ) - (p : ℝ) * η i - Real.sqrt ((p : ℝ) * η i) * α i) ^ 2) /
    (2 * ((p : ℝ) * η i)))

theorem gaussianShape_gaussian (m : ℕ) (hm : 0 < m) (p : Probability) (α : ℝ) (k : ℕ) :
    gaussianShape ((p : ℝ) * m)
      (windowSlope m ((p : ℝ) * m) (Idealized.logistic (logOdds p + α / Real.sqrt ((p : ℝ) * m)))) k =
    Real.exp (-(((k : ℝ) - (p : ℝ) * m - Real.sqrt ((p : ℝ) * m) * α) ^ 2) /
      (2 * ((p : ℝ) * m))) := by
  rw [gaussianShape, log_windowSlope_gaussian m hm p α]
  have hμ : 0 < (p : ℝ) * m := mul_pos p.property.1 (by exact_mod_cast hm)
  have hs := Real.sqrt_pos.mpr hμ
  have heq : ((p : ℝ) * m) * (α / Real.sqrt ((p : ℝ) * m)) = Real.sqrt ((p : ℝ) * m) * α := by
    field_simp
    rw [Real.sq_sqrt hμ.le]
    ring
  rw [heq]

theorem gaussianLatticeWeight_pos (p : Probability) (η : Fin d → ℕ) (α : Fin d → ℝ)
    (a : Fin d → ℕ) : 0 < gaussianLatticeWeight p η α a :=
  Finset.prod_pos fun _ _ => Real.exp_pos _

def gaussianLatticeExpectation (p : Probability) (η : Fin d → ℕ) (α : Fin d → ℝ)
    (S : Finset (Fin d → ℕ)) (f : (Fin d → ℕ) → ℝ) : ℝ :=
  average S (Analysis.FiniteTiltEstimate.normalize S (gaussianLatticeWeight p η α)) f

def gaussianWindowError (p : Probability) (η : Fin d → ℕ) (L : Fin d → ℝ) : ℝ :=
  ∑ i, 2 * L i * gaussianStepError (η i) ((p : ℝ) * η i) (L i)

/-- On a common window, actual binomial expectations differ from normalized
Gaussian lattice expectations by the proved logarithmic likelihood error. -/
theorem finite_gaussian_comparison (p : Probability) (η : Fin d → ℕ) (α L : Fin d → ℝ)
    (hη : ∀ i, 0 < η i) (hL : ∀ i, 0 ≤ L i)
    (hcomp : ∀ i, L i ≤ ((η i : ℝ) - (p : ℝ) * η i) / 2)
    (hsucc : ∀ i, L i ≤ ((p : ℝ) * η i) / 2)
    (S : Finset (Fin d → ℕ)) (hS : S.Nonempty)
    (hrect : ∀ a ∈ S, a ∈ rectangle (fun i => (p : ℝ) * η i) L)
    (f : (Fin d → ℕ) → ℝ) (H : ℝ) (hH : 0 ≤ H) (hf : ∀ a ∈ S, |f a| ≤ H)
    (hsmall : gaussianWindowError p η L ≤ 1 / 4) :
    |finiteExpectation η (gaussianTilt p η α) S f - gaussianLatticeExpectation p η α S f| ≤
      8 * H * gaussianWindowError p η L := by
  have hμ (i : Fin d) : 0 < (p : ℝ) * η i := mul_pos p.property.1 (by exact_mod_cast hη i)
  have hm (i : Fin d) : (p : ℝ) * η i < η i := by
    have hi : (0 : ℝ) < η i := by exact_mod_cast hη i
    nlinarith [p.property.2]
  have hsupp (a : Fin d → ℕ) (ha : a ∈ S) (i : Fin d) : a i ≤ η i := by
    have hai := (abs_le.mp (hrect a ha i)).2
    have hci := hcomp i
    have hmi := hm i
    exact_mod_cast (show (a i : ℝ) ≤ η i by linarith)
  have hmass : ∀ a ∈ S, 0 < ambientMass η (gaussianTilt p η α) a := by
    intro a ha
    rw [ambientMass_eq_prod_pointMass]
    exact Finset.prod_pos fun i _ => pointMass_pos (hsupp a ha i) _
  have hδ : 0 ≤ gaussianWindowError p η L := by
    apply Finset.sum_nonneg
    intro i _
    have hc := sub_pos.mpr (hm i)
    have hi := hμ i
    have hl := hL i
    unfold gaussianStepError
    positivity
  obtain ⟨a₀, ha₀⟩ := hS
  have hlog (a : Fin d → ℕ) : Real.log (gaussianLatticeWeight p η α a) =
      ∑ i, Real.log (gaussianShape ((p : ℝ) * η i)
        (windowSlope (η i) ((p : ℝ) * η i) (gaussianTilt p η α i)) (a i)) := by
    rw [gaussianLatticeWeight, Real.log_prod (fun _ _ => (Real.exp_pos _).ne')]
    apply Finset.sum_congr rfl
    intro i _
    rw [gaussianTilt, gaussianShape_gaussian (η i) (hη i) p (α i)]
  have h := normalized_log_tilt_expansion S a₀ ha₀ (gaussianLatticeWeight p η α)
    (ambientMass η (gaussianTilt p η α)) f (fun _ => 0)
    (fun a _ => gaussianLatticeWeight_pos p η α a) hmass H 0 (gaussianWindowError p η L)
    hH le_rfl hδ (by norm_num) hsmall hf (by simp) (by
      intro a ha
      simp only [sub_zero, log_ambientMass η (gaussianTilt p η α) a (hsupp a ha),
        log_ambientMass η (gaussianTilt p η α) a₀ (hsupp a₀ ha₀), hlog, ← Finset.sum_sub_distrib]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i _
      apply Analysis.window_log_error (fun k : ℕ => Real.log (pointMass (η i) k (gaussianTilt p η α i)) -
        Real.log (gaussianShape ((p : ℝ) * η i) (windowSlope (η i) ((p : ℝ) * η i) (gaussianTilt p η α i)) k))
        ((p : ℝ) * η i) (L i) (gaussianStepError (η i) ((p : ℝ) * η i) (L i))
        (by have hc := sub_pos.mpr (hm i); have hi := hμ i; have hl := hL i; unfold gaussianStepError; positivity)
        (a₀ i) (a i) (hrect a₀ ha₀ i) (hrect a ha i)
      exact gaussian_log_step_error (η i) ((p : ℝ) * η i) (L i) (gaussianTilt p η α i)
        (hμ i) (hm i) (hL i) (hcomp i) (hsucc i))
  simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_mul,
    Analysis.FiniteTiltEstimate.average, Finset.sum_const_zero, add_zero, zero_add, sub_zero,
    finiteExpectation, gaussianLatticeExpectation] using h

end MajorityDynamics.Binomial.Approximation
