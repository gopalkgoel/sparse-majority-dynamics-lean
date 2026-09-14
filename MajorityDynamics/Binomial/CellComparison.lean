import MajorityDynamics.Binomial.GaussianCells

/-! # Normalized Gaussian lattice weights versus actual Gaussian cell masses -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace MajorityDynamics.Binomial.Approximation
open Analysis.FiniteTiltEstimate
variable {d : ℕ}

def gaussianMean (p : Probability) (η : Fin d → ℕ) (α : Fin d → ℝ) (i : Fin d) : ℝ :=
  Real.sqrt ((p : ℝ) * η i) * α i

def gaussianVariance (p : Probability) (η : Fin d → ℕ) (i : Fin d) : ℝ≥0 :=
  ⟨(p : ℝ) * η i, mul_nonneg p.property.1.le (Nat.cast_nonneg _)⟩

def gaussianDensityWeight (p : Probability) (η : Fin d → ℕ) (α : Fin d → ℝ)
    (a : Fin d → ℕ) : ℝ :=
  ∏ i, gaussianPDFReal (gaussianMean p η α i) (gaussianVariance p η i) (centered p η a i)

def gaussianDensityConstant (p : Probability) (η : Fin d → ℕ) : ℝ :=
  ∏ i, (Real.sqrt (2 * Real.pi * ((p : ℝ) * η i)))⁻¹

theorem gaussianDensityWeight_eq (p : Probability) (η : Fin d → ℕ) (α : Fin d → ℝ)
    (a : Fin d → ℕ) :
    gaussianDensityWeight p η α a = gaussianDensityConstant p η * gaussianLatticeWeight p η α a := by
  simp only [gaussianDensityWeight, gaussianPDFReal, gaussianDensityConstant, gaussianLatticeWeight,
    gaussianMean, gaussianVariance, centered, Finset.prod_mul_distrib]
  rfl

theorem normalized_gaussianDensityWeight (p : Probability) (η : Fin d → ℕ)
    (hη : ∀ i, 0 < η i) (α : Fin d → ℝ) (S : Finset (Fin d → ℕ)) :
    Analysis.FiniteTiltEstimate.normalize S (gaussianDensityWeight p η α) =
      Analysis.FiniteTiltEstimate.normalize S (gaussianLatticeWeight p η α) := by
  have hK : gaussianDensityConstant p η ≠ 0 := by
    apply ne_of_gt
    apply Finset.prod_pos
    intro i _
    have hp := p.property.1
    have hi : (0 : ℝ) < η i := by exact_mod_cast hη i
    positivity
  funext a
  simp only [Analysis.FiniteTiltEstimate.normalize, gaussianDensityWeight_eq, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ hK

def gaussianCellExpectation (p : Probability) (η : Fin d → ℕ) (α : Fin d → ℝ)
    (S : Finset (Fin d → ℕ)) (f : (Fin d → ℕ) → ℝ) : ℝ :=
  average S (Analysis.FiniteTiltEstimate.normalize S (gaussianCellMass p η α)) f

set_option backward.isDefEq.respectTransparency false in
/-- The normalization factor of the Gaussian density cancels exactly. Each
coordinate cell error contributes explicitly to the joint expectation bound. -/
theorem finite_cell_comparison (p : Probability) (η : Fin d → ℕ) (α : Fin d → ℝ)
    (hη : ∀ i, 0 < η i) (S : Finset (Fin d → ℕ)) (hS : S.Nonempty)
    (ε H : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 2) (hsmall : 4 * d * ε ≤ 1 / 4)
    (f : (Fin d → ℕ) → ℝ) (hH : 0 ≤ H) (hf : ∀ a ∈ S, |f a| ≤ H)
    (hcell : ∀ a ∈ S, ∀ i,
      |(gaussianReal (gaussianMean p η α i) (gaussianVariance p η i)).real
        (Set.Ico (centered p η a i) (centered p η a i + 1)) -
        gaussianPDFReal (gaussianMean p η α i) (gaussianVariance p η i) (centered p η a i)| ≤
      ε * gaussianPDFReal (gaussianMean p η α i) (gaussianVariance p η i) (centered p η a i)) :
    |gaussianCellExpectation p η α S f - gaussianLatticeExpectation p η α S f| ≤ 32 * H * d * ε := by
  have hv (i : Fin d) : gaussianVariance p η i ≠ 0 := by
    apply ne_of_gt
    exact mul_pos p.property.1 (by exact_mod_cast hη i)
  have hpdf (a : Fin d → ℕ) (i : Fin d) :
      0 < gaussianPDFReal (gaussianMean p η α i) (gaussianVariance p η i) (centered p η a i) :=
    gaussianPDFReal_pos _ _ _ (hv i)
  have hlocal (a : Fin d → ℕ) (ha : a ∈ S) (i : Fin d) :=
    log_weight_error _ _ ε (hpdf a i) hεsmall (hcell a ha i)
  have hmass (a : Fin d → ℕ) (ha : a ∈ S) : 0 < gaussianCellMass p η α a := by
    rw [gaussianCellMass_eq_prod]
    exact Finset.prod_pos fun i _ => (hlocal a ha i).1
  have hpdfprod (a : Fin d → ℕ) : 0 < gaussianDensityWeight p η α a :=
    Finset.prod_pos fun i _ => hpdf a i
  have hlog (a : Fin d → ℕ) (ha : a ∈ S) :
      |Real.log (gaussianCellMass p η α a) - Real.log (gaussianDensityWeight p η α a)| ≤ 2 * d * ε := by
    rw [gaussianCellMass_eq_prod, gaussianDensityWeight]
    change |Real.log (∏ i, (gaussianReal (gaussianMean p η α i) (gaussianVariance p η i)).real
      (Set.Ico (centered p η a i) (centered p η a i + 1))) -
      Real.log (∏ i, gaussianPDFReal (gaussianMean p η α i) (gaussianVariance p η i) (centered p η a i))| ≤ _
    rw [Real.log_prod (fun i _ => (hlocal a ha i).1.ne'), Real.log_prod (fun i _ => (hpdf a i).ne'),
      ← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    have h := Finset.sum_le_sum (fun i (_hi : i ∈ (Finset.univ : Finset (Fin d))) => (hlocal a ha i).2)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      show (d : ℝ) * (2 * ε) = 2 * d * ε by ring] using h
  obtain ⟨a₀, ha₀⟩ := hS
  have h := normalized_log_tilt_expansion S a₀ ha₀ (gaussianDensityWeight p η α)
    (gaussianCellMass p η α) f (fun _ => 0) (fun a _ => hpdfprod a) hmass H 0 (4 * d * ε)
    hH le_rfl (by positivity) (by norm_num) hsmall hf (by simp) (by
      intro a ha
      simp only [sub_zero]
      exact (abs_sub _ _).trans (by linarith [hlog a ha, hlog a₀ ha₀]))
  rw [normalized_gaussianDensityWeight p η hη α S] at h
  simp only [Analysis.FiniteTiltEstimate.average, zero_mul, mul_zero, Finset.sum_const_zero,
    add_zero, sub_zero] at h
  convert h using 1
  · simp only [gaussianCellExpectation, gaussianLatticeExpectation, Analysis.FiniteTiltEstimate.average]
  · ring

end MajorityDynamics.Binomial.Approximation
