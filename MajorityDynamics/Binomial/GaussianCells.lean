import MajorityDynamics.Binomial.GaussianWeights
import MajorityDynamics.Analysis.GaussianCell
import MajorityDynamics.Analysis.DiscreteApproximation

/-! # Product Gaussian unit cells on the original shifted natural lattice -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
namespace MajorityDynamics.Binomial.Approximation
variable {d : ℕ}

def gaussianCell (p : Probability) (η a : Fin d → ℕ) : Set (Fin d → ℝ) :=
  Set.univ.pi fun i => Ico (centered p η a i) (centered p η a i + 1)

theorem gaussianCell_measurable (p : Probability) (η a : Fin d → ℕ) :
    MeasurableSet (gaussianCell p η a) := MeasurableSet.univ_pi fun _ => measurableSet_Ico

theorem gaussianCell_disjoint (p : Probability) (η a b : Fin d → ℕ) (hab : a ≠ b) :
    Disjoint (gaussianCell p η a) (gaussianCell p η b) := by
  apply Set.disjoint_left.mpr
  intro x ha hb
  apply hab
  funext i
  have hai := ha i (Set.mem_univ i)
  have hbi := hb i (Set.mem_univ i)
  change ((a i : ℝ) - (p : ℝ) * η i ≤ x i ∧ x i < (a i : ℝ) - (p : ℝ) * η i + 1) at hai
  change ((b i : ℝ) - (p : ℝ) * η i ≤ x i ∧ x i < (b i : ℝ) - (p : ℝ) * η i + 1) at hbi
  have hab' : a i < b i + 1 := by exact_mod_cast (show (a i : ℝ) < b i + 1 by linarith)
  have hba' : b i < a i + 1 := by exact_mod_cast (show (b i : ℝ) < a i + 1 by linarith)
  omega

theorem gaussianCell_coordinate_error (p : Probability) (η a : Fin d → ℕ)
    {x : Fin d → ℝ} (hx : x ∈ gaussianCell p η a) :
    ∀ i, |centered p η a i - x i| ≤ 1 := by
  intro i
  have hi := hx i (Set.mem_univ i)
  rw [abs_of_nonpos (sub_nonpos.mpr hi.1)]
  linarith [hi.2]

def gaussianCellMass (p : Probability) (η : Fin d → ℕ) (α : Fin d → ℝ)
    (a : Fin d → ℕ) : ℝ := (gaussianLaw p η α).real (gaussianCell p η a)

set_option backward.isDefEq.respectTransparency false in
theorem gaussianCellMass_eq_prod (p : Probability) (η : Fin d → ℕ) (α : Fin d → ℝ)
    (a : Fin d → ℕ) :
    gaussianCellMass p η α a = ∏ i,
      (gaussianReal (Real.sqrt ((p : ℝ) * η i) * α i)
        ⟨(p : ℝ) * η i, mul_nonneg p.property.1.le (Nat.cast_nonneg _)⟩).real
      (Ico (centered p η a i) (centered p η a i + 1)) := by
  unfold gaussianCellMass gaussianLaw gaussianCell
  rw [measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  rfl

theorem gaussianCell_volume (p : Probability) (η a : Fin d → ℕ) :
    volume.real (gaussianCell p η a) = 1 := by
  simp [gaussianCell, measureReal_def, volume_pi, Measure.pi_pi]

/-- Small relative weight error gives an explicit log-weight error. -/
theorem log_weight_error (P Q δ : ℝ) (hQ : 0 < Q) (hδ : δ ≤ 1 / 2)
    (h : |P - Q| ≤ δ * Q) : 0 < P ∧ |Real.log P - Real.log Q| ≤ 2 * δ := by
  have hδ0 : 0 ≤ δ := by nlinarith [abs_nonneg (P - Q)]
  have hP : 0 < P := by have hh := (abs_le.mp h).1; nlinarith
  have herr : |P / Q - 1| ≤ δ := by
    rw [show P / Q - 1 = (P - Q) / Q by rw [sub_div, div_self hQ.ne'], abs_div, abs_of_pos hQ]
    exact (div_le_iff₀ hQ).mpr h
  have he := Analysis.abs_log_one_add_le (herr.trans hδ)
  rw [show 1 + (P / Q - 1) = P / Q by ring, Real.log_div hP.ne' hQ.ne'] at he
  exact ⟨hP, he.trans (mul_le_mul_of_nonneg_left herr (by norm_num))⟩

end MajorityDynamics.Binomial.Approximation
