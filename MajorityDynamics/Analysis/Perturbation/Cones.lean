import MajorityDynamics.Analysis.Perturbation.ConesBasic

/-!
# Perturbations on compact cone targets

Source: `latest/main.tex`, Appendix D.3, `thm:perturbed-bijection`.
The paper's coordinate cube is compact; intersecting it with the closed
row-margin halfspaces gives the exact compact target set. For T > 1 the
positive margin puts this set inside the strict conditioning cone. None of
these geometric facts needs a rank hypothesis or nonemptiness of the target.
The final specialization consumes only the abstract perturbation theorem.
-/

noncomputable section

open Set
open scoped Matrix

namespace MajorityDynamics.Analysis.Perturbation

variable {d r : ℕ}

/-- The exact coordinate cube and closed row margins form a compact set. -/
theorem compactCone_isCompact (M : Matrix (Fin r) (Fin d) ℝ) (T : ℝ) :
    IsCompact (compactCone M T) := by
  have hcube : IsCompact {y : Space d | ∀ j, |y j| ≤ T} := by
    have hc : IsCompact (Set.univ.pi (fun _ : Fin d => Set.Icc (-T) T)) :=
      isCompact_univ_pi (fun _ => isCompact_Icc)
    convert ((PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isCompact_preimage).2 hc using 1
    ext y
    change (∀ j, |y j| ≤ T) ↔ ∀ j ∈ Set.univ, y j ∈ Set.Icc (-T) T
    simp only [Set.mem_univ, forall_const, Set.mem_Icc, abs_le]
  have hrows : IsClosed {y : Space d | ∀ i, T⁻¹ ≤ (M *ᵥ y) i} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro i
    apply isClosed_le continuous_const
    change Continuous (fun y : Space d => ∑ j, M i j * y j)
    exact continuous_finsetSum _
      (fun j _ => continuous_const.mul (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) j))
  exact hcube.inter_right hrows

/-- A positive row margin places every compact target inside the open cone. -/
theorem compactCone_subset_cone (M : Matrix (Fin r) (Fin d) ℝ)
    {T : ℝ} (hT : 1 < T) : compactCone M T ⊆ ConditionalGaussian.cone M := by
  intro y hy i
  exact (inv_pos.mpr (lt_trans zero_lt_one hT)).trans_le (hy.2 i)

/-- With no rows the compact cone target is precisely the coordinate cube. -/
@[simp]
theorem compactCone_zero_rows (M : Matrix (Fin 0) (Fin d) ℝ) (T : ℝ) :
    compactCone M T = {y | ∀ j, |y j| ≤ T} := by
  ext y
  simp [compactCone]

/-- The cone specialization follows from the abstract perturbation theorem. -/
theorem conePerturbation_of_perturbation :
    PerturbationTheorem → ConePerturbationTheorem := by
  intro hperturbation d r hd _hr M _hM f T hT C₀ hC₀
  exact hperturbation d hd (ConditionalGaussian.cone M) f (compactCone M T)
    (compactCone_isCompact M T) (compactCone_subset_cone M hT) C₀ hC₀

end MajorityDynamics.Analysis.Perturbation
