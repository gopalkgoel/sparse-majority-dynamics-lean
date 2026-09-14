import MajorityDynamics.Analysis.ConditionalGaussian.Basic

/-!
# Full-row-rank conditioning cones

Source: `latest/main.tex`, `cor:cone-bijection`. A full-row-rank matrix has a
preimage of the all-ones vector, so its strict positivity cone is nonempty.
The cone is a finite intersection of open convex halfspaces. These geometric
facts specialize the separately stated `CoreTheorem`, without importing its
proof or assuming any cone conclusion.
-/

noncomputable section

open Set
open scoped Matrix

namespace MajorityDynamics.Analysis.ConditionalGaussian

variable {d r : ℕ}

/-- With no rows there are no inequalities, so the conditioning cone is the whole space. -/
@[simp]
theorem cone_zero_rows (M : Matrix (Fin 0) (Fin d) ℝ) :
    cone M = Set.univ := by
  ext x
  simp [cone]

/-- The zero-row cone has the required geometry, with no rank hypothesis. -/
theorem cone_zero_rows_geometry (M : Matrix (Fin 0) (Fin d) ℝ) :
    (cone M).Nonempty ∧ IsOpen (cone M) ∧ Convex ℝ (cone M) := by
  rw [cone_zero_rows]
  exact ⟨Set.univ_nonempty, isOpen_univ, convex_univ⟩

/-- Full row rank makes the matrix map onto its coordinate codomain. -/
theorem mulVec_surjective_of_rank (M : Matrix (Fin r) (Fin d) ℝ)
    (hM : M.rank = r) : Function.Surjective (Matrix.mulVec M) := by
  change Function.Surjective M.mulVecLin
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  simpa [Matrix.rank, Module.finrank_pi] using hM

/-- A preimage of the all-ones vector belongs to the strict positivity cone. -/
theorem cone_nonempty (M : Matrix (Fin r) (Fin d) ℝ) (hM : M.rank = r) :
    (cone M).Nonempty := by
  obtain ⟨x, hx⟩ := mulVec_surjective_of_rank M hM (fun _ => 1)
  refine ⟨WithLp.toLp 2 x, ?_⟩
  intro i
  change 0 < (M *ᵥ x) i
  rw [hx]
  exact zero_lt_one

/-- The defining inequalities are open, and there are finitely many of them. -/
theorem cone_isOpen (M : Matrix (Fin r) (Fin d) ℝ) : IsOpen (cone M) := by
  change IsOpen {x : Space d | ∀ i, 0 < (M *ᵥ x) i}
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_lt continuous_const
  change Continuous (fun x : Space d => ∑ j, M i j * x j)
  exact continuous_finsetSum _
    (fun j _ => continuous_const.mul (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) j))

/-- A strict positivity cone is convex even without any rank hypothesis. -/
theorem cone_convex (M : Matrix (Fin r) (Fin d) ℝ) : Convex ℝ (cone M) := by
  change Convex ℝ {x : Space d | ∀ i, 0 < (M *ᵥ x) i}
  simp only [Set.ofPred_forall]
  apply convex_iInter
  intro i
  apply convex_halfSpace_gt
  constructor
  · intro x y
    change (M *ᵥ (WithLp.ofLp x + WithLp.ofLp y)) i = _
    rw [Matrix.mulVec_add]
    rfl
  · intro a x
    change (M *ᵥ (a • WithLp.ofLp x)) i = _
    rw [Matrix.mulVec_smul]
    rfl

/-- The cone corollary consumes the core theorem statement only. -/
theorem cone_of_core : CoreTheorem → ConeTheorem := by
  intro hcore d r hd _hr M hM S hS
  have hne := cone_nonempty M hM
  have hopen := cone_isOpen M
  have hconvex := cone_convex M
  exact ⟨hne, hopen, hconvex, (hcore d hd S hS (cone M) hne hopen hconvex).strong_bijection⟩

end MajorityDynamics.Analysis.ConditionalGaussian
