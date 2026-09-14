import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Strong bijections: Lipschitz bounds on compact sets

Source: `latest/main.tex`, Appendix D, `def:strong-bijection` and
`lem:strong-bijection-lipschitz` (labels are stable when numbering changes).

The paper uses Euclidean space. The proof works for real normed spaces, so we
prove it in that generality and provide a Euclidean specialization below.
The inverse is an ambient function whose values outside `B` are irrelevant.
There is no convexity assumption on either `B` or the compact set `K`.
-/

open Set Filter
open scoped Topology ContDiff

namespace MajorityDynamics

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A `C¹` map on an open set is Lipschitz on each compact subset.
We pass through local Lipschitz continuity so that `K` need not be convex. -/
theorem lipschitzOnWith_of_contDiffOn_open
    {h : E → F} {W K : Set E} (hW : IsOpen W)
    (hh : ContDiffOn ℝ 1 h W) (hK : IsCompact K) (hKW : K ⊆ W) :
    ∃ C, LipschitzOnWith C h K := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
  intro x hx
  obtain ⟨C, U, hU, hLip⟩ :=
    (hh.contDiffAt (hW.mem_nhds (hKW hx))).exists_lipschitzOnWith
  exact ⟨C, U, mem_nhdsWithin_of_mem_nhds hU, hLip⟩

/-- The paper's smooth bijection onto an open set, represented by a map and
its inverse. The inverse identities and range condition encode bijectivity;
smoothness is imposed on the forward map everywhere and on the inverse in `B`.
-/
structure StrongBijection (B : Set E) where
  toFun : E → E
  invFun : E → E
  isOpen_target : IsOpen B
  mapsTo : MapsTo toFun univ B
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y ∈ B, toFun (invFun y) = y
  smooth : ContDiff ℝ ∞ toFun
  smooth_inv : ContDiffOn ℝ ∞ invFun B

namespace StrongBijection

variable {B : Set E}

/-- The range and inverse fields really give a bijection onto `B`. -/
theorem bijOn (f : StrongBijection B) : BijOn f.toFun univ B := by
  refine ⟨f.mapsTo, ?_, ?_⟩
  · intro x _ y _ hxy
    calc
      x = f.invFun (f.toFun x) := (f.left_inv x).symm
      _ = f.invFun (f.toFun y) := congrArg f.invFun hxy
      _ = y := f.left_inv y
  · intro y hy
    exact ⟨f.invFun y, mem_univ _, f.right_inv y hy⟩

/-- `lem:strong-bijection-lipschitz`: on any compact `K ⊆ B`, the inverse
has both upper and lower Lipschitz bounds with one constant `L ≥ 1`.

The upper bound comes from the inverse on `K`. For the lower bound, apply
the same compact-set result to the forward map on the compact image `invFun '' K`.
-/
theorem lipschitz_bounds (f : StrongBijection B)
    {K : Set E} (hK : IsCompact K) (hKB : K ⊆ B) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ y ∈ K, ∀ z ∈ K,
      L⁻¹ * ‖y - z‖ ≤ ‖f.invFun y - f.invFun z‖ ∧
      ‖f.invFun y - f.invFun z‖ ≤ L * ‖y - z‖ := by
  -- First control the inverse on K.
  obtain ⟨Cinv, hInv⟩ := lipschitzOnWith_of_contDiffOn_open
    f.isOpen_target (f.smooth_inv.of_le (by simp)) hK hKB
  -- Its image is compact because the inverse is continuous on B.
  have hImage : IsCompact (f.invFun '' K) :=
    hK.image_of_continuousOn (f.smooth_inv.continuousOn.mono hKB)
  obtain ⟨Cfwd, hFwd⟩ := lipschitzOnWith_of_contDiffOn_open
    isOpen_univ ((f.smooth.of_le (by simp)).contDiffOn) hImage (subset_univ _)
  -- Enlarge both bounds to a single positive real constant.
  let L : ℝ := max (max (Cinv : ℝ) (Cfwd : ℝ)) 1
  have hL : 1 ≤ L := le_max_right _ _
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hInvL : (Cinv : ℝ) ≤ L := (le_max_left _ _).trans (le_max_left _ _)
  have hFwdL : (Cfwd : ℝ) ≤ L := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨L, hL, ?_⟩
  intro y hy z hz
  have hUpper : ‖f.invFun y - f.invFun z‖ ≤ L * ‖y - z‖ := by
    calc
      ‖f.invFun y - f.invFun z‖ ≤ (Cinv : ℝ) * ‖y - z‖ := by
        simpa only [dist_eq_norm] using hInv.dist_le_mul y hy z hz
      _ ≤ L * ‖y - z‖ := mul_le_mul_of_nonneg_right hInvL (norm_nonneg _)
  have hReverse : ‖y - z‖ ≤ L * ‖f.invFun y - f.invFun z‖ := by
    calc
      ‖y - z‖ ≤ (Cfwd : ℝ) * ‖f.invFun y - f.invFun z‖ := by
        simpa only [dist_eq_norm, f.right_inv y (hKB hy), f.right_inv z (hKB hz)]
          using hFwd.dist_le_mul (f.invFun y) (mem_image_of_mem f.invFun hy)
            (f.invFun z) (mem_image_of_mem f.invFun hz)
      _ ≤ L * ‖f.invFun y - f.invFun z‖ :=
        mul_le_mul_of_nonneg_right hFwdL (norm_nonneg _)
  refine ⟨?_, hUpper⟩
  have hDiv : ‖y - z‖ / L ≤ ‖f.invFun y - f.invFun z‖ :=
    (div_le_iff₀ hLpos).2 (by simpa only [mul_comm] using hReverse)
  simpa only [div_eq_mul_inv, mul_comm] using hDiv

/-- The identity is a simple example of a strong bijection. -/
def identity : StrongBijection (univ : Set E) where
  toFun := id
  invFun := id
  isOpen_target := isOpen_univ
  mapsTo := fun _ _ => mem_univ _
  left_inv := fun _ => rfl
  right_inv := fun _ _ => rfl
  smooth := contDiff_id
  smooth_inv := contDiff_id.contDiffOn

end StrongBijection

/-- The manuscript's Euclidean version, with the usual Euclidean norm.
It also holds in dimension zero, so no `1 ≤ d` hypothesis is needed. -/
theorem strong_bijection_lipschitz {d : ℕ}
    {B K : Set (EuclideanSpace ℝ (Fin d))}
    (f : StrongBijection B) (hK : IsCompact K) (hKB : K ⊆ B) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ y ∈ K, ∀ z ∈ K,
      L⁻¹ * ‖y - z‖ ≤ ‖f.invFun y - f.invFun z‖ ∧
      ‖f.invFun y - f.invFun z‖ ≤ L * ‖y - z‖ :=
  f.lipschitz_bounds hK hKB

end MajorityDynamics
