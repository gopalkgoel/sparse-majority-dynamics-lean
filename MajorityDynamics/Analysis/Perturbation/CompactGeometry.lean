import MajorityDynamics.Analysis.Perturbation.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact

/-!
# Compact geometry for perturbing a strong bijection

Source: `latest/main.tex`, Appendix D.3, `thm:perturbed-bijection`.
A compact set inside the open target has a compact closed thickening on which
the inverse has a uniform Lipschitz bound. This construction also handles an
empty compact set and the whole-space target, without distance to a complement.
The prescribed approximation radius is exactly the maximum inverse norm plus
one whenever the compact set is nonempty.
-/

noncomputable section

open Set Metric

namespace MajorityDynamics.Analysis.Perturbation

variable {d : ℕ} {B K : Set (Space d)}

/-- A uniform compact neighborhood and inverse Lipschitz bound for D.3. -/
theorem compactControl (f : StrongBijection B) (hK : IsCompact K) (hKB : K ⊆ B) :
    CompactControl f K := by
  obtain ⟨r, hr, hVB⟩ := hK.exists_cthickening_subset_open f.isOpen_target hKB
  have hV : IsCompact (cthickening r K) := hK.cthickening
  obtain ⟨L, hL, hLip⟩ := f.lipschitz_bounds hV hVB
  refine ⟨cthickening r K, r, L, hV, self_subset_cthickening _, hVB, hr, hL, ?_, ?_⟩
  · intro y hy z hz
    exact mem_cthickening_of_dist_le z y r K hy (by simpa only [dist_eq_norm] using hz)
  · intro u hu v hv
    exact (hLip u hu v hv).2

/-- Every target inverse lies one unit inside the prescribed approximation ball. -/
theorem norm_inv_add_one_le_inverseRadius (f : StrongBijection B)
    (hK : IsCompact K) (hKB : K ⊆ B) {y : Space d} (hy : y ∈ K) :
    ‖f.invFun y‖ + 1 ≤ inverseRadius f K := by
  have hImage : IsCompact ((fun z => ‖f.invFun z‖) '' K) :=
    hK.image_of_continuousOn (f.smooth_inv.continuousOn.mono hKB).norm
  simpa only [inverseRadius, add_comm] using add_le_add_right
    (le_csSup (hImage.insert 0).bddAbove
      (mem_insert_of_mem 0 (mem_image_of_mem (fun z => ‖f.invFun z‖) hy))) 1

/-- The empty-target convention gives radius one. -/
@[simp]
theorem inverseRadius_empty (f : StrongBijection B) : inverseRadius f ∅ = 1 := by
  simp [inverseRadius]

/-- On a nonempty compact set, the radius is the paper's attained maximum plus one. -/
theorem inverseRadius_eq_max (f : StrongBijection B)
    (hK : IsCompact K) (hKB : K ⊆ B) (hne : K.Nonempty) :
    ∃ y ∈ K, inverseRadius f K = ‖f.invFun y‖ + 1 ∧
      ∀ z ∈ K, ‖f.invFun z‖ ≤ ‖f.invFun y‖ := by
  have hNorm : ContinuousOn (fun y => ‖f.invFun y‖) K :=
    (f.smooth_inv.continuousOn.mono hKB).norm
  obtain ⟨y, hy, hSup, hmax⟩ := hK.exists_sSup_image_eq_and_ge hne hNorm
  refine ⟨y, hy, ?_, hmax⟩
  rw [inverseRadius, csSup_insert (hK.image_of_continuousOn hNorm).bddAbove
    (hne.image (fun z => ‖f.invFun z‖)), hSup, sup_of_le_right (norm_nonneg _)]

end MajorityDynamics.Analysis.Perturbation
