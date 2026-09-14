import MajorityDynamics.Universal.Main

/-!
# Joint independence of the full Gaussian array

The row sampling construction realizes the paper's independent family indexed
by every ordered pair of histories. The proof first identifies its joint law
on measurable coordinate rectangles.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory

namespace MajorityDynamics.Universal

variable {n : ℕ}

/-- Flattening the row array has exactly the product of all prescribed normal laws. -/
theorem arrayLaw_all_coordinates (ν : History (n + 1) → ℝ) (hν : ∀ t, 0 < ν t)
    (γ : History (n + 1) → Row (n + 1)) :
    MeasurePreserving
      (fun W : History (n + 1) → Row (n + 1) =>
        fun p : History (n + 1) × History (n + 1) => W p.1 p.2)
      (arrayLaw ν γ)
      (Measure.pi (fun p : History (n + 1) × History (n + 1) =>
        gaussianReal (γ p.1 p.2) (ν p.2).toNNReal)) where
  measurable := by fun_prop
  map_eq := by
    symm
    apply Measure.pi_eq
    intro sets hsets
    rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hsets)]
    have hpre :
        (fun W : History (n + 1) → Row (n + 1) =>
          fun p : History (n + 1) × History (n + 1) => W p.1 p.2) ⁻¹' (univ.pi sets) =
        univ.pi (fun s => ⋂ t, (fun x : Row (n + 1) => x t) ⁻¹' sets (s, t)) := by
      ext W
      simp only [mem_preimage, mem_pi, mem_univ, forall_true_left, Prod.forall,
        mem_iInter]
    rw [hpre, arrayLaw, Measure.pi_pi, Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro s _
    have hr := (rowLaw_independent_coordinates ν hν (γ s)).measure_inter_preimage_eq_mul
      Finset.univ (sets := fun t => sets (s, t)) (fun t _ => hsets (s, t))
    simp only [Finset.mem_univ, iInter_true] at hr
    rw [hr]
    apply Finset.prod_congr rfl
    intro t _
    exact (rowLaw_coordinate ν hν (γ s) t).measure_preimage (hsets (s, t)).nullMeasurableSet

/-- Joint, rather than only pairwise, independence of all array coordinates. -/
theorem arrayLaw_independent_coordinates (ν : History (n + 1) → ℝ)
    (hν : ∀ t, 0 < ν t) (γ : History (n + 1) → Row (n + 1)) :
    iIndepFun
      (fun (p : History (n + 1) × History (n + 1))
        (W : History (n + 1) → Row (n + 1)) => W p.1 p.2) (arrayLaw ν γ) := by
  let : IsProbabilityMeasure (arrayLaw ν γ) := by unfold arrayLaw; infer_instance
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun p : History (n + 1) × History (n + 1) =>
      (arrayLaw_coordinate ν hν γ p.1 p.2).measurable.aemeasurable)).2
  rw [(arrayLaw_all_coordinates ν hν γ).map_eq]
  congr 1
  funext p
  exact (arrayLaw_coordinate ν hν γ p.1 p.2).map_eq.symm

/-- The concrete all-level array has the full joint independence stipulated in §4. -/
theorem dayArrayLaw_independent_coordinates (n : ℕ) :
    iIndepFun
      (fun (p : History (n + 1) × History (n + 1))
        (W : History (n + 1) → Row (n + 1)) => W p.1 p.2) (dayArrayLaw n) :=
  arrayLaw_independent_coordinates (ν n) (ν_positive n) (γ n)

end MajorityDynamics.Universal
