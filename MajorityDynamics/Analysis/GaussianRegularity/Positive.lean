import MajorityDynamics.Analysis.GaussianRegularity.Basic
import MajorityDynamics.Analysis.ConditionalGaussian.Cones
import MajorityDynamics.Analysis.ConditionalGaussian.GaussianDensity

/-!
# Positive probabilities for shifted Gaussian conditioning events

The positivity part of Appendix E, Lemma E.2. Full row rank supplies a point
strictly inside every shifted event. The actual nondegenerate Gaussian charges
this open set. Compactness then turns continuity into a uniform positive bound.
The arguments also cover zero rows and empty compact parameter sets.
-/

noncomputable section

open Set MeasureTheory

namespace MajorityDynamics.Analysis.GaussianRegularity

open ConditionalGaussian

variable {d r : ℕ}

/-- The strict interior event, used only as a positive-mass subset. -/
def strictEvent (M : Matrix (Fin r) (Fin d) ℝ) (u : Space r) : Set (Space d) :=
  {x | ∀ i, -u i < ∑ j, M i j * x j}

theorem strictEvent_subset_event (M : Matrix (Fin r) (Fin d) ℝ) (u : Space r) :
    strictEvent M u ⊆ event M u := fun _ hx i => (hx i).le

theorem strictEvent_nonempty (M : Matrix (Fin r) (Fin d) ℝ)
    (hM : M.rank = r) (u : Space r) : (strictEvent M u).Nonempty := by
  obtain ⟨x, hx⟩ := mulVec_surjective_of_rank M hM (fun i => -u i + 1)
  refine ⟨WithLp.toLp 2 x, ?_⟩
  intro i
  change -u i < (M.mulVec x) i
  rw [hx]
  linarith

theorem strictEvent_isOpen (M : Matrix (Fin r) (Fin d) ℝ) (u : Space r) :
    IsOpen (strictEvent M u) := by
  unfold strictEvent
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_lt continuous_const
  exact continuous_finsetSum _
    (fun j _ => continuous_const.mul (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) j))

theorem event_mass_pos (M : Matrix (Fin r) (Fin d) ℝ) (hM : M.rank = r)
    (p : Parameters d r) (hp : positiveVariance p) :
    0 < law p (event M p.2) := by
  have hS : (Matrix.diagonal (fun i => p.1.2 i)).PosDef :=
    Matrix.posDef_diagonal_iff.mpr hp
  exact (gaussianLaw_mass_pos _ hS p.1.1 (strictEvent M p.2)
    (strictEvent_isOpen M p.2) (strictEvent_nonempty M hM p.2)).trans_le
      (measure_mono (strictEvent_subset_event M p.2))

theorem mass_pos (M : Matrix (Fin r) (Fin d) ℝ) (hM : M.rank = r)
    (p : Parameters d r) (hp : positiveVariance p) : 0 < mass M p := by
  exact ENNReal.toReal_pos (ne_of_gt (event_mass_pos M hM p hp))
    (ne_of_lt (gaussianLaw_mass_lt_top _ _ _))

/-- Uniform positivity on any compact parameter set once continuity is known.
The analytic continuity proof is supplied separately by the regularity theorem. -/
theorem compact_mass_lower_bound (M : Matrix (Fin r) (Fin d) ℝ)
    (hM : M.rank = r) (P : Set (Parameters d r)) (hP : IsCompact P)
    (hv : ∀ p ∈ P, positiveVariance p) (hc : ContinuousOn (mass M) P) :
    ∃ c : ℝ, 0 < c ∧ ∀ p ∈ P, c ≤ mass M p := by
  rcases P.eq_empty_or_nonempty with h | h
  · exact ⟨1, zero_lt_one, by simp [h]⟩
  · obtain ⟨p, hp, hmin⟩ := hP.exists_isMinOn h hc
    exact ⟨mass M p, mass_pos M hM p (hv p hp), hmin⟩

end MajorityDynamics.Analysis.GaussianRegularity
