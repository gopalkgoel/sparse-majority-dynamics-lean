import MajorityDynamics.GraphProcess.RowGamma.Conditioning

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.FiberTransference

/-- Finite-measure Bayes comparison. The good set carries at least half the
reference history mass; the exceptional part is controlled in the target law. -/
theorem bayes_transfer {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (H I J E : Set Ω) (hE : MeasurableSet E) (hJ : MeasurableSet J)
    {c ε : ℝ} (hc : 0 < c) (hI : 0 < ν.real I)
    (hhalf : ν.real I / 2 ≤ ν.real (H ∩ J))
    (hlower : ν.real (H ∩ J) ≤ c * μ.real (H ∩ J))
    (hupper : μ.real (H ∩ (E ∩ J)) ≤ c * ν.real (I ∩ E))
    (hbad : (cond μ H).real Jᶜ ≤ ε) :
    (cond μ H).real E ≤ ε + (2*c^2)*(cond ν I).real E := by
  have hm : 0 < μ.real H := by
    have hmono : μ.real (H ∩ J) ≤ μ.real H := measureReal_mono inter_subset_left
    nlinarith
  have hden : ν.real I ≤ (2*c)*μ.real H := by
    have hmono : μ.real (H ∩ J) ≤ μ.real H := measureReal_mono inter_subset_left
    nlinarith
  have hsplit : E ⊆ Jᶜ ∪ (E ∩ J) := by
    intro x hx
    by_cases hj : x ∈ J
    · exact Or.inr ⟨hx,hj⟩
    · exact Or.inl hj
  have hg : (cond μ H).real (E ∩ J) ≤ (2*c^2)*(cond ν I).real E := by
    rw [RowExactTotals.conditioned_real_eq_div μ H _ (hE.inter hJ),
      RowExactTotals.conditioned_real_eq_div ν I _ hE]
    apply (div_le_iff₀ hm).2
    apply hupper.trans
    have hv : 0 ≤ ν.real (I ∩ E) := measureReal_nonneg
    have hr : ν.real (I ∩ E) ≤
        (ν.real (I ∩ E) / ν.real I) * ((2*c)*μ.real H) := by
      calc
        _ = (ν.real (I ∩ E) / ν.real I) * ν.real I := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hden (div_nonneg hv hI.le)
    nlinarith [mul_le_mul_of_nonneg_left hr hc.le]
  exact (measureReal_mono hsplit).trans
    ((measureReal_union_le _ _).trans (add_le_add hbad hg))

end MajorityDynamics.GraphProcess.FiberTransference
