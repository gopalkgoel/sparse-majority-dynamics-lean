import MajorityDynamics.Universal.GaussianRows

/-!
# Ties and Gaussian null boundaries

The paper's mixed weak/strict events are encoded with the original tie rule.
Their equality with open cones is an almost-everywhere equality, and is proved
for the concrete Gaussian; it is never asserted as a literal set equality.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory Filter
open MajorityDynamics.Analysis

namespace MajorityDynamics.Universal

variable {n : ℕ}

theorem decision_iff_strict (a b : Bool) {z : ℝ} (hz : z ≠ 0) :
    decision a b z ↔ 0 < sign b * z := by simp [decision, hz]

theorem decision_complement (a : Bool) (z : ℝ) :
    decision a true z ↔ ¬decision a false z := by
  cases a <;> simp [decision]
  · exact ⟨fun h => ⟨h.le, h.ne⟩, fun h => lt_of_le_of_ne h.1 h.2⟩
  · exact ⟨fun h => h.elim le_of_lt le_of_eq, lt_or_eq_of_le⟩

theorem decision_measurable (a b : Bool) (r : Fin (n + 1)) :
    MeasurableSet {x : Row (n + 1) | decision a b (imbalance r x)} := by
  unfold decision
  exact ((isOpen_lt continuous_const
    (continuous_const.mul (imbalance_continuous r))).measurableSet).union
      ((isClosed_eq (imbalance_continuous r) continuous_const).measurableSet.inter
        (MeasurableSet.const _))

theorem historyEvent_measurable (s : History (n + 1)) : MeasurableSet (historyEvent s) := by
  unfold historyEvent
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun r => decision_measurable _ _ r.castSucc

theorem childEvent_measurable (s : History (n + 1)) (b : Bool) :
    MeasurableSet (childEvent s b) :=
  (historyEvent_measurable s).inter (decision_measurable _ _ _)

theorem childEvent_disjoint (s : History (n + 1)) :
    Disjoint (childEvent s false) (childEvent s true) := by
  rw [Set.disjoint_left]
  intro x hx hy
  exact (decision_complement (last s) _).mp hy.2 hx.2

theorem childEvent_union (s : History (n + 1)) :
    childEvent s false ∪ childEvent s true = historyEvent s := by
  classical
  ext x
  simp only [childEvent, mem_union, mem_inter_iff, mem_ofPred]
  rw [decision_complement]
  by_cases h : decision (last s) false (imbalance (Fin.last n) x) <;> simp [h]

theorem imbalance_ne_zero_ae (ν : History (n + 1) → ℝ) (hν : ∀ t, 0 < ν t)
    (γ : Row (n + 1)) (r : Fin (n + 1)) :
    ∀ᵐ x ∂rowLaw ν γ, imbalance r x ≠ 0 := by
  have hnull : rowLaw ν γ {x | imbalance r x = 0} = 0 := by
    apply ConditionalGaussian.gaussianLaw_absolutelyContinuous _ (covariance_posDef ν hν) γ
    simp_rw [imbalance_eq_inner]
    exact ConditionalGaussian.volume_inner_level_eq_zero _ (characterVector_ne_zero r) 0
  simpa only [ae_iff, not_not] using hnull

theorem historyEvent_ae_eq_cone (s : History (n + 1)) (ν : History (n + 1) → ℝ)
    (hν : ∀ t, 0 < ν t) (γ : Row (n + 1)) :
    historyEvent s =ᵐ[rowLaw ν γ] historyCone s := by
  have hall : ∀ᵐ x ∂rowLaw ν γ, ∀ r : Fin (n + 1), imbalance r x ≠ 0 :=
    (ae_all_iff).mpr (imbalance_ne_zero_ae ν hν γ)
  filter_upwards [hall] with x hx
  change (x ∈ historyEvent s) = (x ∈ historyCone s)
  apply propext
  rw [mem_historyCone]
  exact forall_congr' fun r => decision_iff_strict _ _ (hx r.castSucc)

theorem childEvent_ae_eq_cone (s : History (n + 1)) (b : Bool)
    (ν : History (n + 1) → ℝ) (hν : ∀ t, 0 < ν t) (γ : Row (n + 1)) :
    childEvent s b =ᵐ[rowLaw ν γ] childCone s b := by
  filter_upwards [historyEvent_ae_eq_cone s ν hν γ,
    imbalance_ne_zero_ae ν hν γ (Fin.last n)] with x hx hz
  change (x ∈ historyEvent s) = (x ∈ historyCone s) at hx
  apply propext
  change (x ∈ historyEvent s ∧ decision _ _ _) ↔ (x ∈ historyCone s ∧ _)
  rw [hx, decision_iff_strict _ _ hz]
  rfl

theorem condition_congr_set {d : ℕ} (ρ : Measure (ConditionalGaussian.Space d))
    {A B : Set (ConditionalGaussian.Space d)} (h : A =ᵐ[ρ] B) :
    ConditionalGaussian.condition ρ A = ConditionalGaussian.condition ρ B := by
  rw [ConditionalGaussian.condition, ConditionalGaussian.condition,
    measure_congr h, Measure.restrict_congr_set h]

theorem history_condition_eq (s : History (n + 1)) (ν : History (n + 1) → ℝ)
    (hν : ∀ t, 0 < ν t) (γ : Row (n + 1)) :
    ConditionalGaussian.condition (rowLaw ν γ) (historyEvent s) =
      ConditionalGaussian.condition (rowLaw ν γ) (historyCone s) :=
  condition_congr_set _ (historyEvent_ae_eq_cone s ν hν γ)

theorem child_condition_eq (s : History (n + 1)) (b : Bool)
    (ν : History (n + 1) → ℝ) (hν : ∀ t, 0 < ν t) (γ : Row (n + 1)) :
    ConditionalGaussian.condition (rowLaw ν γ) (childEvent s b) =
      ConditionalGaussian.condition (rowLaw ν γ) (childCone s b) :=
  condition_congr_set _ (childEvent_ae_eq_cone s b ν hν γ)

end MajorityDynamics.Universal
