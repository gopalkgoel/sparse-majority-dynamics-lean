import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Covariance

/-!
# Conditioning on an independent history event

The Gaussian variables used in §4 are independent under the original Gaussian
law. These lemmas transport that independence and their laws through the
restriction to a positive-probability event determined by the history variables.
They do not assert that the conditioned history law is Gaussian.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace MajorityDynamics.Analysis.GaussianSplit

variable {Ω A H : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  [MeasurableSpace H] {ρ : Measure Ω} [IsFiniteMeasure ρ]
  {X : Ω → A} {history : Ω → H} {E : Set H}

/-- An event of a variable independent of the history has its original
probability after conditioning on a positive-probability history event. -/
theorem cond_preimage_of_indepFun
    (hXH : IndepFun X history ρ) (hH : Measurable history)
    (hE : MeasurableSet E) (hpos : ρ (history ⁻¹' E) ≠ 0)
    (S : Set A) (hS : MeasurableSet S) :
    (cond ρ (history ⁻¹' E)) (X ⁻¹' S) = ρ (X ⁻¹' S) := by
  rw [cond_apply (hH hE)]
  rw [Set.inter_comm, hXH.measure_inter_preimage_eq_mul S E hS hE]
  rw [mul_left_comm, ENNReal.inv_mul_cancel hpos (measure_ne_top ρ _), mul_one]

/-- Conditioning on history preserves the full law of every independent
variable, including a tuple of jointly independent residuals. -/
theorem map_cond_preimage_of_indepFun
    (hXH : IndepFun X history ρ) (hX : Measurable X) (hH : Measurable history)
    (hE : MeasurableSet E) (hpos : ρ (history ⁻¹' E) ≠ 0) :
    (cond ρ (history ⁻¹' E)).map X = ρ.map X := by
  ext S hS
  rw [Measure.map_apply hX hS, Measure.map_apply hX hS]
  exact cond_preimage_of_indepFun hXH hH hE hpos S hS

/-- The residual and history remain independent after conditioning on an
event determined by the history. -/
theorem indepFun_cond_preimage_of_indepFun
    (hXH : IndepFun X history ρ) (hH : Measurable history)
    (hE : MeasurableSet E) (hpos : ρ (history ⁻¹' E) ≠ 0) :
    IndepFun X history (cond ρ (history ⁻¹' E)) := by
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro S T hS hT
  rw [cond_preimage_of_indepFun hXH hH hE hpos S hS,
    cond_apply (hH hE), cond_apply (hH hE)]
  have hset : history ⁻¹' E ∩ (X ⁻¹' S ∩ history ⁻¹' T) =
      X ⁻¹' S ∩ history ⁻¹' (E ∩ T) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    tauto
  rw [hset, hXH.measure_inter_preimage_eq_mul S (E ∩ T) hS (hE.inter hT),
    Set.preimage_inter]
  ac_rfl

/-- Every measurable scalar statistic of an independent variable has the same
mean after conditioning on the history. -/
theorem integral_comp_cond_preimage_of_indepFun
    (hXH : IndepFun X history ρ) (hX : Measurable X) (hH : Measurable history)
    (hE : MeasurableSet E) (hpos : ρ (history ⁻¹' E) ≠ 0)
    {f : A → ℝ} (hf : Measurable f) :
    (∫ ω, f (X ω) ∂cond ρ (history ⁻¹' E)) = ∫ ω, f (X ω) ∂ρ := by
  rw [← integral_map hX.aemeasurable hf.aestronglyMeasurable,
    map_cond_preimage_of_indepFun hXH hX hH hE hpos,
    integral_map hX.aemeasurable hf.aestronglyMeasurable]

/-- In particular, the conditional mean of an independent scalar residual is
its original mean. -/
theorem integral_cond_preimage_of_indepFun
    {X : Ω → ℝ} (hXH : IndepFun X history ρ) (hX : Measurable X)
    (hH : Measurable history) (hE : MeasurableSet E)
    (hpos : ρ (history ⁻¹' E) ≠ 0) :
    (∫ ω, X ω ∂cond ρ (history ⁻¹' E)) = ∫ ω, X ω ∂ρ :=
  integral_comp_cond_preimage_of_indepFun hXH hX hH hE hpos measurable_id

/-- A centered residual independent of the variables determining an event has
zero conditional mean on that event. The history can include the final
Gaussian residual, so this also applies to the child event. -/
theorem integral_cond_preimage_eq_zero_of_indepFun
    {X : Ω → ℝ} (hXH : IndepFun X history ρ) (hX : Measurable X)
    (hH : Measurable history) (hE : MeasurableSet E)
    (hpos : ρ (history ⁻¹' E) ≠ 0) (hmean : ∫ ω, X ω ∂ρ = 0) :
    ∫ ω, X ω ∂cond ρ (history ⁻¹' E) = 0 := by
  rw [integral_cond_preimage_of_indepFun hXH hX hH hE hpos, hmean]

/-- Conditioning preserves covariances within an independent tuple. -/
theorem covariance_comp_cond_preimage_of_indepFun
    (hXH : IndepFun X history ρ) (hX : Measurable X) (hH : Measurable history)
    (hE : MeasurableSet E) (hpos : ρ (history ⁻¹' E) ≠ 0)
    {f g : A → ℝ} (hf : Measurable f) (hg : Measurable g) :
    covariance (f ∘ X) (g ∘ X) (cond ρ (history ⁻¹' E)) =
      covariance (f ∘ X) (g ∘ X) ρ := by
  rw [← covariance_map hf.aestronglyMeasurable hg.aestronglyMeasurable hX.aemeasurable,
    map_cond_preimage_of_indepFun hXH hX hH hE hpos,
    covariance_map hf.aestronglyMeasurable hg.aestronglyMeasurable hX.aemeasurable]

/-- Specialization to the covariance of the two coordinates of an independent
pair of scalar residuals. -/
theorem covariance_cond_preimage_of_indepFun
    {X Y : Ω → ℝ} (hXYH : IndepFun (fun ω ↦ (X ω, Y ω)) history ρ)
    (hX : Measurable X) (hY : Measurable Y) (hH : Measurable history)
    (hE : MeasurableSet E) (hpos : ρ (history ⁻¹' E) ≠ 0) :
    covariance X Y (cond ρ (history ⁻¹' E)) = covariance X Y ρ :=
  covariance_comp_cond_preimage_of_indepFun hXYH (hX.prodMk hY) hH hE hpos
    measurable_fst measurable_snd

omit [IsFiniteMeasure ρ] in
/-- Finite moments survive conditioning on a positive-probability event. -/
theorem memLp_cond {V : Type*} [TopologicalSpace V] [ContinuousENorm V]
    {f : Ω → V} {p : ℝ≥0∞} {S : Set Ω}
    (hf : MemLp f p ρ) (hpos : ρ S ≠ 0) : MemLp f p (cond ρ S) :=
  (hf.restrict S).smul_measure (ENNReal.inv_ne_top.mpr hpos)

/-- An independent residual has zero covariance with every square-integrable
scalar statistic of the conditioned history. -/
theorem covariance_cond_preimage_eq_zero_of_indepFun
    {X : Ω → ℝ} (hXH : IndepFun X history ρ) (hH : Measurable history)
    (hE : MeasurableSet E) (hpos : ρ (history ⁻¹' E) ≠ 0)
    {g : H → ℝ} (hg : Measurable g)
    (hX : MemLp X 2 ρ) (hgH : MemLp (g ∘ history) 2 ρ) :
    covariance X (g ∘ history) (cond ρ (history ⁻¹' E)) = 0 := by
  have hind := (indepFun_cond_preimage_of_indepFun hXH hH hE hpos).comp measurable_id hg
  exact hind.covariance_eq_zero (memLp_cond hX hpos) (memLp_cond hgH hpos)

end MajorityDynamics.Analysis.GaussianSplit
