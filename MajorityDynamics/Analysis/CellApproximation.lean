import MajorityDynamics.Analysis.FiniteCells

/-! # Comparing a cellwise expectation with the full continuous integral -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace MajorityDynamics.Analysis
variable {Ω ι : Type*} [MeasurableSpace Ω]

theorem cell_integral_error (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Finset ι) (cell : ι → Set Ω) (hm : ∀ a ∈ S, MeasurableSet (cell a))
    (hd : (S : Set ι).Pairwise (fun a b => Disjoint (cell a) (cell b)))
    (f : ι → ℝ) (F : Ω → ℝ) (hF : Integrable F μ)
    (B : Set Ω) (hB : MeasurableSet B) (ε K : ℝ) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (herr : ∀ a ∈ S, ∀ x ∈ cell a, |F x - f a| ≤ ε + K * B.indicator (fun _ => (1 : ℝ)) x) :
    |(∫ x, F x ∂μ) - ∫ x, cellObservable S cell f x ∂μ| ≤
      ε + K * μ.real B + ∫ x in (⋃ a ∈ S, cell a)ᶜ, |F x| ∂μ := by
  classical
  let E := ⋃ a ∈ S, cell a
  let g := cellObservable S cell f
  have hE : MeasurableSet E := S.measurableSet_biUnion hm
  have hg : Integrable g μ := integrable_cellObservable μ S cell hm f
  have hdiff : Integrable (fun x => F x - g x) μ := hF.sub hg
  have hbound : Integrable (fun x => ε + K * B.indicator (fun _ => (1 : ℝ)) x) μ :=
    (integrable_const ε).add (((integrable_const (1 : ℝ)).indicator hB).const_mul K)
  have hbound0 : ∀ x, 0 ≤ ε + K * B.indicator (fun _ => (1 : ℝ)) x := by
    intro x
    exact add_nonneg hε (mul_nonneg hK (Set.indicator_nonneg (fun _ _ => zero_le_one) x))
  have hon : |∫ x in E, F x - g x ∂μ| ≤ ε + K * μ.real B := by
    calc
      _ ≤ ∫ x in E, |F x - g x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x in E, ε + K * B.indicator (fun _ => (1 : ℝ)) x ∂μ := by
        apply integral_mono_ae hdiff.abs.integrableOn hbound.integrableOn
        filter_upwards [ae_restrict_mem hE] with x hx
        obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp hx
        rw [show g x = f a from cellObservable_on S cell hd f a ha x hxa]
        exact herr a ha x hxa
      _ ≤ ∫ x, ε + K * B.indicator (fun _ => (1 : ℝ)) x ∂μ :=
        setIntegral_le_integral hbound (ae_of_all μ hbound0)
      _ = _ := by
        rw [integral_add (integrable_const ε) (((integrable_const (1 : ℝ)).indicator hB).const_mul K),
          integral_const_mul, integral_indicator hB]
        simp
  have hoff : |∫ x in Eᶜ, F x - g x ∂μ| ≤ ∫ x in Eᶜ, |F x| ∂μ := by
    have heq : (∫ x in Eᶜ, F x - g x ∂μ) = ∫ x in Eᶜ, F x ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hE.compl] with x hx
      rw [show g x = 0 from cellObservable_off S cell f x hx, sub_zero]
    rw [heq]
    exact abs_integral_le_integral_abs
  rw [← integral_sub hF hg, ← integral_add_compl hE hdiff]
  exact (abs_add_le _ _).trans (add_le_add hon hoff)

theorem normalized_cell_integral_error (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Finset ι) (cell : ι → Set Ω) (hm : ∀ a ∈ S, MeasurableSet (cell a))
    (hd : (S : Set ι).Pairwise (fun a b => Disjoint (cell a) (cell b)))
    (hpos : 0 < μ.real (⋃ a ∈ S, cell a)) (f : ι → ℝ) (H : ℝ) (hf : ∀ a ∈ S, |f a| ≤ H)
    (F : Ω → ℝ) (hF : Integrable F μ) (B : Set Ω) (hB : MeasurableSet B)
    (ε K : ℝ) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (herr : ∀ a ∈ S, ∀ x ∈ cell a, |F x - f a| ≤ ε + K * B.indicator (fun _ => (1 : ℝ)) x) :
    |(∫ x, F x ∂μ) - normalizedCellExpectation μ S cell f| ≤
      ε + K * μ.real B + (∫ x in (⋃ a ∈ S, cell a)ᶜ, |F x| ∂μ) +
        H * μ.real (⋃ a ∈ S, cell a)ᶜ := by
  exact (abs_sub_le _ (∫ x, cellObservable S cell f x ∂μ) _).trans
    (add_le_add (cell_integral_error μ S cell hm hd f F hF B hB ε K hε hK herr)
      (cell_normalization_error μ S cell hm hd hpos f H hf))

end MajorityDynamics.Analysis
