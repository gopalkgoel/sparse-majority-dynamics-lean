import MajorityDynamics.Analysis.ApproximateFiniteTilt
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Finite disjoint cells as an actual measurable observable -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace MajorityDynamics.Analysis

variable {Ω ι : Type*}

def cellObservable (S : Finset ι) (cell : ι → Set Ω) (f : ι → ℝ) (x : Ω) : ℝ :=
  ∑ a ∈ S, (cell a).indicator (fun _ => f a) x

theorem cellObservable_on (S : Finset ι) (cell : ι → Set Ω)
    (hd : (S : Set ι).Pairwise (fun a b => Disjoint (cell a) (cell b))) (f : ι → ℝ)
    (a : ι) (ha : a ∈ S) (x : Ω) (hx : x ∈ cell a) : cellObservable S cell f x = f a := by
  classical
  rw [cellObservable, Finset.sum_eq_single a]
  · exact Set.indicator_of_mem hx _
  · intro b hb hba
    apply Set.indicator_of_notMem
    intro hxb
    exact Set.disjoint_left.mp (hd ha hb hba.symm) hx hxb
  · exact fun h => False.elim (h ha)

theorem cellObservable_off (S : Finset ι) (cell : ι → Set Ω) (f : ι → ℝ) (x : Ω)
    (hx : x ∉ ⋃ a ∈ S, cell a) : cellObservable S cell f x = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro a ha
  exact Set.indicator_of_notMem (fun h => hx (Set.mem_iUnion₂.mpr ⟨a, ha, h⟩)) _

theorem cellObservable_abs_le (S : Finset ι) (cell : ι → Set Ω)
    (hd : (S : Set ι).Pairwise (fun a b => Disjoint (cell a) (cell b))) (f : ι → ℝ)
    (H : ℝ) (hH : 0 ≤ H) (hf : ∀ a ∈ S, |f a| ≤ H) (x : Ω) :
    |cellObservable S cell f x| ≤ H := by
  classical
  by_cases hx : x ∈ ⋃ a ∈ S, cell a
  · obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp hx
    rw [cellObservable_on S cell hd f a ha x hxa]
    exact hf a ha
  · rw [cellObservable_off S cell f x hx, abs_zero]
    exact hH

variable [MeasurableSpace Ω]

theorem integral_cellObservable (μ : Measure Ω) [IsFiniteMeasure μ]
    (S : Finset ι) (cell : ι → Set Ω) (hm : ∀ a ∈ S, MeasurableSet (cell a)) (f : ι → ℝ) :
    (∫ x, cellObservable S cell f x ∂μ) = ∑ a ∈ S, μ.real (cell a) * f a := by
  classical
  simp only [cellObservable]
  rw [integral_finsetSum _ (fun a ha => (integrable_const (f a)).indicator (hm a ha))]
  apply Finset.sum_congr rfl
  intro a ha
  rw [integral_indicator (hm a ha), setIntegral_const, smul_eq_mul]

theorem integrable_cellObservable (μ : Measure Ω) [IsFiniteMeasure μ]
    (S : Finset ι) (cell : ι → Set Ω) (hm : ∀ a ∈ S, MeasurableSet (cell a)) (f : ι → ℝ) :
    Integrable (cellObservable S cell f) μ :=
  integrable_finsetSum S fun a ha => (integrable_const (f a)).indicator (hm a ha)

def normalizedCellExpectation (μ : Measure Ω) (S : Finset ι) (cell : ι → Set Ω) (f : ι → ℝ) : ℝ :=
  FiniteTiltEstimate.average S (FiniteTiltEstimate.normalize S (fun a => μ.real (cell a))) f

theorem cell_normalization_error (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Finset ι) (cell : ι → Set Ω) (hm : ∀ a ∈ S, MeasurableSet (cell a))
    (hd : (S : Set ι).Pairwise (fun a b => Disjoint (cell a) (cell b)))
    (hpos : 0 < μ.real (⋃ a ∈ S, cell a)) (f : ι → ℝ) (H : ℝ) (hf : ∀ a ∈ S, |f a| ≤ H) :
    |(∫ x, cellObservable S cell f x ∂μ) - normalizedCellExpectation μ S cell f| ≤
      H * μ.real (⋃ a ∈ S, cell a)ᶜ := by
  have hsum : μ.real (⋃ a ∈ S, cell a) = ∑ a ∈ S, μ.real (cell a) :=
    measureReal_biUnion_finset hd hm (fun _ _ => measure_ne_top _ _)
  have hsum0 : 0 < ∑ a ∈ S, μ.real (cell a) := hsum ▸ hpos
  have hnorm := FiniteTiltEstimate.abs_average_le S
    (FiniteTiltEstimate.normalize S (fun a => μ.real (cell a))) f
    (fun _ _ => div_nonneg measureReal_nonneg hsum0.le)
    (FiniteTiltEstimate.normalize_sum S _ hsum0.ne') H hf
  have hid : (∫ x, cellObservable S cell f x ∂μ) =
      normalizedCellExpectation μ S cell f * μ.real (⋃ a ∈ S, cell a) := by
    rw [integral_cellObservable μ S cell hm f, hsum]
    simp only [normalizedCellExpectation, FiniteTiltEstimate.average, FiniteTiltEstimate.normalize,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    field_simp
  have htotal : μ.real (⋃ a ∈ S, cell a) + μ.real (⋃ a ∈ S, cell a)ᶜ = 1 := by
    simpa using measureReal_add_measureReal_compl (μ := μ) (S.measurableSet_biUnion hm)
  rw [hid, ← mul_sub_one, abs_mul,
    show μ.real (⋃ a ∈ S, cell a) - 1 = -μ.real (⋃ a ∈ S, cell a)ᶜ by linarith,
    abs_neg, abs_of_nonneg measureReal_nonneg]
  exact mul_le_mul_of_nonneg_right hnorm measureReal_nonneg

end MajorityDynamics.Analysis
