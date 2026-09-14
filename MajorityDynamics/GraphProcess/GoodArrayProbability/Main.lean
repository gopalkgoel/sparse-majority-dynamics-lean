import MajorityDynamics.GraphProcess.GoodArrayProbability.Point
import MajorityDynamics.GraphProcess.GoodArrays.Main

noncomputable section
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.GoodArrayProbability
open Universal
universe u

/-- The whole original good set has exponentially positive probability under
the actual row law and its exact-count conditioning. With the original
separation assumption this also bounds the literal history/count/κ/Γ₁ event.
All constants precede the varying graph size, density, coarse data and tilt. -/
theorem uniform_probability {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
      (∀ s t, |(q s t : ℝ)-p| ≤ T*p/Real.sqrt (p*N)) →
      Real.exp (-C*N) ≤ (RowArray.law y.part q).real (GoodArrays.E0 y T p) ∧
      Real.exp (-C*N) ≤
        (cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge)).real
          (GoodArrays.E0 y T p) ∧
      (GoodArrays.Separated y T p →
        Real.exp (-C*N) ≤ (RowArray.law y.part q).real
          (RowArray.history y.part ∩ RowArray.exactTotals y.part y.edge ∩
            {d | RowArray.Regular p d} ∩ {d | RowArray.Gamma y.part y.edge 1 p d})) := by
  obtain ⟨Cpoint, hCpoint, Npoint, hpoint⟩ := uniform_point n hθlo hθhi hT
  obtain ⟨Ccount, hCcount, Ncount, hcount⟩ := GoodArrays.uniform_cardinality n hθlo hθhi hT
  obtain ⟨Nreg, hreg⟩ := GoodArrays.uniform_regime n hθlo hθhi hT
  refine ⟨Ccount+Cpoint, add_pos hCcount hCpoint, max Npoint (max Ncount Nreg), ?_⟩
  intro N hN V inst hcard p hlo hhi y q hsizes hcounts htilt
  have hNp : Npoint ≤ N := (le_max_left _ _).trans hN
  have hNc : Ncount ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNr : Nreg ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hr := hreg N hNr V hcard p hlo hhi y hsizes hcounts
  have hx : 0 < p*N := by
    simpa only [hcard] using mul_pos hr.density_pos hr.card_pos
  let b : ℝ := Real.exp (-Cpoint*N)*(p*N)^(-(((2^(n+1)*N : ℕ) : ℝ)/2))
  have hb : 0 ≤ b := mul_nonneg (Real.exp_pos _).le (Real.rpow_pos_of_pos hx _).le
  have hpoints : ∀ d ∈ GoodArrays.E0 y T p, b ≤ (RowArray.law y.part q).real {d} := by
    intro d hd
    exact (hpoint N hNp V hcard p hlo hhi y q hsizes hcounts htilt d hd).1
  have hcardinal := hcount N hNc V hcard p hlo hhi y hsizes hcounts
  have htotal : Real.exp (-(Ccount+Cpoint)*N) ≤
      (RowArray.law y.part q).real (GoodArrays.E0 y T p) := by
    calc
      _ = (Real.exp (-Ccount*N)*(p*N)^(((2^(n+1)*N : ℕ) : ℝ)/2))*b :=
        (count_point_cancellation hx N (2^(n+1)*N)).symm
      _ ≤ ((GoodArrays.E0 y T p).card : ℝ)*b :=
        mul_le_mul_of_nonneg_right hcardinal hb
      _ ≤ _ := card_mul_point_le_event y q T p b hpoints
  refine ⟨htotal, htotal.trans (E0_le_conditioned y q T p), ?_⟩
  intro hsep
  apply htotal.trans
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro d hd
  exact ⟨⟨⟨GoodArrays.e0_history hT hr hsep hd,
    ((GoodArrays.mem_E0 y T p d).mp hd).1⟩,
    GoodArrays.e0_regular hT hr hd⟩, GoodArrays.e0_gamma_one hT hr hd⟩

end MajorityDynamics.GraphProcess.GoodArrayProbability
