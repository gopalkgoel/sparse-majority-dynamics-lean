import MajorityDynamics.GraphProcess.GoodArrayProbability.CentralBinomial
import MajorityDynamics.GraphProcess.GoodArrayProbability.CoordinateRegime
import MajorityDynamics.GraphProcess.GoodArrayProbability.Product

noncomputable section
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.GoodArrayProbability
open Universal
universe u

/-- Uniform lower bounds for every actual coordinate of every array in the original E0. -/
theorem uniform_coordinate_lower {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
      (∀ s t, |(q s t : ℝ)-p| ≤ T*p/Real.sqrt (p*N)) →
      ∀ d : RowArray.Ambient y.part, d ∈ GoodArrays.E0 y T p → ∀ v t,
        c/Real.sqrt (p*N) ≤ Binomial.Approximation.pointMass
          (Local.trials y.sizes (y.part v) t) (RowArray.naturalRows d v t)
          (q (y.part v) t) := by
  obtain ⟨c, hc, L, hL, hpoint⟩ := central_binomial_lower (coordinateConstant T)
    (coordinateConstant_pos hT).le
  obtain ⟨N₀, hN₀⟩ := uniform_coordinate_regime n hθlo hθhi hT hL
  refine ⟨c/2, by positivity, N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi y q hsizes hcounts htilt d hd v t
  obtain ⟨hq, hmean, hupper, hwindow⟩ :=
    hN₀ N hN V hcard p hlo hhi y q hsizes hcounts htilt d hd v t
  let μ : ℝ := (Local.trials y.sizes (y.part v) t : ℝ)*(q (y.part v) t : ℝ)
  have hμ : 0 < μ := by dsimp [μ]; linarith
  have hx : 0 < p*N := by dsimp [μ] at hμ; nlinarith
  have hs : Real.sqrt μ ≤ 2*Real.sqrt (p*N) := by
    have := Real.sq_sqrt hμ.le
    have := Real.sq_sqrt hx.le
    have := Real.sqrt_nonneg μ
    have := Real.sqrt_nonneg (p*N)
    change μ ≤ 2*p*N at hupper
    nlinarith
  calc
    (c/2)/Real.sqrt (p*N) = c/(2*Real.sqrt (p*N)) := by ring
    _ ≤ c/Real.sqrt μ := div_le_div_of_nonneg_left hc.le (Real.sqrt_pos.2 hμ) hs
    _ ≤ _ := hpoint _ _ _ hq hmean hwindow

/-- The complete point estimate, for both the original row law and its exact-count
conditioning. Constants precede all varying data; the exponent is literal real division. -/
theorem uniform_point {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
      (∀ s t, |(q s t : ℝ)-p| ≤ T*p/Real.sqrt (p*N)) →
      ∀ d : RowArray.Ambient y.part, d ∈ GoodArrays.E0 y T p →
        Real.exp (-C*N)*(p*N)^(-(((2^(n+1)*N : ℕ) : ℝ)/2)) ≤
          (RowArray.law y.part q).real {d} ∧
        Real.exp (-C*N)*(p*N)^(-(((2^(n+1)*N : ℕ) : ℝ)/2)) ≤
          (cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge)).real {d} := by
  obtain ⟨c, hc, N₁, h₁⟩ := uniform_coordinate_lower n hθlo hθhi hT
  obtain ⟨N₂, h₂⟩ := GoodArrays.uniform_regime n hθlo hθhi hT
  let C := (|Real.log c|+1)*(2^(n+1) : ℕ)
  refine ⟨C, by dsimp [C]; positivity, max N₁ N₂, ?_⟩
  intro N hN V inst hcard p hlo hhi y q hsizes hcounts htilt d hd
  have hreg := h₂ N ((le_max_right _ _).trans hN) V hcard p hlo hhi y hsizes hcounts
  have hx : 0 < p*N := by simpa only [hcard] using mul_pos hreg.density_pos hreg.card_pos
  have hprod := row_atom_of_coordinate_bound y q d
    (div_nonneg hc.le (Real.sqrt_nonneg _))
    (h₁ N ((le_max_left _ _).trans hN) V hcard p hlo hhi y q hsizes hcounts htilt d hd)
  rw [hcard] at hprod
  have hb := (coordinate_power_bound n N hc hx).trans hprod
  exact ⟨hb, hb.trans (row_atom_le_conditioned y q d ((GoodArrays.mem_E0 y T p d).mp hd).1)⟩

end MajorityDynamics.GraphProcess.GoodArrayProbability
