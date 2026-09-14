import MajorityDynamics.GraphProcess.GoodArrays.Preparation
import MajorityDynamics.GraphProcess.GoodArrays.Counting
import MajorityDynamics.GraphProcess.GoodArrays.Membership
import MajorityDynamics.GraphProcess.AutomaticGraphicality.Main
import MajorityDynamics.GraphProcess.BlockPairLaws.Atoms

noncomputable section
open scoped BigOperators Classical
open MeasureTheory
namespace MajorityDynamics.GraphProcess.GoodArrays
open Universal
universe u
variable {V : Type*} [Fintype V] {n : ℕ}

theorem E0_nonempty (y : Local.CoarseData V n) {T p : ℝ}
    (hT : 1 < T) (hreg : Regime y T p) : (E0 y T p).Nonempty := by
  have hlower : 0 < Real.exp (-countingRate n T * Fintype.card V) *
      (p*Fintype.card V)^(((labelCount n*Fintype.card V : ℕ) : ℝ)/2) :=
    mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (mul_pos hreg.density_pos hreg.card_pos) _)
  have hc := hlower.trans_le (card_E0 y T p hT hreg)
  exact Finset.card_pos.mp (by exact_mod_cast hc)

/-- A constructed array gives positivity of the literal joint history and count event. -/
theorem row_history_totals_pos (y : Local.CoarseData V n) {T p : ℝ}
    (hT : 1 < T) (hreg : Regime y T p) (hsep : Separated y T p)
    (q : Local.Tilt n) :
    0 < RowArray.law y.part q
      (RowArray.history y.part ∩ RowArray.exactTotals y.part y.edge) := by
  obtain ⟨d, hd⟩ := E0_nonempty y hT hreg
  apply lt_of_lt_of_le (BlockPairLaws.law_singleton_pos y.part q d)
  apply measure_mono
  intro a ha
  obtain rfl := Set.mem_singleton_iff.mp ha
  exact ⟨e0_history hT hreg hsep hd, (mem_E0 y T p a).mp hd |>.1⟩

/-- The complete cardinality bound: constants and threshold precede all varying data. -/
theorem uniform_cardinality {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ y : Local.CoarseData V n,
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
      Real.exp (-C*N)*(p*N)^((((2^(n+1)*N : ℕ) : ℝ))/2) ≤ ((E0 y T p).card : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := uniform_regime n hθlo hθhi hT
  refine ⟨countingRate n T, countingRate_pos n hT, N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi y hsizes hcounts
  have hreg := hN₀ N hN V hcard p hlo hhi y hsizes hcounts
  simpa only [hcard, labelCount] using card_E0 y T p hT hreg

/-- Uniform literal inclusion in exact counts, original histories, κ and every Γ_C, C≥1. -/
theorem uniform_inclusion {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ y : Local.CoarseData V n,
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) → Separated y T p →
      ∀ d ∈ E0 y T p, RowArray.totals d = y.edge ∧ d ∈ RowArray.history y.part ∧
        RowArray.Regular p d ∧ RowArray.Gamma y.part y.edge 1 p d ∧
        ∀ C : ℝ, 1 ≤ C → RowArray.Gamma y.part y.edge C p d := by
  obtain ⟨N₀, hN₀⟩ := uniform_regime n hθlo hθhi hT
  refine ⟨N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi y hsizes hcounts hsep d hd
  have hreg := hN₀ N hN V hcard p hlo hhi y hsizes hcounts
  exact ⟨((mem_E0 y T p d).mp hd).1, e0_history hT hreg hsep hd,
    e0_regular hT hreg hd, e0_gamma_one hT hreg hd,
    fun _ hC => e0_gamma_mono hT hreg hC hd⟩

/-- Literal graph existence is the only endpoint using the accepted EG/GR inputs. -/
theorem uniform_inclusion_graphical {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ y : Local.CoarseData V n,
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) → Separated y T p →
      ∀ d ∈ E0 y T p, RowArray.totals d = y.edge ∧ d ∈ RowArray.history y.part ∧
        RowArray.Regular p d ∧ RowArray.Gamma y.part y.edge 1 p d ∧
        (∀ C : ℝ, 1 ≤ C → RowArray.Gamma y.part y.edge C p d) ∧
        ∃ G : SimpleGraph V, History.degreeArray y.part G = RowArray.values d := by
  obtain ⟨N₁, hN₁⟩ := uniform_inclusion n hθlo hθhi hT
  obtain ⟨N₂, hN₂⟩ := AutomaticGraphicality.automatic_graphicality_exists hθlo hθhi hT
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN V inst hcard p hlo hhi y hsizes hcounts hsep d hd
  obtain ⟨htot, hhist, hreg, hgamma, hmono⟩ :=
    hN₁ N ((le_max_left _ _).trans hN) V hcard p hlo hhi y hsizes hcounts hsep d hd
  exact ⟨htot, hhist, hreg, hgamma, hmono,
    hN₂ N ((le_max_right _ _).trans hN) V hcard n p hlo hhi y d hsizes hcounts htot hreg⟩

/-- Nonemptiness and strict conditioning positivity, without a quantitative LCLT claim. -/
theorem uniform_nonempty_and_positive {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ y : Local.CoarseData V n,
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
      (E0 y T p).Nonempty ∧ (Separated y T p → ∀ q : Local.Tilt n,
        0 < RowArray.law y.part q
          (RowArray.history y.part ∩ RowArray.exactTotals y.part y.edge)) := by
  obtain ⟨N₀, hN₀⟩ := uniform_regime n hθlo hθhi hT
  refine ⟨N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi y hsizes hcounts
  have hreg := hN₀ N hN V hcard p hlo hhi y hsizes hcounts
  exact ⟨E0_nonempty y hT hreg, fun hsep q => row_history_totals_pos y hT hreg hsep q⟩

end MajorityDynamics.GraphProcess.GoodArrays
