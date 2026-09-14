import MajorityDynamics.GraphProcess.GoodArrays.Main
import MajorityDynamics.GraphProcess.AutomaticGraphicality.Sparse
import MajorityDynamics.GraphProcess.EnumerationBounds.BandAsymptotics

/-! Separate sparse-range versions; all original finite laws and predicates
are retained. Constants precede every varying finite datum. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology
namespace MajorityDynamics.GraphProcess.GoodArrays
open Universal
universe u

theorem uniform_regime_sparse {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-(1/2 : ℝ)) →
      ∀ y : Local.CoarseData V n,
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) → Regime y T p := by
  obtain ⟨X, hX, hpow⟩ := EnumerationBounds.eventually_mul_rpow_le
    (a := (1:ℝ)/2) (b := (4:ℝ)/7) (A := T^2+1) (B := 1)
    (by norm_num) zero_lt_one
  let L := max X (max (4*T^6) (max ((200*T*(labelCount n : ℝ))^2) ((2*T^2)^2)))
  have hL : 0 < L := hX.trans_le (le_max_left _ _)
  obtain ⟨N₀, hN₀⟩ := EnumerationBounds.eventually_band_window (η := 1/2) (by norm_num) hθhi hT hL
    (U := 1/(8*T^2)) (by positivity) (M := 2*T) (by linarith)
  refine ⟨N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi y hsizes hcounts
  have hw := hN₀ N hN p hlo hhi
  have hLX : X ≤ L := le_max_left _ _
  have hLC : 4*T^6 ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hLR : (200*T*(labelCount n : ℝ))^2 ≤ L :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hLS : (2*T^2)^2 ≤ L :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  subst N
  apply finite_regime y hT hw.2.2.1 hw.2.1 hw.2.2.2.2
    (hLC.trans hw.2.2.2.1) (hLR.trans hw.2.2.2.1) (hLS.trans hw.2.2.2.1)
    _ hsizes hcounts
  simpa [Real.sqrt_eq_rpow] using hpow (p*Fintype.card V) (hLX.trans hw.2.2.2.1)

theorem uniform_cardinality_sparse {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-(1/2 : ℝ)) →
      ∀ y : Local.CoarseData V n,
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
      Real.exp (-C*N)*(p*N)^((((2^(n+1)*N : ℕ) : ℝ))/2) ≤ ((E0 y T p).card : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := uniform_regime_sparse n hθlo hθhi hT
  refine ⟨countingRate n T, countingRate_pos n hT, N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi y hsizes hcounts
  have hreg := hN₀ N hN V hcard p hlo hhi y hsizes hcounts
  simpa only [hcard, labelCount] using card_E0 y T p hT hreg

/-- Uniform literal inclusion in exact counts, original histories, κ and every Γ_C, C≥1. -/
theorem uniform_inclusion_sparse {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-(1/2 : ℝ)) →
      ∀ y : Local.CoarseData V n,
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) → Separated y T p →
      ∀ d ∈ E0 y T p, RowArray.totals d = y.edge ∧ d ∈ RowArray.history y.part ∧
        RowArray.Regular p d ∧ RowArray.Gamma y.part y.edge 1 p d ∧
        ∀ C : ℝ, 1 ≤ C → RowArray.Gamma y.part y.edge C p d := by
  obtain ⟨N₀, hN₀⟩ := uniform_regime_sparse n hθlo hθhi hT
  refine ⟨N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi y hsizes hcounts hsep d hd
  have hreg := hN₀ N hN V hcard p hlo hhi y hsizes hcounts
  exact ⟨((mem_E0 y T p d).mp hd).1, e0_history hT hreg hsep hd,
    e0_regular hT hreg hd, e0_gamma_one hT hreg hd,
    fun _ hC => e0_gamma_mono hT hreg hC hd⟩

/-- Literal graph existence is the only endpoint using the accepted EG/GR inputs. -/
theorem uniform_inclusion_graphical_sparse {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-(1/2 : ℝ)) →
      ∀ y : Local.CoarseData V n,
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) → Separated y T p →
      ∀ d ∈ E0 y T p, RowArray.totals d = y.edge ∧ d ∈ RowArray.history y.part ∧
        RowArray.Regular p d ∧ RowArray.Gamma y.part y.edge 1 p d ∧
        (∀ C : ℝ, 1 ≤ C → RowArray.Gamma y.part y.edge C p d) ∧
        ∃ G : SimpleGraph V, History.degreeArray y.part G = RowArray.values d := by
  obtain ⟨N₁, hN₁⟩ := uniform_inclusion_sparse n hθlo hθhi hT
  obtain ⟨N₂, hN₂⟩ := AutomaticGraphicality.automatic_graphicality_exists_sparse hθlo hθhi hT
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN V inst hcard p hlo hhi y hsizes hcounts hsep d hd
  obtain ⟨htot, hhist, hreg, hgamma, hmono⟩ :=
    hN₁ N ((le_max_left _ _).trans hN) V hcard p hlo hhi y hsizes hcounts hsep d hd
  exact ⟨htot, hhist, hreg, hgamma, hmono,
    hN₂ N ((le_max_right _ _).trans hN) V hcard n p hlo hhi y d hsizes hcounts htot hreg⟩

/-- Nonemptiness and strict conditioning positivity, without a quantitative LCLT claim. -/
theorem uniform_nonempty_and_positive_sparse {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-(1/2 : ℝ)) →
      ∀ y : Local.CoarseData V n,
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
      (E0 y T p).Nonempty ∧ (Separated y T p → ∀ q : Local.Tilt n,
        0 < RowArray.law y.part q
          (RowArray.history y.part ∩ RowArray.exactTotals y.part y.edge)) := by
  obtain ⟨N₀, hN₀⟩ := uniform_regime_sparse n hθlo hθhi hT
  refine ⟨N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi y hsizes hcounts
  have hreg := hN₀ N hN V hcard p hlo hhi y hsizes hcounts
  exact ⟨E0_nonempty y hT hreg, fun hsep q => row_history_totals_pos y hT hreg hsep q⟩

end MajorityDynamics.GraphProcess.GoodArrays
