import MajorityDynamics.GraphProcess.EnumerationBounds.Preparation
import MajorityDynamics.GraphProcess.EnumerationBounds.BandAsymptotics

noncomputable section
namespace MajorityDynamics.GraphProcess.EnumerationBounds
universe u

/-- One threshold, before every varying graph carrier and array, supplies all
numerical preparation; no history, attainability or graphicality is assumed. -/
theorem uniform_band_preparation {θ η T : ℝ}
    (hη : 0 < η) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ (n : ℕ) (p : ℝ),
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-η) →
      ∀ (y : Local.CoarseData V n) (d : RowArray.Ambient y.part),
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
      RowArray.Regular p d → Prepared y d T p := by
  have hT0 : 0 < T := by linarith
  obtain ⟨X, _hX0, hX⟩ := eventually_deviation_regime hT
  obtain ⟨N₀, hN₀⟩ := eventually_band_window hη hθhi hT
    (L := max 1 (max (4*T^6) X)) (U := 1/(8*T^2)) (M := 2*T)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (by positivity) (by positivity)
  refine ⟨N₀, ?_⟩
  intro N hNN V inst hcard n p hlo hhi y d hsizes hcounts hreg
  obtain ⟨hN, hp, hNsize, hx, hsmall⟩ := hN₀ N hNN p hlo hhi
  have hx1 : 1 ≤ p*N := (le_max_left _ _).trans hx
  have hxT : 4*T^6 ≤ p*N := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hx
  have hxX : X ≤ p*N := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hx
  obtain ⟨hdev, hentry⟩ := hX (p*N) hxX
  subst N
  exact finite_preparation y d hT hN hp hNsize hx1 hxT hsmall hdev hentry
    hsizes hcounts hreg

end MajorityDynamics.GraphProcess.EnumerationBounds
