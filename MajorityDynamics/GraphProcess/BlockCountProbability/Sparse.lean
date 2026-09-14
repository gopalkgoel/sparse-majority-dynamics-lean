import MajorityDynamics.GraphProcess.BlockCountProbability.Main
import MajorityDynamics.GraphProcess.EnumerationBounds.BandAsymptotics

/-! Separate sparse-range versions; all original finite laws and predicates
are retained. Constants precede every varying finite datum. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology
namespace MajorityDynamics.GraphProcess.BlockCountProbability
open Universal
universe u

theorem uniform_regime_sparse {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-(1/2 : ℝ)) →
      ∀ y : Local.CoarseData V n,
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
      1 ≤ (N : ℝ) ∧ 0 < p ∧ p < 1 ∧
      (∀ s, CountRegime N p (lossConstant T)
        ((y.sizes s).choose 2) ((y.edge s s/2).toNat)) ∧
      (∀ s t, s ≠ t → CountRegime N p (lossConstant T)
        (y.sizes s*y.sizes t) ((y.edge s t).toNat)) := by
  obtain ⟨N₀, h₀⟩ := EnumerationBounds.eventually_band_window (η := 1/2) (by norm_num) hθhi hT
    (L := max 1 (4*T^6)) (U := 1/(8*T^2)) (M := 2*T)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (by positivity) (by positivity)
  refine ⟨N₀, ?_⟩
  intro N hNN V inst hcard p hlo hhi y hsizes hcounts
  obtain ⟨hN, hp, hNs, hx, hps⟩ := h₀ N hNN p hlo hhi
  have hx1 : 1 ≤ p*N := (le_max_left _ _).trans hx
  have hxT : 4*T^6 ≤ p*N := (le_max_right _ _).trans hx
  have hsmall := (le_div_iff₀ (by positivity : 0 < 8*T^2)).mp hps
  have hp1 : p < 1 := by
    have hT2 : 1 < T^2 := by nlinarith
    nlinarith
  subst N
  exact ⟨by linarith, hp, hp1,
    finite_regime y hN hT hp hx1 hxT hps hNs hsizes hcounts⟩

theorem uniform_component_lower_sparse {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : unitInterval,
      T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) → (p : ℝ) < T*(N : ℝ)^(-(1/2 : ℝ)) →
      ∀ y : Local.CoarseData V n,
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-(p : ℝ)*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*(p : ℝ)/Real.sqrt ((p : ℝ)*N)) →
      (∀ s, Real.exp (-C*N) ≤
        (ProbabilityTheory.binomial ((y.sizes s).choose 2) p).real
          {(y.edge s s/2).toNat}) ∧
      (∀ s t, s ≠ t → Real.exp (-C*N) ≤
        (ProbabilityTheory.binomial (y.sizes s*y.sizes t) p).real
          {(y.edge s t).toNat}) := by
  obtain ⟨N₀, h₀⟩ := uniform_regime_sparse n hθlo hθhi hT
  refine ⟨componentConstant T, componentConstant_pos hT, N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi y hsizes hcounts
  obtain ⟨hN1, hp0, hp1, hi, hc⟩ := h₀ N hN V hcard (p : ℝ) hlo hhi y hsizes hcounts
  have hNnat : 1 ≤ N := by exact_mod_cast hN1
  constructor
  · intro s
    obtain ⟨hk, hkm, hkN, hloss⟩ := hi s
    exact binomial_lower_of_loss p (lossConstant T) hp0 hp1 hNnat hk hkm hkN hloss
  · intro s t hst
    obtain ⟨hk, hkm, hkN, hloss⟩ := hc s t hst
    exact binomial_lower_of_loss p (lossConstant T) hp0 hp1 hNnat hk hkm hkN hloss

theorem count_event_lower_sparse {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : unitInterval,
      T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) → (p : ℝ) < T*(N : ℝ)^(-(1/2 : ℝ)) →
      ∀ y : Local.CoarseData V n,
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-(p : ℝ)*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*(p : ℝ)/Real.sqrt ((p : ℝ)*N)) →
      Real.exp (-C*N) ≤ (SimpleGraph.binomialRandom V p).real
        (GraphicalArray.fixedCountFamily y.part y.edge) := by
  obtain ⟨C, hC, N₀, h₀⟩ := uniform_component_lower_sparse n hθlo hθhi hT
  refine ⟨C*factorCount n, mul_pos hC (by exact_mod_cast factorCount_pos n), N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi y hsizes hcounts
  obtain ⟨hi, hc⟩ := h₀ N hN V hcard p hlo hhi y hsizes hcounts
  rw [exact_factorization p y]
  exact product_lower n N C _ _ hi (fun z => hc z.val.1 z.val.2 (ne_of_lt z.property))

end MajorityDynamics.GraphProcess.BlockCountProbability
