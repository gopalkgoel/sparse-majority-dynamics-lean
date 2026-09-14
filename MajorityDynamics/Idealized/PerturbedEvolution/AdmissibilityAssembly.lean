import MajorityDynamics.Idealized.PerturbedEvolution.AdmissibilitySeparation
import MajorityDynamics.Idealized.PerturbedTilt.AdmissibilityEdges

/-! Assembly of LA1–LA9. Only the three response clauses enter this internal
lemma; the perturbed-evolution endpoint discharges them with the row theorem. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace MajorityDynamics.Idealized.PerturbedEvolution
open Universal LinearResponse PerturbedTilt
open Binomial.Approximation (Density)

theorem admissibility_spec (θ T δ : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hδ : 0 < δ) (n ell : ℕ)
    (hk : (n : ℝ) + 1 < 1 / (1 - θ)) (C : ℝ) (hC : 0 ≤ C) :
    ∃ K : ℝ, T ≤ K ∧ C ≤ K ∧ 0 < K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ p : Binomial.Probability, Density θ T N p →
      ∀ a : Process.Data, Process.Specification N p (responseHorizon θ) ell a →
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ (V : Type*) [Fintype V] (y : Local.CoarseData V n), Fintype.card V = N →
      y.reg = true → FaithfulNumericalData N (p : ℝ) T δ τ a n y.integerSizes y.edge →
      ∀ q : Local.Tilt n, Local.Solves y.sizes y.realEdges q →
      (∀ s t, |(q s t : ℝ) - (p : ℝ)| ≤ C * (p : ℝ) / Real.sqrt ((p : ℝ) * N)) →
      ∀ φ : ℝ,
      (∀ s, φ ≤ Binomial.eventMass (Local.trials y.sizes s) (q s)
        (Local.historySupport y.sizes s)) →
      (∀ s b, φ ≤ Local.splitProbability y.sizes q s b ∧
        Local.splitProbability y.sizes q s b ≤ 1 - φ) →
      Local.Admissible y q K φ (p : ℝ) := by
  obtain ⟨Ks, hKs, hsizes⟩ := faithful_sizes_admissible θ T δ hθlo hθhi hT hδ n ell hk
  obtain ⟨Ke, hKe, hedges⟩ := faithful_edge_bounds θ T δ hθlo hθhi hT hδ n ell hk
  obtain ⟨c, hc, hsep⟩ := faithful_separation θ T δ hθlo hθhi hT hδ n ell hk
  let K : ℝ := T + C + Ks + Ke + 2 / c
  have hT0 : 0 < T := by linarith
  have hKs0 : 0 < Ks := by linarith
  have hKe0 : 0 < Ke := by linarith
  have hcinv : 0 < 2 / c := by positivity
  have hKT : T ≤ K := by dsimp [K]; linarith
  have hKC : C ≤ K := by dsimp [K]; linarith
  have hKS : Ks ≤ K := by dsimp [K]; linarith
  have hKE : Ke ≤ K := by dsimp [K]; linarith
  have hKc : 2 / c ≤ K := by dsimp [K]; linarith
  have hK0 : 0 < K := hT0.trans_le hKT
  have hInv : K⁻¹ < c := by
    have hhalf : K⁻¹ ≤ c / 2 := by
      rw [inv_eq_one_div]
      apply (div_le_iff₀ hK0).mpr
      have hh : 2 / c * (c / 2) = 1 := by field_simp
      have := mul_le_mul_of_nonneg_right hKc (half_pos hc).le
      nlinarith
    exact hhalf.trans_lt (half_lt_self hc)
  refine ⟨K, hKT, hKC, hK0, ?_⟩
  filter_upwards [hsizes, hedges, hsep, eventually_gt_atTop (0 : ℕ)]
    with N hsizes hedges hsep hN
  intro p hp a ha τ hτ hτT V inst y hcard hreg hf q hq htilt φ hcond hsplit
  have hsz := hsizes p hp a ha τ hτ hτT y.integerSizes y.edge hf
  have hed := hedges p hp a ha τ hτ hτT y.integerSizes y.edge hf
  have hsp := hsep p hp a ha τ hτ hτT y.integerSizes y.edge hf
  have hp0 := p.property.1
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hE : 0 < Local.edgeScale N (p : ℝ) := by unfold Local.edgeScale; positivity
  refine ⟨hreg, ?_, ?_, ?_, ?_, ?_, ?_, hcond, hq, hsplit⟩
  · intro s
    have hl := (mul_le_mul_of_nonneg_right (inv_anti₀ hKs0 hKS) hNr.le).trans (hsz.1 s)
    simpa only [hcard, Local.CoarseData.integerSizes, Int.cast_natCast] using hl
  · intro r
    have hl := (hsz.2 r).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKS hNr.le) (Real.sqrt_nonneg _))
    simpa only [hcard, Local.CoarseData.integerSizes, Int.cast_natCast] using hl
  · intro s t
    have hl := (hed s t).1.trans (mul_le_mul_of_nonneg_right hKE hE.le)
    simpa only [hcard, Local.CoarseData.integerSizes, Int.cast_natCast,
      Local.CoarseData.realEdges] using hl
  · intro s t
    exact (hed s t).2
  · intro s r
    have hl := (mul_lt_mul_of_pos_right hInv hE).trans_le (hsp s r)
    simpa only [hcard, Local.CoarseData.realEdges] using
      Local.decision_of_strict_margin (bits (n + 1) s r.castSucc)
        (bits (n + 1) s r.succ) hl
  · intro s t
    have hl := (htilt s t).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKC hp0.le) (Real.sqrt_nonneg _))
    simpa only [hcard] using hl

end MajorityDynamics.Idealized.PerturbedEvolution
