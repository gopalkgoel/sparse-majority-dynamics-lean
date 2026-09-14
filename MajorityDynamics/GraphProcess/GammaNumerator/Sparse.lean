import MajorityDynamics.GraphProcess.GammaNumerator.Main
import MajorityDynamics.GraphProcess.EnumerationBounds.BandAsymptotics

/-! Original Gamma estimates with constants uniform over the sparse range. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.GammaNumerator
open Universal
universe u

theorem uniform_regime_sparse {θ T : ℝ} (n : ℕ)
    (_hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-(1/2 : ℝ)) →
      ∀ π : V → History (n+1),
      (∀ s, (N : ℝ)/T ≤ (Local.partSizes π s : ℝ)) →
      0 < (N : ℝ) ∧ 0 < p ∧ p < 1 ∧ 2*T ≤ (N : ℝ) ∧
      (∀ s, 2 ≤ Local.partSizes π s) ∧
      (∀ s, (p*N)^((4:ℝ)/7) ≤ p*(Local.partSizes π s : ℝ)) ∧
      (∀ s t, Probability.DegreeConcentration.sizeRange T
        (Local.partSizes π t) (Local.partSizes π s)) := by
  obtain ⟨X,hX,hpow⟩ := EnumerationBounds.eventually_mul_rpow_le
    (a := (4:ℝ)/7) (b := 1) (A := T) (B := 1) (by norm_num) zero_lt_one
  obtain ⟨N₀,h₀⟩ := EnumerationBounds.eventually_band_window (η := 1/2) (by norm_num) hθhi hT
    (L := X) (U := 1/2) (M := 2*T) hX (by norm_num) (by linarith)
  refine ⟨N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi π hsizes
  obtain ⟨hNp,hp,hNT,hx,hp1⟩ := h₀ N hN p hlo hhi
  have hT0 : 0 < T := by linarith
  have hup (s : History (n+1)) : (Local.partSizes π s : ℝ) ≤ N := by
    have hh : Local.partSizes π s ≤ Fintype.card V :=
      (Finset.card_filter_le _ _).trans_eq Finset.card_univ
    rw [hcard] at hh
    exact_mod_cast hh
  have htol : T*(p*N)^((4:ℝ)/7) ≤ p*N := by
    simpa only [Real.rpow_one, one_mul] using hpow (p*N) hx
  refine ⟨hNp,hp,by linarith,hNT,?_,?_,?_⟩
  · intro s
    have hh := (div_le_iff₀ hT0).mp (hsizes s)
    have hh' : (2:ℝ) ≤ Local.partSizes π s := by nlinarith
    exact_mod_cast hh'
  · intro s
    exact tolerance_le_block hT0 hp.le (hsizes s) htol
  · intro s t
    exact block_sizeRange hT0 (hsizes t) (hsizes s) (hup t) (hup s)

theorem uniform_numerator_sparse {θ T K : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hK : 0 < K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : unitInterval,
      T⁻¹*(N : ℝ)^(-θ) < (p : ℝ) → (p : ℝ) < T * (N : ℝ)^(-(1/2 : ℝ)) →
      ∀ π : V → History (n+1),
      (∀ s, (N : ℝ)/T ≤ (Local.partSizes π s : ℝ)) →
      (SimpleGraph.binomialRandom V p).real {G |
        ¬ RowArray.Gamma π (RowArray.totals (RowArray.graphArray π G)) C p
          (RowArray.graphArray π G) ∧ RowArray.Regular p (RowArray.graphArray π G)} ≤
          Real.exp (-K*N) ∧
      ((SimpleGraph.binomialRandom V p).map (RowArray.graphArray π)).real
        {d | ¬ RowArray.Gamma π (RowArray.totals d) C p d ∧ RowArray.Regular p d} ≤
          Real.exp (-K*N) ∧
      ∀ m : History (n+1) → History (n+1) → ℤ,
        ((SimpleGraph.binomialRandom V p).map (RowArray.graphArray π)).real
          {d | ¬ RowArray.Gamma π m C p d ∧ d ∈ RowArray.history π ∧
            RowArray.Regular p d ∧ d ∈ RowArray.exactTotals π m} ≤ Real.exp (-K*N) := by
  obtain ⟨N₁,h₁⟩ := uniform_regime_sparse n hθlo hθhi hT
  obtain ⟨N₂,h₂⟩ := eventually_exp_absorption (Fintype.card (History (n+1))) K
  refine ⟨numeratorConstant T K, numeratorConstant_ge_one T K, max N₁ N₂, ?_⟩
  intro N hN V inst hcard p hlo hhi π hsizes
  obtain ⟨_,hp,_,_,hs2,htol,hratio⟩ :=
    h₁ N ((le_max_left _ _).trans hN) V hcard p hlo hhi π hsizes
  have hb := graph_numerator_bound π p hT hK.le hp hcard hsizes hs2 hratio
    (by simpa only [hcard] using htol)
  have hg := hb.trans (h₂ N ((le_max_right _ _).trans hN))
  refine ⟨hg, ?_, fun m => (paper_numerator_le π p m _).trans hg⟩
  change (arrayLaw π p).real _ ≤ _
  rw [arrayLaw_real]
  exact hg

/-- Literal real-density form. Positivity and p<1 are derived uniformly before
forming the actual random graph law, with no extra density assumption. -/
theorem uniform_numerator_real_sparse {θ T K : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hK : 0 < K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-(1/2 : ℝ)) →
      ∃ hp : 0 < p ∧ p < 1, ∀ π : V → History (n+1),
      (∀ s, (N : ℝ)/T ≤ (Local.partSizes π s : ℝ)) →
      let q : unitInterval := ⟨p,hp.1.le,hp.2.le⟩
      (SimpleGraph.binomialRandom V q).real {G |
        ¬ RowArray.Gamma π (RowArray.totals (RowArray.graphArray π G)) C p
          (RowArray.graphArray π G) ∧ RowArray.Regular p (RowArray.graphArray π G)} ≤
          Real.exp (-K*N) ∧
      ((SimpleGraph.binomialRandom V q).map (RowArray.graphArray π)).real
        {d | ¬ RowArray.Gamma π (RowArray.totals d) C p d ∧ RowArray.Regular p d} ≤
          Real.exp (-K*N) ∧
      ∀ m : History (n+1) → History (n+1) → ℤ,
        ((SimpleGraph.binomialRandom V q).map (RowArray.graphArray π)).real
          {d | ¬ RowArray.Gamma π m C p d ∧ d ∈ RowArray.history π ∧
            RowArray.Regular p d ∧ d ∈ RowArray.exactTotals π m} ≤ Real.exp (-K*N) := by
  obtain ⟨C,hC,N₁,h₁⟩ := uniform_numerator_sparse n hθlo hθhi hT hK
  obtain ⟨N₂,h₂⟩ := EnumerationBounds.eventually_band_window (η := 1/2)
    (by norm_num) hθhi hT (L := 1) zero_lt_one (U := 1/2) (by norm_num)
    (M := 1) zero_lt_one
  refine ⟨C,hC,max N₁ N₂,?_⟩
  intro N hN V inst hcard p hlo hhi
  have hr := h₂ N ((le_max_right _ _).trans hN) p hlo hhi
  have hp : 0 < p ∧ p < 1 := ⟨hr.2.1, by linarith [hr.2.2.2.2]⟩
  refine ⟨hp,?_⟩
  intro π hsizes
  exact h₁ N ((le_max_left _ _).trans hN) V hcard ⟨p,hp.1.le,hp.2.le⟩ hlo hhi π hsizes

end MajorityDynamics.GraphProcess.GammaNumerator

