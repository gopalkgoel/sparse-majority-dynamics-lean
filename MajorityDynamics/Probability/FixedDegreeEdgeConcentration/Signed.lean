import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Main
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.SignedInputs

noncomputable section
universe u v
open scoped Classical BigOperators
namespace MajorityDynamics.Probability.FixedDegreeEdgeConcentration
open FixedDegreeSampling

/-- C.1's graph clauses with the manuscript's integer edge total. Positivity of
that total is proved; the law still uses the original bounded natural degrees. -/
theorem signed_graph_concentration {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-θ) →
      ∀ (V : Type u) [Fintype V] (m : ℤ) (d : V → ℕ),
        Fintype.card V = N → (∀ v, d v ≤ N-1) →
        (∑ v, (d v:ℤ) = 2*m) →
        |(m:ℝ)-p*N*(N-1)/2| ≤ T*N^2*p/Real.sqrt (p*N) →
        (∀ v, |(d v:ℝ)-p*N| ≤ (p*N)^((4:ℝ)/7)) →
        0 < m ∧ ∀ U : Finset V,
          (N:ℝ)/T ≤ U.card → (N:ℝ)/T ≤ N-(U.card:ℝ) →
          (fixedDegreeLaw d).real {G | edgeThreshold N p ≤
            |(internalCount U G:ℝ)-(∑ v ∈ U, (d v:ℝ))^2/(4*(m:ℝ))|} < 1/Real.log N ∧
          (fixedDegreeLaw d).real {G | edgeThreshold N p ≤
            |(cutCount U G:ℝ)-(∑ v ∈ U, (d v:ℝ))*
              (∑ v ∈ Finset.univ \ U, (d v:ℝ))/(2*(m:ℝ))|} < 1/Real.log N := by
  obtain ⟨N₁,h₁⟩ := graph_concentration.{u} hθlo hθhi hT
  obtain ⟨N₂,h₂⟩ := eventually_originalScales hθlo hθhi hT
  refine ⟨max N₁ N₂,?_⟩
  intro N hN p hlo hhi V _ m d hcard hbound htotal hcount hdegree
  obtain ⟨_,hmc,hi⟩ := graphInput_of_signed_total N m p T d hcard hbound htotal hcount hdegree
  have hs := h₂ N ((le_max_right _ _).trans hN) p ⟨hlo,hhi⟩
  have hmpos : (0:ℝ) < m := by simpa only [hmc] using hi.count_pos hs
  refine ⟨by exact_mod_cast hmpos,?_⟩
  intro U _ _
  have hh := h₁ N ((le_max_left _ _).trans hN) p ⟨hlo,hhi⟩ V m.toNat d hi U
  simpa only [hmc] using hh

/-- All three literal graph inputs, including integer m, on the manuscript's
Fin N carrier. No conversion is made to the random graph or degree vector. -/
theorem signed_graph_concentration_fin {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-θ) →
      ∀ (m : ℤ) (d : Fin N → ℕ),
        (∀ v, d v ≤ N-1) → (∑ v, (d v:ℤ) = 2*m) →
        |(m:ℝ)-p*N*(N-1)/2| ≤ T*N^2*p/Real.sqrt (p*N) →
        (∀ v, |(d v:ℝ)-p*N| ≤ (p*N)^((4:ℝ)/7)) →
        0 < m ∧ ∀ U : Finset (Fin N),
          (N:ℝ)/T ≤ U.card → (N:ℝ)/T ≤ N-(U.card:ℝ) →
          (fixedDegreeLaw d).real {G | edgeThreshold N p ≤
            |(internalCount U G:ℝ)-(∑ v ∈ U, (d v:ℝ))^2/(4*(m:ℝ))|} < 1/Real.log N ∧
          (fixedDegreeLaw d).real {G | edgeThreshold N p ≤
            |(cutCount U G:ℝ)-(∑ v ∈ U, (d v:ℝ))*
              (∑ v ∈ Finset.univ \ U, (d v:ℝ))/(2*(m:ℝ))|} < 1/Real.log N := by
  obtain ⟨N₀,h₀⟩ := signed_graph_concentration.{0} hθlo hθhi hT
  refine ⟨N₀,?_⟩
  intro N hN p hlo hhi m d hb ht hc hd
  have h := h₀ N hN p hlo hhi (Fin N) m d (Fintype.card_fin N) hb ht hc hd
  refine ⟨h.1,?_⟩
  intro U hU hUc
  have hh := h.2 U hU hUc
  refine ⟨hh.1,?_⟩
  convert! hh.2 using 1
  congr! 8
  apply Finset.sum_congr
  · ext v
    simp
  · intro v _
    rfl


/-- C.1's bipartite clause with both manuscript parameters ell and m signed.
Their positivity follows from the original size and degree conditions. The two
degree tolerances both use the same reference p*N. -/
theorem signed_bipartite_concentration {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-θ) →
      ∀ (L : Type u) (R : Type v) [Fintype L] [Fintype R]
        (ell m : ℤ) (a : L → ℕ) (b : R → ℕ),
        (Fintype.card L:ℤ) = ell → Fintype.card R = N →
        (N:ℝ)/T ≤ (ell:ℝ) → (ell:ℝ) ≤ T*N →
        (∀ i, a i ≤ N) → (∀ j, (b j:ℤ) ≤ ell) →
        (∑ i, (a i:ℤ) = m) → (∑ j, (b j:ℤ) = m) →
        |(m:ℝ)-p*(ell:ℝ)*N| ≤ T*N^2*p/Real.sqrt (p*N) →
        (∀ i, |(a i:ℝ)-p*N| ≤ (p*N)^((4:ℝ)/7)) →
        (∀ j, |(b j:ℝ)-p*(ell:ℝ)| ≤ (p*N)^((4:ℝ)/7)) →
        0 < ell ∧ 0 < m ∧ ∀ (U : Finset L) (W : Finset R),
          (N:ℝ)/T ≤ U.card → (N:ℝ)/T ≤ (ell:ℝ)-(U.card:ℝ) →
          (N:ℝ)/T ≤ W.card → (N:ℝ)/T ≤ N-(W.card:ℝ) →
          (bipartiteFixedDegreeLaw a b).real {E | edgeThreshold N p ≤
            |(rectangleCount U W E:ℝ)-(∑ i ∈ U, (a i:ℝ))*
              (∑ j ∈ W, (b j:ℝ))/(m:ℝ)|} < 1/Real.log N := by
  obtain ⟨N₁,h₁⟩ := bipartite_concentration.{u,v} hθlo hθhi hT
  obtain ⟨N₂,h₂⟩ := eventually_originalScales hθlo hθhi hT
  refine ⟨max N₁ N₂,?_⟩
  intro N hN p hlo hhi L R _ _ ell m a b hcL hcR heL heU ha hb hta htb hcount hda hdb
  obtain ⟨_,_,_,hmc,hi⟩ := bipartiteInput_of_signed_totals N ell m p T a b
    hcL hcR heL heU ha hb hta htb hcount hda hdb
  have hs := h₂ N ((le_max_right _ _).trans hN) p ⟨hlo,hhi⟩
  have hmpos : (0:ℝ) < m := by simpa only [hmc] using hi.count_pos hs
  have hepos : (0:ℝ) < ell := (div_pos hs.N_pos (by linarith : 0 < T)).trans_le heL
  refine ⟨by exact_mod_cast hepos,by exact_mod_cast hmpos,?_⟩
  intro U W _ _ _ _
  have hh := h₁ N ((le_max_left _ _).trans hN) p ⟨hlo,hhi⟩ L R ell.toNat m.toNat a b hi U W
  simpa only [hmc] using hh

/-- Literal Fin carriers for signed ell and m. The size window proves ell>0,
so Fin ell.toNat has exactly ell vertices; nonnegativity is not an extra input. -/
theorem signed_bipartite_concentration_fin {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-θ) →
      ∀ (ell m : ℤ) (a : Fin ell.toNat → ℕ) (b : Fin N → ℕ),
        (N:ℝ)/T ≤ (ell:ℝ) → (ell:ℝ) ≤ T*N →
        (∀ i, a i ≤ N) → (∀ j, (b j:ℤ) ≤ ell) →
        (∑ i, (a i:ℤ) = m) → (∑ j, (b j:ℤ) = m) →
        |(m:ℝ)-p*(ell:ℝ)*N| ≤ T*N^2*p/Real.sqrt (p*N) →
        (∀ i, |(a i:ℝ)-p*N| ≤ (p*N)^((4:ℝ)/7)) →
        (∀ j, |(b j:ℝ)-p*(ell:ℝ)| ≤ (p*N)^((4:ℝ)/7)) →
        0 < ell ∧ 0 < m ∧ ∀ (U : Finset (Fin ell.toNat)) (W : Finset (Fin N)),
          (N:ℝ)/T ≤ U.card → (N:ℝ)/T ≤ (ell:ℝ)-(U.card:ℝ) →
          (N:ℝ)/T ≤ W.card → (N:ℝ)/T ≤ N-(W.card:ℝ) →
          (bipartiteFixedDegreeLaw a b).real {E | edgeThreshold N p ≤
            |(rectangleCount U W E:ℝ)-(∑ i ∈ U, (a i:ℝ))*
              (∑ j ∈ W, (b j:ℝ))/(m:ℝ)|} < 1/Real.log N := by
  obtain ⟨N₁,h₁⟩ := signed_bipartite_concentration.{0,0} hθlo hθhi hT
  obtain ⟨N₂,h₂⟩ := eventually_originalScales hθlo hθhi hT
  refine ⟨max N₁ N₂,?_⟩
  intro N hN p hlo hhi ell m a b heL
  have hs := h₂ N ((le_max_right _ _).trans hN) p ⟨hlo,hhi⟩
  have heposR : (0:ℝ) < ell := (div_pos hs.N_pos (by linarith : 0 < T)).trans_le heL
  have hepos : 0 < ell := by exact_mod_cast heposR
  have hcL : (Fintype.card (Fin ell.toNat):ℤ) = ell := by
    simp only [Fintype.card_fin, Int.toNat_of_nonneg hepos.le]
  exact h₁ N ((le_max_left _ _).trans hN) p hlo hhi (Fin ell.toNat) (Fin N)
    ell m a b hcL (Fintype.card_fin N) heL

end MajorityDynamics.Probability.FixedDegreeEdgeConcentration
