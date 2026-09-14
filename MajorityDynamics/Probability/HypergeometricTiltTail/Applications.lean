import MajorityDynamics.Probability.HypergeometricTiltTail.Main

noncomputable section
namespace MajorityDynamics.Probability.HypergeometricTiltTail

/-- Uniform graph application of the analytic factor estimate. The population
omits the distinguished vertex, the target size is the original `S.card`, and
the weight normalization remains the full ambient size. -/
theorem uniform_graph_factor {θ T B : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hB : 0 ≤ B) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-θ) →
      ∀ (V : Type*) [Fintype V] [DecidableEq V], Fintype.card V = N →
      ∀ (v : V) (S : Finset V),
      (N:ℝ)/T ≤ S.card → (S.card:ℝ) ≤ N-(N:ℝ)/T →
      ∀ β : V → ℝ, (∀ w, |β w| ≤ Real.log (N:ℝ)) →
      ∀ d t : ℤ, |(d:ℝ)-p*N| ≤ Real.sqrt (p*N)*Real.log (N:ℝ) →
      0 ≤ t → t ≤ d →
      (Real.log (N:ℝ))^100 ≤ |((t:ℝ)-p*S.card)/Real.sqrt (p*S.card)| →
      Real.exp (B*(Real.log (N:ℝ))^4) * graphFactor v S d t p β ≤
        Real.exp (-c*(((t:ℝ)-p*S.card)/Real.sqrt (p*S.card))^2) := by
  obtain ⟨c,hc,N₀,h⟩ := uniform_factor hθlo hθhi hT hB
  refine ⟨c,hc,N₀,?_⟩
  intro N hN p hlo hhi V _ _ hcard v S hSlo hShi β hβ d t hd ht htd hτ
  have hN0 : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  have hTN : (N:ℝ) ≤ T*N := by
    nlinarith only [mul_nonneg hN0 (le_of_lt (sub_pos.mpr hT))]
  have hNL : (N:ℝ)/T ≤ N := by
    apply (div_le_iff₀ (by linarith : 0 < T)).2
    nlinarith only [hTN]
  have hM : (Finset.univ.erase v).card = N-1 := by
    rw [erased_population_card, hcard]
  have hf := h N hN p hlo hhi V (Finset.univ.erase v) (S.erase v)
    (erase_subset_population v S) (Or.inr hM) S.card hSlo hShi
    (erased_part_card_close v S) N hNL hTN β (fun w _ => hβ w)
    d t hd ht htd hτ
  simpa only [graphFactor, hcard] using hf

/-- Uniform bipartite application. The opposite population has size `N`, while
the normalization `L` may be the different size of the distinguished side. -/
theorem uniform_bipartite_factor {θ T B : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hB : 0 ≤ B) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-θ) →
      ∀ (V : Type*) [Fintype V] [DecidableEq V], Fintype.card V = N →
      ∀ S : Finset V, (N:ℝ)/T ≤ S.card → (S.card:ℝ) ≤ N-(N:ℝ)/T →
      ∀ L : ℝ, (N:ℝ)/T ≤ L → L ≤ T*N →
      ∀ β : V → ℝ, (∀ w, |β w| ≤ Real.log (N:ℝ)) →
      ∀ d t : ℤ, |(d:ℝ)-p*N| ≤ Real.sqrt (p*N)*Real.log (N:ℝ) →
      0 ≤ t → t ≤ d →
      (Real.log (N:ℝ))^100 ≤ |((t:ℝ)-p*S.card)/Real.sqrt (p*S.card)| →
      Real.exp (B*(Real.log (N:ℝ))^4) * bipartiteFactor S d t p L β ≤
        Real.exp (-c*(((t:ℝ)-p*S.card)/Real.sqrt (p*S.card))^2) := by
  obtain ⟨c,hc,N₀,h⟩ := uniform_factor hθlo hθhi hT hB
  refine ⟨c,hc,N₀,?_⟩
  intro N hN p hlo hhi V _ _ hcard S hSlo hShi L hLlo hLhi β hβ d t hd ht htd hτ
  have hM : (Finset.univ : Finset V).card = N := by simpa only [Finset.card_univ] using hcard
  exact h N hN p hlo hhi V Finset.univ S (Finset.subset_univ S) (Or.inl hM)
    S.card hSlo hShi (by simp) L hLlo hLhi β (fun w _ => hβ w) d t hd ht htd hτ

end MajorityDynamics.Probability.HypergeometricTiltTail
