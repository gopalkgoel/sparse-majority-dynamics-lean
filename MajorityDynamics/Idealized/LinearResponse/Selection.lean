import MajorityDynamics.Idealized.LinearResponse.Basic

/-! Properties of the selected Theorem 5.2 process and of the rate. -/

noncomputable section

namespace MajorityDynamics.Idealized.LinearResponse

open MajorityDynamics.Universal

theorem responseRate_pos {θ : ℝ} {n : ℕ} (hθlo : 1 / 2 < θ) (hθhi : θ < 1)
    (hk : (n : ℝ) + 1 < 1 / (1 - θ)) : 0 < responseRate θ n := by
  have hden : 0 < 1 - θ := sub_pos.mpr hθhi
  have hk' : ((n : ℝ) + 1) * (1 - θ) < 1 := (lt_div_iff₀ hden).mp hk
  have h1 : 0 < (1 - ((n : ℝ) + 1) * (1 - θ)) / 2 := by linarith
  have h2 : 0 < θ / 2 := by linarith
  have h3 : 0 < (1 - θ) / 2 := by linarith
  unfold responseRate
  have := lt_min h1 (lt_min h2 h3)
  linarith

theorem responseRate_le_first {θ : ℝ} {n : ℕ} :
    responseRate θ n ≤ (1 - ((n : ℝ) + 1) * (1 - θ)) / 4 := by
  unfold responseRate
  have := min_le_left ((1 - ((n : ℝ) + 1) * (1 - θ)) / 2) (min (θ / 2) ((1 - θ) / 2))
  linarith

theorem responseRate_le_theta {θ : ℝ} {n : ℕ} : responseRate θ n ≤ θ / 4 := by
  unfold responseRate
  have := (min_le_right ((1 - ((n : ℝ) + 1) * (1 - θ)) / 2) (min (θ / 2) ((1 - θ) / 2))).trans
    (min_le_left (θ / 2) ((1 - θ) / 2))
  linarith

theorem responseRate_le_complement {θ : ℝ} {n : ℕ} : responseRate θ n ≤ (1 - θ) / 4 := by
  unfold responseRate
  have := (min_le_right ((1 - ((n : ℝ) + 1) * (1 - θ)) / 2) (min (θ / 2) ((1 - θ) / 2))).trans
    (min_le_right (θ / 2) ((1 - θ) / 2))
  linarith

/-- Day `k = n + 1 < 1/(1-θ)` lies strictly inside the Theorem 5.2 horizon. -/
theorem level_succ_lt_horizon {θ : ℝ} {n : ℕ} (hk : (n : ℝ) + 1 < 1 / (1 - θ)) :
    n + 1 < responseHorizon θ := by
  have hfloor : 1 / (1 - θ) < ((⌊1 / (1 - θ)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlt : ((n : ℝ) + 1) < ((⌊1 / (1 - θ)⌋₊ : ℕ) : ℝ) + 1 := hk.trans hfloor
  have hnat : ((n + 1 : ℕ) : ℝ) < ((⌊1 / (1 - θ)⌋₊ + 1 : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast hnat

theorem processSelection_spec {θ T : ℝ} (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    1 ≤ processExponent θ T ∧ 1 ≤ processThreshold θ T ∧
      ∀ N ≥ processThreshold θ T, ∀ p : ℝ, T⁻¹ * (N : ℝ) ^ (-θ) < p → p < T * (N : ℝ) ^ (-θ) →
        ∃ hp : 0 < p ∧ p < 1, ∃ a : Process.Data,
          Process.Specification N ⟨p, hp⟩ (responseHorizon θ) (processExponent θ T) a ∧
            ∀ b : Process.Data, Process.Recursion N ⟨p, hp⟩ (responseHorizon θ) b →
              Process.AgreeThrough (responseHorizon θ) a b := by
  have h : 1 / 2 < θ ∧ θ < 1 ∧ 1 < T := ⟨hθlo, hθhi, hT⟩
  have he : processExponent θ T = (processExistence θ T h).choose := by
    unfold processExponent
    rw [dif_pos h]
  have ht : processThreshold θ T = (processExistence θ T h).choose_spec.2.choose := by
    unfold processThreshold
    rw [dif_pos h]
  rw [he, ht]
  exact ⟨(processExistence θ T h).choose_spec.1,
    (processExistence θ T h).choose_spec.2.choose_spec.1,
    (processExistence θ T h).choose_spec.2.choose_spec.2⟩

theorem referenceData_spec {θ T : ℝ} {N : ℕ} {p : Binomial.Probability}
    (h : ∃ a : Process.Data,
      Process.Specification N p (responseHorizon θ) (processExponent θ T) a) :
    Process.Specification N p (responseHorizon θ) (processExponent θ T)
      (referenceData θ T N p) := by
  unfold referenceData
  rw [dif_pos h]
  exact h.choose_spec

theorem referenceDataReal_eq {θ T : ℝ} {N : ℕ} {p : ℝ} (hp : 0 < p ∧ p < 1) :
    referenceDataReal θ T N p = referenceData θ T N ⟨p, hp⟩ := by
  unfold referenceDataReal
  rw [dif_pos hp]

/-- The selected process agrees with every recursion solution on the horizon. -/
theorem referenceData_agree {θ T : ℝ} (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    {N : ℕ} (hN : processThreshold θ T ≤ N) {p : ℝ}
    (hp₀ : T⁻¹ * (N : ℝ) ^ (-θ) < p) (hp₁ : p < T * (N : ℝ) ^ (-θ)) :
    ∃ hp : 0 < p ∧ p < 1,
      Process.Specification N ⟨p, hp⟩ (responseHorizon θ) (processExponent θ T)
        (referenceData θ T N ⟨p, hp⟩) ∧
      ∀ b : Process.Data, Process.Recursion N ⟨p, hp⟩ (responseHorizon θ) b →
        Process.AgreeThrough (responseHorizon θ) (referenceData θ T N ⟨p, hp⟩) b := by
  obtain ⟨hp, a, ha, huniq⟩ := (processSelection_spec hθlo hθhi hT).2.2 N hN p hp₀ hp₁
  have hspec := referenceData_spec (θ := θ) (T := T) ⟨a, ha⟩
  refine ⟨hp, hspec, ?_⟩
  intro b hb
  have h₁ := huniq (referenceData θ T N ⟨p, hp⟩) hspec.toRecursion
  have h₂ := huniq b hb
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · rw [← h₁.1 m hm, h₂.1 m hm]
  · rw [← h₁.2 m hm, h₂.2 m hm]

end MajorityDynamics.Idealized.LinearResponse
