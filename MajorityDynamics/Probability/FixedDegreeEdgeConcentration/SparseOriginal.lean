import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Original
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.SparseRegime
noncomputable section
namespace MajorityDynamics.Probability.FixedDegreeEdgeConcentration
theorem eventually_originalScales_sparse {θ T : ℝ}
    (_hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ, SparseDensityWindow θ T p N → OriginalScales N p T := by
  have hT0 : 0 < T := by linarith
  obtain ⟨X,hX,hpow⟩ := GraphProcess.EnumerationBounds.eventually_mul_rpow_le
    (a:=(4:ℝ)/7) (b:=1) (A:=1) (B:=1/(2*T)) (by norm_num) (by positivity)
  obtain ⟨N₀,h₀⟩ := GraphProcess.EnumerationBounds.eventually_band_window (η:=(1/2:ℝ)) (by norm_num) hθhi hT (L:=max 1 X) (by positivity)
    (U:=1/(64*T^3)) (by positivity) (M:=16*T^2) (by positivity)
  refine ⟨N₀, ?_⟩
  intro N hN p hp
  have hw := h₀ N hN p hp.1 hp.2
  have hp0 := hw.2.1
  have hx : 1 ≤ p*N := (le_max_left _ _).trans hw.2.2.2.1
  have hx0 : 0 ≤ p*N := by positivity
  have he := hpow (p*N) ((le_max_right _ _).trans hw.2.2.2.1)
  simp only [one_mul, Real.rpow_one] at he
  have hp1 : p ≤ 1 := by
    apply hw.2.2.2.2.trans
    apply (div_le_iff₀ (by positivity : 0 < 64*T^3)).mpr
    have hT2 : 1 ≤ T^2 := by nlinarith
    have hT3 : 1 ≤ T^3 := by nlinarith [mul_le_mul_of_nonneg_right hT.le (sq_nonneg T)]
    nlinarith
  refine ⟨hT,hw.1,hw.2.1,hx,hp1,hw.2.2.1,by simpa [div_eq_mul_inv,mul_comm] using he,?_⟩
  have hsmall : 12*T^3*p ≤ 1 := by
    have hz := (le_div_iff₀ (by positivity : 0 < 64*T^3)).mp hw.2.2.2.2
    have hn : 0 ≤ T^3*p := by positivity
    nlinarith
  have hTx : 1 ≤ T*(p*N) := by nlinarith
  calc
    (2*T*(p*N))*(2*T*(p*N)+1) ≤ (2*T*(p*N))*(3*T*(p*N)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    _ = (12*T^3*p)*(p*N^2)/(2*T) := by field_simp; ring
    _ ≤ p*N^2/(2*T) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [mul_le_mul_of_nonneg_right hsmall (by positivity : 0 ≤ p*N^2)]

end MajorityDynamics.Probability.FixedDegreeEdgeConcentration
