import MajorityDynamics.GraphProcess.EnumerationBounds.Asymptotics
import MajorityDynamics.Probability.FixedSizeExponential.Bounds

noncomputable section
open Filter Set
open scoped Topology
namespace MajorityDynamics.GraphProcess.RowConcentration

/-- Logarithmic exponential tails dominate every fixed polynomial, uniformly. -/
theorem eventually_log_tail {C c r b A : ℝ} (hC : 0 < C) (hc : 0 < c)
    (hr : 1 < r) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      C * (N : ℝ)^b * Real.exp (-c * (Real.log (N : ℝ))^r) ≤ (N : ℝ)^(-A) := by
  obtain ⟨X, _, hX⟩ := EnumerationBounds.eventually_mul_rpow_le
    (A := |Real.log C| + |b| + |A|) (a := 1) (b := r) hr hc
  have ht := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((eventually_ge_atTop (1 : ℕ)).and (ht.eventually_ge_atTop (max 1 X)))
  refine ⟨N₀, ?_⟩
  intro N hN
  obtain ⟨hN1, hlog⟩ := hN₀ N hN
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hlog1 : 1 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans hlog
  have hpow := hX (Real.log (N : ℝ)) ((le_max_right _ _).trans hlog)
  rw [Real.rpow_one] at hpow
  have hcLog : Real.log C ≤ |Real.log C| * Real.log (N : ℝ) := by
    exact (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hlog1)
  have hb := mul_le_mul_of_nonneg_right (le_abs_self b) (by linarith : 0 ≤ Real.log (N : ℝ))
  have ha := mul_le_mul_of_nonneg_right (le_abs_self A) (by linarith : 0 ≤ Real.log (N : ℝ))
  rw [Real.rpow_def_of_pos hNp, Real.rpow_def_of_pos hNp]
  rw [← Real.exp_log hC, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The manuscript's degree tolerance is eventually at most the mean-degree scale. -/
theorem eventually_tolerance_le {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      0 < p ∧ 0 < (N : ℝ) ∧ 1 ≤ Real.log (N : ℝ) ∧
      Real.sqrt (p*N)*(Real.log (N : ℝ))^((2:ℝ)/3) ≤ p*N := by
  obtain ⟨N₀, hN₀⟩ := Probability.FixedSizeExponential.eventually_weight_regime θ T hθlo hθhi hT
  refine ⟨max N₀ 1, ?_⟩
  intro N hN p hlo hhi
  have hw := hN₀ N ((le_max_left _ _).trans hN) p ⟨hlo,hhi⟩
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hxp : 0 < p*N := mul_pos hw.1 hNp
  have hs := Real.sq_sqrt hxp.le
  have hl : (Real.log (N : ℝ))^((2:ℝ)/3) ≤ Real.log (N : ℝ) := by
    calc
      _ ≤ (Real.log (N : ℝ))^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hw.2.2.1 (by norm_num)
      _ = _ := Real.rpow_one _
  have hls : Real.log (N : ℝ) ≤ Real.sqrt (p*N) := by
    nlinarith [Real.sqrt_nonneg (p*N)]
  refine ⟨hw.1, hNp, hw.2.2.1, ?_⟩
  calc
    _ ≤ Real.sqrt (p*N)*Real.sqrt (p*N) :=
      mul_le_mul_of_nonneg_left (hl.trans hls) (Real.sqrt_nonneg _)
    _ = p*N := by nlinarith only [hs]

/-- A fixed fourth-power tail absorbs the expectation bias of bounded row sums. -/
theorem eventually_mass_bias {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      (N : ℝ)^2 * (N : ℝ)^(-(4:ℝ)) ≤
        ((N : ℝ)^2*p/Real.sqrt (N : ℝ)*Real.log (N : ℝ))/2 := by
  obtain ⟨N₁,h₁⟩ := eventually_tolerance_le hθlo hθhi hT
  obtain ⟨N₂,h₂⟩ := EnumerationBounds.eventually_window hθlo hθhi hT
    (L := 1) zero_lt_one (U := 1) zero_lt_one (M := 4) (by norm_num)
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN p hlo hhi
  have ha := h₁ N ((le_max_left _ _).trans hN) p hlo hhi
  have hb := h₂ N ((le_max_right _ _).trans hN) p hlo hhi
  have hs : 2 ≤ Real.sqrt (N : ℝ) := by
    nlinarith [Real.sq_sqrt ha.2.1.le, Real.sqrt_nonneg (N : ℝ)]
  have hid : (N : ℝ)^2*p/Real.sqrt (N : ℝ) = (p*N)*Real.sqrt (N : ℝ) := by
    apply (div_eq_iff (Real.sqrt_pos.mpr ha.2.1).ne').mpr
    calc
      _ = p*(N:ℝ)*(Real.sqrt (N:ℝ))^2 := by rw [Real.sq_sqrt ha.2.1.le]; ring
      _ = _ := by ring
  have hm : 2 ≤ (N : ℝ)^2*p/Real.sqrt (N : ℝ)*Real.log (N : ℝ) := by
    rw [hid]
    have hh : 2 ≤ (p*N)*Real.sqrt (N : ℝ) := by nlinarith [hb.2.2.2.1]
    exact hh.trans (le_mul_of_one_le_right (by positivity) ha.2.2.1)
  have hpw : (N : ℝ)^2 * (N : ℝ)^(-(4:ℝ)) ≤ 1 := by
    rw [Real.rpow_neg ha.2.1.le]
    norm_num
    have hN0 := ha.2.1
    apply (div_le_one (by positivity : 0 < (N : ℝ)^4)).mpr
    nlinarith [sq_nonneg ((N : ℝ)^2-1)]
  linarith

end MajorityDynamics.GraphProcess.RowConcentration

/-- info: 'MajorityDynamics.GraphProcess.RowConcentration.eventually_log_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowConcentration.eventually_log_tail

/-- info: 'MajorityDynamics.GraphProcess.RowConcentration.eventually_tolerance_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowConcentration.eventually_tolerance_le

/-- info: 'MajorityDynamics.GraphProcess.RowConcentration.eventually_mass_bias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowConcentration.eventually_mass_bias
