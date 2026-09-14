import MajorityDynamics.GraphProcess.RowConcentration.Main
import MajorityDynamics.Probability.FixedSizeExponential.SparseBounds
import MajorityDynamics.GraphProcess.EnumerationBounds.BandAsymptotics

/-! Original R1/R2/R3 row concentration, uniformly on the sparse range. -/
noncomputable section
open Filter Set MeasureTheory ProbabilityTheory
open scoped BigOperators Classical Topology
namespace MajorityDynamics.GraphProcess.RowConcentration
open Universal
universe u

theorem eventually_tolerance_le_sparse {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-(1/2 : ℝ)) →
      0 < p ∧ 0 < (N : ℝ) ∧ 1 ≤ Real.log (N : ℝ) ∧
      Real.sqrt (p*N)*(Real.log (N : ℝ))^((2:ℝ)/3) ≤ p*N := by
  obtain ⟨N₀, hN₀⟩ := Probability.FixedSizeExponential.eventually_weight_regime_sparse θ T hθlo hθhi hT
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
theorem eventually_mass_bias_sparse {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-(1/2 : ℝ)) →
      (N : ℝ)^2 * (N : ℝ)^(-(4:ℝ)) ≤
        ((N : ℝ)^2*p/Real.sqrt (N : ℝ)*Real.log (N : ℝ))/2 := by
  obtain ⟨N₁,h₁⟩ := eventually_tolerance_le_sparse hθlo hθhi hT
  obtain ⟨N₂,h₂⟩ := EnumerationBounds.eventually_band_window (η := 1/2) (by norm_num) hθhi hT
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

theorem uniform_degree_regime_sparse {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-(1/2 : ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(q s t : ℝ)-p| ≤ T*p/Real.sqrt (p*N)) →
      0 < (N : ℝ) ∧ 0 < p ∧ 1 ≤ Real.log (N : ℝ) ∧
      Real.sqrt (p*N)*(Real.log (N : ℝ))^((2:ℝ)/3) ≤ p*N ∧
      (∀ s t, (Local.trials y.sizes s t : ℝ)*(q s t : ℝ) ≤ 2*p*N ∧
        |p*(y.sizes t : ℝ)-(Local.trials y.sizes s t : ℝ)*(q s t : ℝ)| ≤
          Real.sqrt (p*N)*(Real.log (N : ℝ))^((2:ℝ)/3)/2) := by
  obtain ⟨N₁,h₁⟩ := eventually_tolerance_le_sparse hθlo hθhi hT
  obtain ⟨N₂,h₂⟩ := EnumerationBounds.eventually_band_window (η := 1/2) (by norm_num) hθhi hT
    (L := (2*T)^2) (by positivity) (U := 1) zero_lt_one (M := 2*T) (by linarith)
  have ht := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<2/3)).comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop :
      Filter.Tendsto (fun N : ℕ => (N : ℝ)) Filter.atTop Filter.atTop))
  obtain ⟨N₃,h₃⟩ := Filter.eventually_atTop.mp (ht.eventually_ge_atTop (2*(T+1)))
  refine ⟨max N₁ (max N₂ N₃), ?_⟩
  intro N hN V inst hcard p hlo hhi y q hsizes htilt
  have ha := h₁ N ((le_max_left _ _).trans hN) p hlo hhi
  have hb := h₂ N ((le_max_left _ _).trans ((le_max_right _ _).trans hN)) p hlo hhi
  have hc := h₃ N ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  refine ⟨ha.2.1, ha.1, ha.2.2.1, ha.2.2.2, ?_⟩
  intro s t
  subst N
  have hf := finite_mean_bounds y q hT ha.1 hb.2.2.2.2 hb.2.2.1 hb.2.2.2.1 hsizes htilt s t
  refine ⟨hf.1, hf.2.trans ?_⟩
  have hh := mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg (p*Fintype.card V))
  dsimp only [Function.comp_apply] at hh
  nlinarith

theorem uniform_degree_tail_sparse {θ T φ A : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-(1/2 : ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(q s t : ℝ)-p| ≤ T*p/Real.sqrt (p*N)) →
      Conditioning y q φ →
      (conditionedLaw y q).real {d | ¬ R1 y p d} ≤ (N:ℝ)^(-A) := by
  obtain ⟨N₁,h₁⟩ := uniform_degree_regime_sparse n hθlo hθhi hT
  obtain ⟨N₂,h₂⟩ := eventually_log_tail
    (C := (2:ℝ)^(n+1)*2/φ) (c := 3/80) (r := 4/3) (b := 1) (A := A)
    (by positivity) (by norm_num) (by norm_num)
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN V inst hcard p hlo hhi y q hsizes htilt hc
  have hr := h₁ N ((le_max_left _ _).trans hN) V hcard p hlo hhi y q hsizes htilt
  have ht := h₂ N ((le_max_right _ _).trans hN)
  rw [Real.rpow_one] at ht
  subst N
  exact (degree_tail y q hφ hc hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2).trans (by simpa only [neg_div] using ht)

theorem uniform_concentration_sparse {θ T φ A : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T * (N : ℝ)^(-(1/2 : ℝ)) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(q s t : ℝ)-p| ≤ T*p/Real.sqrt (p*N)) →
      Conditioning y q φ →
      (conditionedLaw y q).real {d | ¬ Good y p q d} ≤ (N : ℝ)^(-A) := by
  let h : ℝ := Fintype.card (History (n + 1))
  have hh : 0 < h := by
    dsimp [h]
    rw [history_card]
    positivity
  obtain ⟨N₁, h₁⟩ := uniform_degree_tail_sparse (A := (4 : ℝ)) n hθlo hθhi hT hφ
  obtain ⟨N₂, h₂⟩ := uniform_degree_tail_sparse (A := A + 1) n hθlo hθhi hT hφ
  obtain ⟨N₃, h₃⟩ := eventually_tolerance_le_sparse hθlo hθhi hT
  obtain ⟨N₄, h₄⟩ := eventually_mass_bias_sparse hθlo hθhi hT
  obtain ⟨N₅, h₅⟩ := eventually_log_tail
    (C := 4*h) (c := 2) (r := 2) (b := 0) (A := A+1)
    (by positivity) (by norm_num) (by norm_num)
  obtain ⟨N₆, h₆⟩ := eventually_log_tail
    (C := 4*h^2) (c := 1/8) (r := 2) (b := 0) (A := A+1)
    (by positivity) (by norm_num) (by norm_num)
  obtain ⟨N₇, h₇⟩ := exists_nat_gt (3 + 2*h^2)
  refine ⟨max N₁ (max N₂ (max N₃ (max N₄ (max N₅ (max N₆ N₇))))), ?_⟩
  intro N hN V inst hcard p hlo hhi y q hsizes htilt hc
  have hd₄ := h₁ N (by omega) V hcard p hlo hhi y q hsizes htilt hc
  have hd := h₂ N (by omega) V hcard p hlo hhi y q hsizes htilt hc
  have hr := h₃ N (by omega) p hlo hhi
  have hb := h₄ N (by omega) p hlo hhi
  have ht₂ := h₅ N (by omega)
  have ht₃ := h₆ N (by omega)
  simp only [Real.rpow_zero, mul_one, Real.rpow_two] at ht₂ ht₃
  have hC : 3 + 2*h^2 ≤ (N : ℝ) :=
    h₇.le.trans (by exact_mod_cast (show N₇ ≤ N by omega))
  have hNr := hr.2.1
  have hNN : 0 < Fintype.card V := by rw [hcard]; exact_mod_cast hNr
  have hlog : 0 ≤ Real.log (Fintype.card V) := by rw [hcard]; linarith [hr.2.2.1]
  have htol : Real.sqrt (p * Fintype.card V) *
      (Real.log (Fintype.card V)) ^ (2 / 3 : ℝ) ≤ p * Fintype.card V := by
    simpa only [hcard] using hr.2.2.2
  have hbias : (Fintype.card V : ℝ)^2 * (conditionedLaw y q).real {d | ¬ R1 y p d} ≤
      ((Fintype.card V : ℝ)^2 * p / Real.sqrt (Fintype.card V) *
        Real.log (Fintype.card V)) / 2 := by
    rw [hcard]
    exact (mul_le_mul_of_nonneg_left hd₄ (sq_nonneg _)).trans hb
  have hs := R2_failure y q hφ hc hNN hlog
  have hm := R3_failure y hr.1 q hφ hc hNN hlog htol hbias
  have hj := failure_union_le y p q hφ hc
  rw [hcard] at hs hm
  change (conditionedLaw y q).real {d | ¬ R2 y q d} ≤
    (h*2)*(2*Real.exp (-2*(Real.log (N : ℝ))^2)) at hs
  change (conditionedLaw y q).real {d | ¬ R3 y p q d} ≤
    (h^2*2)*((conditionedLaw y q).real {d | ¬ R1 y p d} +
      2*Real.exp (-(Real.log (N : ℝ))^2/8)) at hm
  have he₃ : -(1/8 : ℝ)*(Real.log (N : ℝ))^2 =
      -(Real.log (N : ℝ))^2/8 := by ring
  rw [he₃] at ht₃
  have hs' : (conditionedLaw y q).real {d | ¬ R2 y q d} ≤ (N : ℝ)^(-(A+1)) := by
    nlinarith
  have hmd := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ h^2*2)
  have hout : (conditionedLaw y q).real {d | ¬ Good y p q d} ≤
      (3+2*h^2)*(N : ℝ)^(-(A+1)) := by nlinarith
  exact hout.trans (polynomial_absorption hNr hC)

end MajorityDynamics.GraphProcess.RowConcentration

