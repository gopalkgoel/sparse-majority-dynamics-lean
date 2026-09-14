import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section
open Filter Topology MeasureTheory

namespace MajorityDynamics.Probability.ConditionedBinomialFourier.HighFrequency

/-- The literal fundamental frequency cube. -/
def cube (d : ℕ) : Set (Fin d → ℝ) := {t | ∀ i, |t i| ≤ Real.pi}

/-- Frequencies above the local Gaussian cutoff, inside the fundamental cube. -/
def region (d N : ℕ) (p δ : ℝ) : Set (Fin d → ℝ) :=
  {t | t ∈ cube d ∧ (N : ℝ) ^ δ / Real.sqrt ((N : ℝ) ^ 2 * p) < ‖t‖}

theorem cube_eq_Icc (d : ℕ) :
    cube d = Set.Icc (fun _ => -Real.pi) (fun _ => Real.pi) := by
  ext t
  simp only [cube, Set.mem_ofPred_eq, Set.mem_Icc, Pi.le_def, abs_le]
  exact forall_and

theorem measurableSet_cube (d : ℕ) : MeasurableSet (cube d) := by
  rw [cube_eq_Icc]
  exact measurableSet_Icc

theorem measurableSet_region (d N : ℕ) (p δ : ℝ) :
    MeasurableSet (region d N p δ) :=
  (measurableSet_cube d).inter (measurableSet_lt measurable_const continuous_norm.measurable)

theorem cube_volume_lt_top (d : ℕ) : volume (cube d) < ⊤ := by
  rw [cube_eq_Icc]
  exact isCompact_Icc.measure_lt_top

theorem cube_volume (d : ℕ) : volume.real (cube d) = (2 * Real.pi) ^ d := by
  change (volume (cube d)).toReal = _
  rw [cube_eq_Icc, Real.volume_Icc_pi_toReal]
  · simp [sub_neg_eq_add, two_mul]
  · intro i
    dsimp
    linarith [Real.pi_pos]

theorem region_volume_lt_top (d N : ℕ) (p δ : ℝ) : volume (region d N p δ) < ⊤ :=
  (measure_mono (fun _ h => h.1)).trans_lt (cube_volume_lt_top d)

/-- Stretched exponential decay absorbs an arbitrary fixed polynomial and constant. -/
theorem exp_eventually_le (a b B C : ℝ) (ha : 0 < a) (hb : 0 < b) (hC : 0 < C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      Real.exp (-a * (N : ℝ) ^ b) ≤ (N : ℝ) ^ (-B) / C := by
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (B / b) a ha).comp
    ((tendsto_rpow_atTop hb).comp hnat)
  have heq : ∀ᶠ N : ℕ in atTop,
      ((N : ℝ) ^ b) ^ (B / b) * Real.exp (-a * (N : ℝ) ^ b) =
        (N : ℝ) ^ B * Real.exp (-a * (N : ℝ) ^ b) := by
    filter_upwards [] with N
    rw [← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 2
    field_simp
  have ht' : Tendsto (fun N : ℕ => (N : ℝ) ^ B * Real.exp (-a * (N : ℝ) ^ b))
      atTop (𝓝 0) := ht.congr' heq
  have hevent := ht'.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < 1 / C))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hevent.and (eventually_ge_atTop (1 : ℕ)))
  refine ⟨N₀, fun N hN => ?_⟩
  have hpN : 0 < (N : ℝ) := by exact_mod_cast (hN₀ N hN).2
  have hpow : 0 < (N : ℝ) ^ B := Real.rpow_pos_of_pos hpN B
  have h := (hN₀ N hN).1.le
  rw [Real.rpow_neg hpN.le]
  apply (le_div_iff₀ hC).2
  apply (mul_le_mul_iff_right₀ hpow).1
  calc
    (N : ℝ) ^ B * (Real.exp (-a * (N : ℝ) ^ b) * C) =
        ((N : ℝ) ^ B * Real.exp (-a * (N : ℝ) ^ b)) * C := by ring
    _ ≤ (1 / C) * C := mul_le_mul_of_nonneg_right h hC.le
    _ = (N : ℝ) ^ B * ((N : ℝ) ^ B)⁻¹ := by field_simp

/-- At the literal cutoff the amplified gap is at least a stretched power of N. -/
theorem cutoff_gap {d N m : ℕ} {p δ T : ℝ} (hN : 1 ≤ N) (hp : 0 < p)
    (hδ : δ < 1 / 2) (hT : 0 < T) (hm : (N : ℝ) / T ≤ m)
    {t : Fin d → ℝ} (ht : t ∈ region d N p δ) :
    (N : ℝ) ^ (2 * δ) / T ≤
      (m : ℝ) * min (p * N * ‖t‖ ^ 2) 1 := by
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hden : 0 < (N : ℝ) ^ 2 * p := by positivity
  have hsqrt : 0 < Real.sqrt ((N : ℝ) ^ 2 * p) := Real.sqrt_pos.2 hden
  have hcut := (div_lt_iff₀ hsqrt).1 ht.2
  have hcut2 : ((N : ℝ) ^ δ) ^ 2 < (‖t‖ * Real.sqrt ((N : ℝ) ^ 2 * p)) ^ 2 :=
    (sq_lt_sq₀ (by positivity) (by positivity)).2 hcut
  have hpow : ((N : ℝ) ^ δ) ^ 2 = (N : ℝ) ^ (2 * δ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1
    ring
  rw [hpow, mul_pow, Real.sq_sqrt hden.le] at hcut2
  have hx : 0 ≤ p * N * ‖t‖ ^ 2 := by positivity
  have hm' : (N : ℝ) ≤ (m : ℝ) * T := (div_le_iff₀ hT).1 hm
  apply (div_le_iff₀ hT).2
  by_cases hsmall : p * N * ‖t‖ ^ 2 ≤ 1
  · rw [min_eq_left hsmall]
    have hh := mul_le_mul_of_nonneg_right hm' hx
    nlinarith [hcut2]
  · rw [min_eq_right (le_of_not_ge hsmall)]
    have hpown := Real.rpow_le_self_of_one_le hN1 (by linarith : 2 * δ ≤ 1)
    simpa using hpown.trans hm'

/-- A global amplified gap gives a uniform pointwise high-frequency envelope. -/
theorem point_envelope {d N m : ℕ} {p δ T c : ℝ}
    (hN : 1 ≤ N) (hp : 0 < p) (hδ : δ < 1 / 2) (hT : 0 < T) (hc : 0 < c)
    (hm : (N : ℝ) / T ≤ m) (F : (Fin d → ℝ) → ℂ)
    (hF : ∀ t ∈ cube d,
      ‖F t‖ ≤ Real.exp (-c * m * min (p * N * ‖t‖ ^ 2) 1))
    {t : Fin d → ℝ} (ht : t ∈ region d N p δ) :
    ‖F t‖ ≤ Real.exp (-(c / T) * (N : ℝ) ^ (2 * δ)) := by
  apply (hF t ht.1).trans
  apply Real.exp_le_exp.2
  have hg := mul_le_mul_of_nonneg_left (cutoff_gap hN hp hδ hT hm ht) hc.le
  calc
    -c * m * min (p * N * ‖t‖ ^ 2) 1 = -(c * (m * min (p * N * ‖t‖ ^ 2) 1)) := by ring
    _ ≤ -(c * ((N : ℝ) ^ (2 * δ) / T)) := neg_le_neg hg
    _ = -(c / T) * (N : ℝ) ^ (2 * δ) := by ring

/-- The ambient frequency domain has finite volume; measurable bounded functions
are integrable on its high-frequency part. -/
theorem integrableOn_region {d N : ℕ} {p δ : ℝ} (F : (Fin d → ℝ) → ℂ)
    (hFm : Measurable F) {C : ℝ} (hF : ∀ t ∈ region d N p δ, ‖F t‖ ≤ C) :
    IntegrableOn F (region d N p δ) := by
  apply Measure.integrableOn_of_bounded (region_volume_lt_top d N p δ).ne
    hFm.aestronglyMeasurable
  exact (ae_restrict_mem (measurableSet_region d N p δ)).mono fun t ht => hF t ht

/-- The polynomial lower bound for the local-CLT scale, uniformly for p≤1. -/
theorem atom_scale_lower {d N : ℕ} {p : ℝ} (hN : 0 < N) (hp : 0 < p) (hp1 : p ≤ 1) :
    (N : ℝ) ^ (-(d : ℝ)) ≤ ((N : ℝ) ^ 2 * p) ^ (-(d : ℝ) / 2) := by
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hn : 0 < (N : ℝ) ^ 2 * p := by positivity
  have hle : (N : ℝ) ^ 2 * p ≤ (N : ℝ) ^ 2 := by nlinarith [sq_nonneg (N : ℝ)]
  have hh := Real.rpow_le_rpow_of_nonpos hn hle (by have := Nat.cast_nonneg (α := ℝ) d; linarith : -(d : ℝ) / 2 ≤ 0)
  have heq : ((N : ℝ) ^ 2) ^ (-(d : ℝ) / 2) = (N : ℝ) ^ (-(d : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1
    ring
  rwa [heq] at hh

/-- Full point and integrated high-frequency decay, conditional only on a proved
global amplified characteristic-function bound. The original-law theorem
supplies that bound; this numerical lemma imports no probability estimates. -/
theorem uniform_decay (d : ℕ) (c T δ A : ℝ) (hc : 0 < c) (hT : 0 < T)
    (hδ0 : 0 < δ) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (p : ℝ) (m : ℕ) (F : (Fin d → ℝ) → ℂ),
      0 < p → p ≤ 1 → (N : ℝ) / T ≤ m →
      (∀ t ∈ cube d, ‖F t‖ ≤ Real.exp (-c * m * min (p * N * ‖t‖ ^ 2) 1)) →
      (∀ t ∈ region d N p δ, ‖F t‖ ≤ (N : ℝ) ^ (-A)) ∧
      ‖∫ t in region d N p δ, F t‖ ≤
        (N : ℝ) ^ (-A) * ((N : ℝ) ^ 2 * p) ^ (-(d : ℝ) / 2) := by
  let C : ℝ := volume.real (cube d) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨N₁, hN₁⟩ := exp_eventually_le (c / T) (2 * δ) A 1
    (by positivity) (by positivity) (by norm_num)
  obtain ⟨N₂, hN₂⟩ := exp_eventually_le (c / T) (2 * δ) (A + d) C
    (by positivity) (by positivity) hC
  refine ⟨max 1 (max N₁ N₂), fun N hN p m F hp hp1 hm hF => ?_⟩
  have hNpos : 1 ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hhN := (le_max_right 1 (max N₁ N₂)).trans hN
  have hpoint : ∀ t ∈ region d N p δ,
      ‖F t‖ ≤ Real.exp (-(c / T) * (N : ℝ) ^ (2 * δ)) :=
    fun _ ht => point_envelope hNpos hp hδ hT hc hm F hF ht
  constructor
  · intro t ht
    exact (hpoint t ht).trans (by simpa using hN₁ N ((le_max_left _ _).trans hhN))
  · calc
      ‖∫ t in region d N p δ, F t‖ ≤
          Real.exp (-(c / T) * (N : ℝ) ^ (2 * δ)) * volume.real (region d N p δ) :=
        norm_setIntegral_le_of_norm_le_const (region_volume_lt_top d N p δ) (fun t ht => hpoint t ht)
      _ ≤ Real.exp (-(c / T) * (N : ℝ) ^ (2 * δ)) * C := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        exact (measureReal_mono (fun _ h => h.1) (cube_volume_lt_top d).ne).trans
          (by dsimp [C]; linarith)
      _ ≤ (N : ℝ) ^ (-(A + d)) := by
        exact (le_div_iff₀ hC).1 (hN₂ N ((le_max_right _ _).trans hhN))
      _ = (N : ℝ) ^ (-A) * (N : ℝ) ^ (-(d : ℝ)) := by
        rw [← Real.rpow_add hN0]
        congr 1
        ring
      _ ≤ (N : ℝ) ^ (-A) * ((N : ℝ) ^ 2 * p) ^ (-(d : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left (atom_scale_lower (by omega) hp hp1) (by positivity)

end MajorityDynamics.Probability.ConditionedBinomialFourier.HighFrequency

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.HighFrequency.cube_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialFourier.HighFrequency.cube_volume

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.HighFrequency.measurableSet_region' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialFourier.HighFrequency.measurableSet_region

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.HighFrequency.exp_eventually_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialFourier.HighFrequency.exp_eventually_le

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.HighFrequency.cutoff_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialFourier.HighFrequency.cutoff_gap

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.HighFrequency.point_envelope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialFourier.HighFrequency.point_envelope

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.HighFrequency.integrableOn_region' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialFourier.HighFrequency.integrableOn_region

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.HighFrequency.atom_scale_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialFourier.HighFrequency.atom_scale_lower

/-- info: 'MajorityDynamics.Probability.ConditionedBinomialFourier.HighFrequency.uniform_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.ConditionedBinomialFourier.HighFrequency.uniform_decay
