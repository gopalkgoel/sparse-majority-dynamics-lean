import MajorityDynamics.Binomial.ExpansionError

/-! # Appendix A.2: the full uniform different-trial tilted expansion -/

noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators
namespace MajorityDynamics.Binomial.Approximation

set_option maxHeartbeats 1200000 in
/-- The original A.2 endpoint, modulo only the cited scalar Chernoff bound. -/
theorem tilted_expansion : TiltedExpansionTheorem := by
  intro θ T hθlo hθhi hT d hd r M strict c e
  let D := ∑ i, e i
  let Cfin := 12 * |c| * (d : ℝ) ^ 2 + 256 * |c| * d * T
  let A := 4 * |c| * (2 * T) ^ D * d * (3 + 4 * d * T) + 1
  have hT0 : 0 < T := by linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hCfin : 0 ≤ Cfin := by dsimp [Cfin]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨Cfin + T + 1, by positivity, ?_⟩
  have hevent : ∀ᶠ n : ℕ in atTop,
      (0 < n ∧ 1 + 8 * T ^ 2 + 128 * d * T ≤ Real.log n ∧
        ∀ p : Probability, Density θ T n p →
          (Real.log n) ^ 3 ≤ scale n p ∧ (p : ℝ) * scale n p ≤ 1) ∧
      A * (n : ℝ) ^ (D + 1) * Real.exp (-((Real.log n) ^ 2) / (32 * T + 4)) ≤ 1 / n :=
    (eventually_logarithmic_window θ T d hθlo hθhi hT0).and
      (polynomial_log_tail A (32 * T + 4) (D + 1) hA (by positivity))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hevent
  refine ⟨n₀, ?_⟩
  intro n hn p hp ref old new href hpositive htrials q₀ q₁ hprobs htilt
  dsimp only
  obtain ⟨⟨hnpos, hlog, hscales⟩, htailpoly⟩ := hn₀ n hn
  have hn1 : 1 ≤ n := hnpos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnr1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  let s := scale n p
  let l := Real.log (n : ℝ)
  let β := tiltDifference p ref old new q₀ q₁
  let center : Fin d → ℝ := fun i => (p : ℝ) * ref i
  let δ := likelihoodErrorBound old new center (fun _ => s * l)
  have hs : 0 < s := Real.sqrt_pos.mpr (mul_pos p.property.1 hn0)
  have hsquare : s ^ 2 = (p : ℝ) * n := Real.sq_sqrt (mul_nonneg p.property.1.le hn0.le)
  have hw := logarithmic_window_conditions (d : ℝ) T n p s l ‖β‖ hd1 hT.le hn0
    p.property.1 p.property.2.le hs hsquare hlog (hscales p hp).1 (hscales p hp).2
    (norm_nonneg _) htilt.le
  obtain ⟨hlarge, hsmall, hL1, hLupper, hlogT, hls, hb, hδsmall, hB1⟩ := hw
  have hl1 : 1 ≤ l := by dsimp [l]; nlinarith
  have hl0 : 0 ≤ l := by linarith
  have hs1 : 1 ≤ s := hl1.trans hls
  have hcenter : ∀ i, 0 ≤ center i := fun i => mul_nonneg p.property.1.le (Nat.cast_nonneg _)
  have hgeom (η : Fin d → ℕ) (q : Fin d → Probability)
      (hη : ∀ i, |(η i : ℝ) - ref i| < T * n / s)
      (hq : ∀ i, |(q i : ℝ) - p| < T * (p : ℝ) / s) (i : Fin d) :
      (n : ℝ) / (2 * T) ≤ η i ∧ (η i : ℝ) ≤ 2 * T * n ∧
      (n : ℝ) / (4 * T) ≤ (η i : ℝ) - center i ∧
      |(η i : ℝ) * (q i : ℝ) - center i| ≤ 3 * T ^ 2 * s ∧
      (η i : ℝ) * (q i : ℝ) ≤ 4 * T * s ^ 2 := by
    apply trial_geometry T n p s (ref i) (η i) (q i) hT.le hn0 p.property.1 hs
      hsquare hlarge hsmall _ (href i).2.le (hη i).le (hq i).le
    simpa only [div_eq_mul_inv, mul_comm] using (href i).1.le
  have hg₀ := hgeom old q₀ (fun i => (htrials i).1) (fun i => (hprobs i).1)
  have hg₁ := hgeom new q₁ (fun i => (htrials i).2) (fun i => (hprobs i).2)
  have hremain0 : 0 < (n : ℝ) / (4 * T) := by positivity
  have hc₀ : ∀ i, center i < old i := fun i => sub_pos.mp (hremain0.trans_le (hg₀ i).2.2.1)
  have hc₁ : ∀ i, center i < new i := fun i => sub_pos.mp (hremain0.trans_le (hg₁ i).2.2.1)
  have hLhalf : s * l ≤ ((n : ℝ) / (4 * T)) / 2 := by
    convert hLupper using 1
    ring
  have hL₀ : ∀ i, s * l ≤ ((old i : ℝ) - center i) / 2 :=
    fun i => hLhalf.trans (div_le_div_of_nonneg_right (hg₀ i).2.2.1 (by norm_num))
  have hL₁ : ∀ i, s * l ≤ ((new i : ℝ) - center i) / 2 :=
    fun i => hLhalf.trans (div_le_div_of_nonneg_right (hg₁ i).2.2.1 (by norm_num))
  have hRref : ∀ i, center i ≤ 2 * T * n := by
    intro i
    have h := mul_le_mul_of_nonneg_right p.property.2.le (show (0 : ℝ) ≤ ref i by positivity)
    have hr := (href i).2
    dsimp [center]
    nlinarith
  have hR₀ : ∀ i, (old i : ℝ) - center i ≤ 2 * T * n := fun i =>
    (sub_le_self _ (hcenter i)).trans (hg₀ i).2.1
  have hR₁ : ∀ i, (new i : ℝ) - center i ≤ 2 * T * n := fun i =>
    (sub_le_self _ (hcenter i)).trans (hg₁ i).2.1
  have hLR : s * l ≤ 2 * T * n := by
    have h := hL₀ ⟨0, hd⟩
    have hr := hR₀ ⟨0, hd⟩
    nlinarith [hcenter ⟨0, hd⟩]
  have hδ : δ ≤ 32 * d * T * (p : ℝ) * l ^ 2 :=
    likelihoodErrorBound_le old new center T n p s l hT0 hn0 hsquare
      (fun i => (hg₀ i).2.2.1) (fun i => (hg₁ i).2.2.1)
  have hexp := tilted_window M strict p ref old new q₀ q₁ c e (s * l) (2 * T * n)
    hL1 hLR hc₀ hc₁ hL₀ hL₁ hRref hR₀ hR₁ hb (hδ.trans hδsmall)
  dsimp only at hexp
  have ht₀ := rectangle_tail_of_trial_geometry old q₀ center T s l hT0 hs hlogT hls
    (fun i => (hpositive i).1) (fun i => (hg₀ i).2.2.2.1) (fun i => (hg₀ i).2.2.2.2)
  have ht₁ := rectangle_tail_of_trial_geometry new q₁ center T s l hT0 hs hlogT hls
    (fun i => (hpositive i).2) (fun i => (hg₁ i).2.2.2.1) (fun i => (hg₁ i).2.2.2.2)
  have hfinite := finite_expansion_error |c| d T p s l ‖β‖ δ D
    (abs_nonneg _) hd0 hT0.le p.property.1.le hs.le hl1 hδ
  have htail := tail_expansion_error |c| d T n ‖β‖ (d * ‖β‖ * (s * l))
    ((law old q₀).real (rectangle center (fun _ => s * l))ᶜ)
    ((law new q₁).real (rectangle center (fun _ => s * l))ᶜ)
    (Real.exp (-(l ^ 2) / (32 * T + 4))) D (abs_nonneg _) hd0 hT0.le hnr1
    (norm_nonneg _) hB1 (by positivity) (hb.trans (by norm_num)) (Real.exp_pos _).le ht₀ ht₁
  have htail' := htail.trans htailpoly
  let E := max (p : ℝ) (‖β‖ ^ 2 * s ^ 2 * l ^ 2) * s ^ D * l ^ (2 + D)
  have hE : (p : ℝ) ≤ E := by
    have hsD : 1 ≤ s ^ D := one_le_pow₀ hs1
    have hlD : 1 ≤ l ^ (2 + D) := one_le_pow₀ hl1
    have hmax : (p : ℝ) ≤ max (p : ℝ) (‖β‖ ^ 2 * s ^ 2 * l ^ 2) := le_max_left _ _
    dsimp [E]
    nlinarith [mul_nonneg (show 0 ≤ max (p : ℝ) (‖β‖ ^ 2 * s ^ 2 * l ^ 2) by positivity)
      (show 0 ≤ s ^ D - 1 by linarith), mul_nonneg
      (show 0 ≤ max (p : ℝ) (‖β‖ ^ 2 * s ^ 2 * l ^ 2) * s ^ D by positivity)
      (show 0 ≤ l ^ (2 + D) - 1 by linarith)]
  have hinv : 1 / (n : ℝ) ≤ T * E :=
    (density_inverse_size θ T n p hθhi hT0 hn1 hp).trans (mul_le_mul_of_nonneg_left hE hT0.le)
  have hfinite' : 12 * (|c| * (s * l) ^ D) * (d * ‖β‖ * (s * l)) ^ 2 +
      8 * (|c| * (s * l) ^ D) * δ ≤ Cfin * E := by
    convert hfinite using 1
    dsimp [Cfin, E]
    ring
  have hfinal : |moment M strict p ref new q₁ (monomial c e) -
      moment M strict p ref old q₀ (monomial c e) -
      (∑ i, β i * moment M strict p ref old q₀ (fun x => x i * monomial c e x)) +
      (∑ i, β i * (∫ a, centered p ref a i ∂law old q₀) * moment M strict p ref old q₀ (monomial c e))|
      ≤ (Cfin + T + 1) * E := by
    have hE0 : 0 ≤ E := p.property.1.le.trans hE
    linarith only [hexp, hfinite', htail', hinv, hE0]
  convert hfinal using 1
  dsimp [E, D, β, s, l, scale]
  rw [Real.sq_sqrt (mul_nonneg p.property.1.le hn0.le)]
  ring

end MajorityDynamics.Binomial.Approximation
