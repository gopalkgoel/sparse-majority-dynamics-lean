import MajorityDynamics.Idealized.CriticalDay.Target

noncomputable section
open Filter Topology
open scoped BigOperators
namespace MajorityDynamics.Idealized.CriticalDay
open Universal LinearResponse PerturbedTilt
open Binomial.Approximation (Density scale)

/-- The current-size centering cancels the first-order epsilon term, even
though its normalized coefficient has constant rather than vanishing size. -/
theorem centered_target (θ T δ : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hδ : 0 < δ) (n ell : ℕ)
    (hk : (n : ℝ) + 1 = 1 / (1 - θ)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
    ∀ p : Binomial.Probability, Density θ T N p →
    ∀ a : Process.Data, Process.Specification N p (responseHorizon θ) ell a →
    ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
    ∀ η : History (n + 1) → ℤ, ∀ e : History (n + 1) → History (n + 1) → ℤ,
    FaithfulNumericalData N (p : ℝ) T δ τ a n η e →
    ∀ s t, |((e s t : ℝ) / (η s : ℝ) - (p : ℝ) * (η t : ℝ)) /
      scale N p - ν n t * μ n s t| ≤ K * (N : ℝ) ^ (-targetRate θ δ) := by
  classical
  have hT0 : 0 < T := by linarith
  obtain ⟨F, hF, hfTarget⟩ := faithful_target θ T δ hθlo hθhi hT hδ n ell hk
  let R : ℝ := 1 + ∑ s : History (n + 1), ∑ t : History (n + 1),
    abs (2 * ν n t + |μ n s t|)
  let B := Real.sqrt T ^ (n + 1)
  have hR : 0 < R := by dsimp [R]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hRbound : ∀ s t, 2 * ν n t + |μ n s t| ≤ R := by
    intro s t
    have h1 := Finset.single_le_sum (fun t _ => abs_nonneg (2 * ν n t + |μ n s t|))
      (Finset.mem_univ t)
    have h2 := Finset.single_le_sum (fun s _ => show 0 ≤ ∑ t, abs (2 * ν n t + |μ n s t|) by positivity)
      (Finset.mem_univ s)
    dsimp [R]
    linarith [le_abs_self (2 * ν n t + |μ n s t|)]
  have hrate := targetRate_bounds (rate_pos hθlo hθhi) hδ
  refine ⟨R + T * B * F + T * B, by positivity, ?_⟩
  filter_upwards [hfTarget, faithful_geometry θ T δ hθlo hθhi hT hδ n ell hk,
    eventually_basic θ T hθlo hθhi hT,
    Process.eventually_level_sizes (n := n) θ T ell hθhi hT0,
    eventually_small θ T hθlo hθhi hT 0 ell (first_day_subcritical hθlo hθhi)]
    with N htarget hgeo hbasic hlev hsmall
  intro p hp a ha τ hτ hτT η e hf s t
  obtain ⟨hη, _, _, hrefpos⟩ := hgeo p hp a ha τ hτ hτT η e hf
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr hbasic.1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hbasic.1
  have hp0 := p.property.1
  have hS : 0 < scale N p := Real.sqrt_pos.mpr (by positivity)
  have hβ : 0 < betaScale N (p : ℝ) n := by unfold betaScale; positivity
  have hτ0 : 0 < τ := (inv_pos.mpr hT0).trans_le hτ
  have hspec := ha.estimates n (Nat.lt_of_succ_lt (critical_level_lt_horizon hk))
  have hsz := hlev.2 p hp (a.state n) hspec
  have hρr : targetRate θ δ < responseRate θ 0 := by
    have hh := hrate.2.1
    unfold rate at hh
    linarith [responseRate_pos hθlo hθhi (first_day_subcritical hθlo hθhi)]
  have hpowr : (N : ℝ) ^ (-responseRate θ 0) ≤ (N : ℝ) ^ (-targetRate θ δ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hpowδ : (N : ℝ) ^ (-δ) ≤ (N : ℝ) ^ (-targetRate θ δ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [hrate.2.2])
  let E := (N : ℝ) ^ (-targetRate θ δ)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hlog : 0 ≤ Real.log (N : ℝ) ^ ell / scale N p := by
    have := hbasic.2.1
    positivity
  have href : |((a.state n).edges s t / (a.state n).sizes s -
      (p : ℝ) * (a.state n).sizes t) / scale N p - ν n t * μ n s t| ≤ R * E := by
    exact (hspec.normalized_target hbasic.1 (by linarith [hbasic.2.1]) hrefpos
      (fun t => (hsz t).2.2.le) s t).trans
      (mul_le_mul (hRbound s t) (((hsmall p hp).2.2.1).trans hpowr) hlog hR.le)
  have hb : betaScale N (p : ℝ) n * scale N p ≤ B :=
    (critical_scale_bounds hbasic.1 hT0 hp hk hθhi).2
  have hshift : τ * betaScale N (p : ℝ) n * scale N p ≤ T * B := by
    nlinarith [mul_le_mul_of_nonneg_left hb hτ0.le,
      mul_le_mul_of_nonneg_right hτT hB.le]
  have htarg : |τ * betaScale N (p : ℝ) n * scale N p *
      (edgeTarget N (p : ℝ) a τ η e s t - ε n t)| ≤ T * B * F * E := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < τ * betaScale N (p : ℝ) n * scale N p)]
    have hh := mul_le_mul hshift (htarget p hp a ha τ hτ hτT η e hf s t)
      (abs_nonneg _) (by positivity : 0 ≤ T * B)
    simpa only [mul_assoc] using hh
  have hsq : scale N p ^ 2 = (p : ℝ) * N := Real.sq_sqrt (by positivity)
  have hsc : sizeScale N (p : ℝ) n = betaScale N (p : ℝ) n * N :=
    sizeScale_eq N hbasic.1 (p : ℝ) n
  have hfaith : |(p : ℝ) / scale N p *
      ((η t : ℝ) - (a.state n).sizes t - τ * sizeScale N (p : ℝ) n * ε n t)| ≤ T * B * E := by
    rw [abs_mul, abs_of_pos (div_pos p.property.1 hS)]
    have hh := mul_le_mul_of_nonneg_left (hf.sizes t) (div_pos p.property.1 hS).le
    have hid : (p : ℝ) / scale N p * (T * sizeScale N (p : ℝ) n * (N : ℝ) ^ (-δ)) =
        T * (betaScale N (p : ℝ) n * scale N p) * (N : ℝ) ^ (-δ) := by
      rw [hsc]
      field_simp
      nlinarith [hsq]
    rw [hid] at hh
    exact hh.trans (mul_le_mul (mul_le_mul_of_nonneg_left hb hT0.le) hpowδ
      (by positivity) (by positivity))
  have hid : ((e s t : ℝ) / (η s : ℝ) - (p : ℝ) * (η t : ℝ)) / scale N p - ν n t * μ n s t =
      (((a.state n).edges s t / (a.state n).sizes s - (p : ℝ) * (a.state n).sizes t) /
        scale N p - ν n t * μ n s t) +
      τ * betaScale N (p : ℝ) n * scale N p *
        (edgeTarget N (p : ℝ) a τ η e s t - ε n t) -
      (p : ℝ) / scale N p * ((η t : ℝ) - (a.state n).sizes t -
        τ * sizeScale N (p : ℝ) n * ε n t) := by
    dsimp [edgeTarget]
    rw [hsc, ← hsq]
    field_simp
    rw [hsq]
    ring
  rw [hid]
  have hh := (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add href htarg)) hfaith)
  convert hh using 1 <;> first | ring | rfl

end MajorityDynamics.Idealized.CriticalDay
