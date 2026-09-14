import MajorityDynamics.Idealized.PerturbedEvolution.AdmissibilitySizes
import MajorityDynamics.Idealized.PerturbedTilt.Target

/-! LA5: the faithful mean target preserves the strict universal cone margin. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace MajorityDynamics.Idealized.PerturbedEvolution
open Universal LinearResponse PerturbedTilt
open Binomial.Approximation (Density scale)

theorem signed_sum_error {n : ℕ} (r : Fin (n + 1))
    (x y : History (n + 1) → ℝ) (E : ℝ) (he : ∀ t, |x t - y t| ≤ E) :
    |(∑ t, character r t * x t) - ∑ t, character r t * y t| ≤
      (Fintype.card (History (n + 1)) : ℝ) * E := by
  rw [← Finset.sum_sub_distrib]
  simp only [← mul_sub]
  simpa only [one_mul] using abs_sum_mul_le' (character r) (fun t => x t - y t)
    1 E (fun t => (abs_character r t).le) he

set_option maxHeartbeats 800000 in
theorem faithful_separation (θ T δ : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hδ : 0 < δ) (n ell : ℕ)
    (hk : (n : ℝ) + 1 < 1 / (1 - θ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      ∀ p : Binomial.Probability, Density θ T N p →
      ∀ a : Process.Data, Process.Specification N p (responseHorizon θ) ell a →
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ η : History (n + 1) → ℤ, ∀ e : History (n + 1) → History (n + 1) → ℤ,
      FaithfulNumericalData N (p : ℝ) T δ τ a n η e →
      ∀ s (r : Fin n), c * Local.edgeScale N (p : ℝ) ≤
        sign (bits (n + 1) s r.succ) * ∑ t, character r.castSucc t * (e s t : ℝ) := by
  classical
  obtain ⟨φ, ζ, hnd⟩ := universal_nondegeneracy_exists n
  obtain ⟨v, hv, hvle⟩ := RowLimits.finite_common_positive (ν n) (ν_positive n)
  obtain ⟨F, hF, htarget⟩ := faithful_target θ T δ hθlo hθhi hT hδ n ell hk
  let d : ℝ := Fintype.card (History (n + 1))
  let R : ℝ := 1 + ∑ s, ∑ t, abs (2 * ν n t + |μ n s t|)
  have hd : 0 < d := by dsimp [d]; exact_mod_cast Fintype.card_pos
  have hR : 0 < R := by dsimp [R]; positivity
  have hT0 : 0 < T := by linarith
  have hζ : 0 < ζ := hnd.separation_pos
  have hκ := responseRate_pos hθlo hθhi hk
  have hρ := (tiltRate_bounds hκ hδ).1
  have hRbound : ∀ s t, 2 * ν n t + |μ n s t| ≤ R := by
    intro s t
    have h1 := Finset.single_le_sum
      (fun t _ => abs_nonneg (2 * ν n t + |μ n s t|)) (Finset.mem_univ t)
    have h2 := Finset.single_le_sum
      (fun s _ => show 0 ≤ ∑ t, abs (2 * ν n t + |μ n s t|) by positivity)
      (Finset.mem_univ s)
    dsimp [R]
    linarith [le_abs_self (2 * ν n t + |μ n s t|)]
  refine ⟨v * ζ / 8, by positivity, ?_⟩
  filter_upwards [htarget, faithful_geometry θ T δ hθlo hθhi hT hδ n ell hk,
    eventually_basic θ T hθlo hθhi hT,
    eventually_small θ T hθlo hθhi hT n ell hk,
    eventually_rpow_neg_le (responseRate θ n) 1 hκ zero_lt_one,
    eventually_rpow_neg_le (responseRate θ n) (ζ / (4 * d * R)) hκ (by positivity),
    eventually_rpow_neg_le (tiltRate θ δ n) (ζ / (4 * d * T * F)) hρ (by positivity)]
      with N htarget hgeo hbasic hsmall hrate herr1 herr2
  intro p hp a ha τ hτ hτT η e hf s r
  obtain ⟨hη, hcast, _, hsz⟩ := hgeo p hp a ha τ hτ hτT η e hf
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hbasic.1
  have hp0 := p.property.1
  have hS : 0 < scale N p := Real.sqrt_pos.mpr (by positivity)
  have hηs : (0 : ℝ) < η s := by exact_mod_cast hη s
  have hτ0 : 0 < τ := (inv_pos.mpr hT0).trans_le hτ
  have hβ : 0 < betaScale N (p : ℝ) n := by unfold betaScale; positivity
  have hlog : 1 ≤ Real.log (N : ℝ) ^ ell := one_le_pow₀ (by linarith [hbasic.2.1])
  have hbeta : betaScale N (p : ℝ) n * scale N p ≤ 1 := by
    have := (hsmall p hp).2.2.2.trans hrate
    have := le_mul_of_one_le_right (mul_nonneg hβ.le hS.le) hlog
    exact this.trans ‹betaScale N (p : ℝ) n * scale N p * Real.log (N : ℝ) ^ ell ≤ 1›
  let b : ℝ := τ * betaScale N (p : ℝ) n * scale N p
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hbT : b ≤ T := by dsimp [b]; nlinarith
  let x : History (n + 1) → ℝ := fun t =>
    ((e s t : ℝ) / (η s : ℝ) - (p : ℝ) * (a.state n).sizes t) / scale N p - b * ε n t
  have hx : ∀ t, |x t - ν n t * μ n s t| ≤ ζ / (2 * d) := by
    intro t
    have hr := (ha.estimates n (Nat.lt_of_succ_lt (level_succ_lt_horizon hk))).normalized_target
      hbasic.1 (by linarith [hbasic.2.1]) hsz.ref_pos
      (fun t => (hsz.ref_upper t).le) s t
    have hr' : |((a.state n).edges s t / (a.state n).sizes s -
        (p : ℝ) * (a.state n).sizes t) / scale N p - ν n t * μ n s t| ≤
        ζ / (4 * d) := by
      have hc := mul_le_mul (hRbound s t) ((hsmall p hp).2.2.1.trans herr1)
        (by positivity : 0 ≤ Real.log (N : ℝ) ^ ell / scale N p) hR.le
      have hc' : R * (ζ / (4 * d * R)) = ζ / (4 * d) := by field_simp
      rw [hc'] at hc
      exact hr.trans hc
    have hf' := htarget p hp a ha τ hτ hτT η e hf s t
    have hfaith : |b * (edgeTarget N (p : ℝ) a τ η e s t - ε n t)| ≤ ζ / (4 * d) := by
      rw [abs_mul, abs_of_nonneg hb0]
      have hc := mul_le_mul hbT (hf'.trans (mul_le_mul_of_nonneg_left herr2 hF.le))
        (abs_nonneg _) hT0.le
      have hc' : T * (F * (ζ / (4 * d * T * F))) = ζ / (4 * d) := by field_simp
      rw [hc'] at hc
      exact hc
    have hsq : scale N p ^ 2 = (p : ℝ) * N := Real.sq_sqrt (by positivity)
    have hid : x t - ν n t * μ n s t =
        (((a.state n).edges s t / (a.state n).sizes s -
          (p : ℝ) * (a.state n).sizes t) / scale N p - ν n t * μ n s t) +
        b * (edgeTarget N (p : ℝ) a τ η e s t - ε n t) := by
      dsimp [x, b, edgeTarget]
      change _ = _ + τ * betaScale N (p : ℝ) n * scale N p *
        (((e s t : ℝ) / (η s : ℝ) - (a.state n).edges s t / (a.state n).sizes s) /
          (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)) - ε n t)
      rw [← hsq]
      field_simp
      ring
    rw [hid]
    calc
      _ ≤ ζ / (4 * d) + ζ / (4 * d) := (abs_add_le _ _).trans (add_le_add hr' hfaith)
      _ = _ := by ring
  have hsum := signed_sum_error r.castSucc x (fun t => ν n t * μ n s t)
    (ζ / (2 * d)) hx
  have hsumBound : |(∑ t, character r.castSucc t * x t) -
      ∑ t, character r.castSucc t * (ν n t * μ n s t)| ≤ ζ / 2 := by
    convert hsum using 1
    dsimp [d]
    field_simp
  have href : ∑ t, character r.castSucc t * ((a.state n).sizes t : ℝ) = 0 :=
    Process.symmetric_imbalance_eq_zero (a.state n)
      (ha.symmetry n (Nat.lt_of_succ_lt (level_succ_lt_horizon hk))) r.castSucc
  have hsumx : (∑ t, character r.castSucc t * x t) =
      (∑ t, character r.castSucc t * (e s t : ℝ)) / ((η s : ℝ) * scale N p) := by
    dsimp [x]
    simp only [mul_sub, ← mul_div_assoc, Finset.sum_sub_distrib, ← Finset.sum_div]
    have hid1 : (∑ t, character r.castSucc t * ((p : ℝ) * (a.state n).sizes t)) =
        (p : ℝ) * ∑ t, character r.castSucc t * ((a.state n).sizes t : ℝ) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro t _; ring
    have hid2 : (∑ t, character r.castSucc t * (b * ε n t)) =
        b * ∑ t, character r.castSucc t * ε n t := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro t _; ring
    rw [hid1, href, mul_zero, sub_zero, hid2, ε_earlier_signed_sum,
      mul_zero, sub_zero, div_div]
  rw [hsumx] at hsumBound
  have hsep := hnd.separation s r
  change ζ ≤ sign (bits (n + 1) s r.succ) *
    ∑ t, character r.castSucc t * (ν n t * μ n s t) at hsep
  have hnormalized : ζ / 2 ≤ sign (bits (n + 1) s r.succ) *
      ((∑ t, character r.castSucc t * (e s t : ℝ)) / ((η s : ℝ) * scale N p)) := by
    rcases abs_le.mp hsumBound with ⟨hlo, hhi⟩
    cases hbit : bits (n + 1) s r.succ <;> simp only [hbit, sign_false, sign_true] at *
      <;> linarith
  have hmargin := (le_div_iff₀ (mul_pos hηs hS)).mp
    (show ζ / 2 ≤ (sign (bits (n + 1) s r.succ) *
      ∑ t, character r.castSucc t * (e s t : ℝ)) / ((η s : ℝ) * scale N p) by
        simpa only [mul_div_assoc] using hnormalized)
  have hl := hsz.sizes_lower s
  rw [hcast s] at hl
  have hvl : (N : ℝ) * v / 4 ≤ (η s : ℝ) := by
    have := mul_le_mul_of_nonneg_left (hvle s) hNr.le
    linarith
  have hscl : Local.edgeScale N (p : ℝ) = (N : ℝ) * scale N p := by
    unfold Local.edgeScale
    have hsq : scale N p ^ 2 = (p : ℝ) * N := Real.sq_sqrt (by positivity)
    apply (div_eq_iff hS.ne').mpr
    change (N : ℝ) ^ 2 * (p : ℝ) = (N : ℝ) * scale N p * scale N p
    nlinarith
  rw [hscl]
  have := mul_le_mul_of_nonneg_right hvl (mul_nonneg hζ.le hS.le)
  nlinarith

end MajorityDynamics.Idealized.PerturbedEvolution
