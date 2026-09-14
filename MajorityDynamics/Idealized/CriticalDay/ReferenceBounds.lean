import MajorityDynamics.Idealized.CriticalDay.Scaling
import MajorityDynamics.Idealized.PerturbedTilt.ReferenceBounds
noncomputable section
open Filter Topology
open scoped BigOperators
namespace MajorityDynamics.Idealized.CriticalDay
open Universal LinearResponse PerturbedTilt
open Binomial.Approximation (Density scale)

theorem first_day_subcritical {θ : ℝ} (hθlo : 1 / 2 < θ) (hθhi : θ < 1) : ((0 : ℕ) : ℝ) + 1 < 1 / (1 - θ) := by
  apply (lt_div_iff₀ (sub_pos.mpr hθhi)).mpr
  norm_num at *
  linarith

theorem reference_coordinates (θ T : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (n ell : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ p : Binomial.Probability, Density θ T N p →
      ∀ x : Process.State n, Process.LevelEstimates N p ell x →
      (∀ s, |(x.sizes s : ℝ) / N - ν n s| ≤ K * (N : ℝ) ^ (-responseRate θ 0)) ∧
      (∀ s t, |x.edges s t / ((p : ℝ) * (N : ℝ) ^ 2) - ν n s * ν n t| ≤
        K * (N : ℝ) ^ (-responseRate θ 0)) := by
  classical
  let C := fun s t => 4 * ν n s * ν n t * (1 + |μ n s t|) + 2 * ν n s + ν n t
  let K := 1 + ∑ s, ∑ t, |C s t|
  have hK : 1 ≤ K := by
    have : 0 ≤ ∑ s, ∑ t, |C s t| := by positivity
    dsimp [K]
    linarith
  have hCK : ∀ s t, C s t ≤ K := by
    intro s t
    have h1 := Finset.single_le_sum (fun t _ => abs_nonneg (C s t)) (Finset.mem_univ t)
    have h2 := Finset.single_le_sum (fun s _ => show 0 ≤ ∑ t, |C s t| by positivity) (Finset.mem_univ s)
    dsimp [K]
    linarith [le_abs_self (C s t)]
  refine ⟨K, hK, ?_⟩
  filter_upwards [eventually_basic θ T hθlo hθhi hT,
    eventually_small θ T hθlo hθhi hT 0 ell (first_day_subcritical hθlo hθhi),
    Process.eventually_level_sizes (n := n) θ T ell hθhi (by linarith)] with N hbasic hsmall hlev
  intro p hp x hx
  have hp0 := p.property.1
  have hN := hbasic.1
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hS1 := (hbasic.2.2 p hp).1
  have hS1' : 1 ≤ scale N p := hS1
  have hS : 0 < scale N p := lt_of_lt_of_le zero_lt_one hS1
  have hlog : 1 ≤ Real.log (N : ℝ) ^ ell := one_le_pow₀ (by linarith [hbasic.2.1])
  have herr := (hsmall p hp).2.2.1
  have hsize := hlev.2 p hp x hx
  have hR : 0 ≤ Real.log (N : ℝ) ^ ell / scale N p := by positivity
  refine ⟨fun s => (hx.relative_sizes hN s).trans (herr.trans (by nlinarith [Real.rpow_nonneg (Nat.cast_nonneg N) (-responseRate θ 0)])), ?_⟩
  intro s t
  have hνs := ν_positive n s
  have hνt := ν_positive n t
  have hs0 : 0 ≤ (x.sizes s : ℝ) / N := by positivity
  have ht0 : 0 ≤ (x.sizes t : ℝ) / N := by positivity
  have hsU : (x.sizes s : ℝ) / N ≤ 2 * ν n s := by
    apply (div_le_iff₀ hNr).mpr
    nlinarith [(hsize s).2.2]
  have htU : (x.sizes t : ℝ) / N ≤ 2 * ν n t := by
    apply (div_le_iff₀ hNr).mpr
    nlinarith [(hsize t).2.2]
  have hnorm : |x.edges s t / ((p : ℝ) * (N : ℝ) ^ 2) -
      ((x.sizes s : ℝ) / N) * ((x.sizes t : ℝ) / N) * (1 + μ n s t / scale N p)| ≤
      ((x.sizes s : ℝ) / N) * ((x.sizes t : ℝ) / N) *
        (Real.log (N : ℝ) ^ ell / scale N p) := by
    have hid : x.edges s t / ((p : ℝ) * (N : ℝ) ^ 2) -
        ((x.sizes s : ℝ) / N) * ((x.sizes t : ℝ) / N) * (1 + μ n s t / scale N p) =
        (x.edges s t - (p : ℝ) * x.sizes s * x.sizes t * (1 + μ n s t / scale N p)) /
          ((p : ℝ) * (N : ℝ) ^ 2) := by field_simp
    rw [hid, abs_div, abs_of_pos (by positivity : 0 < (p : ℝ) * (N : ℝ) ^ 2)]
    have hsq : scale N p ^ 2 = (p : ℝ) * N := Real.sq_sqrt (by positivity)
    have hL : Real.log (N : ℝ) ^ ell / ((p : ℝ) * N) ≤ Real.log (N : ℝ) ^ ell / scale N p := by
      apply div_le_div_of_nonneg_left (by positivity) hS
      nlinarith
    have hdiv := div_le_div_of_nonneg_right (hx.edges s t)
      (show 0 ≤ (p : ℝ) * (N : ℝ) ^ 2 by positivity)
    have heq : ((p : ℝ) * x.sizes s * x.sizes t * (Real.log (N : ℝ) ^ ell / ((p : ℝ) * N))) /
        ((p : ℝ) * (N : ℝ) ^ 2) =
        ((x.sizes s : ℝ) / N) * ((x.sizes t : ℝ) / N) * (Real.log (N : ℝ) ^ ell / ((p : ℝ) * N)) := by
      field_simp
    rw [heq] at hdiv
    exact hdiv.trans (mul_le_mul_of_nonneg_left hL (mul_nonneg hs0 ht0))
  have hb := normalized_edge_scalar hs0 ht0 (ν_positive n s).le (ν_positive n t).le hsU htU hS hR
    (div_le_div_of_nonneg_right hlog hS.le) (hx.relative_sizes hN s) (hx.relative_sizes hN t) hnorm
  have hC0 : 0 ≤ C s t := by dsimp [C]; positivity
  exact hb.trans ((mul_le_mul_of_nonneg_left herr hC0).trans
    (mul_le_mul_of_nonneg_right (hCK s t) (Real.rpow_nonneg (Nat.cast_nonneg N) _)))

end MajorityDynamics.Idealized.CriticalDay
