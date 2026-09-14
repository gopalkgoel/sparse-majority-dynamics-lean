import MajorityDynamics.Idealized.CriticalDay.ReferenceBounds

noncomputable section
open scoped BigOperators
namespace MajorityDynamics.Idealized.CriticalDay
open Universal LinearResponse PerturbedTilt
open Binomial.Approximation (scale)

/-- Keep the sharp logarithmic-over-square-root-degree error instead of
weakening it to a fixed power of N before the terminal comparison. -/
theorem reference_coordinates_log_budget (n ell : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ N : ℕ, 0 < N → 1 ≤ Real.log (N:ℝ) →
      ∀ p : Binomial.Probability, 1 ≤ scale N p →
      ∀ x : Process.State n, Process.LevelEstimates N p ell x →
      (∀ s, (x.sizes s:ℝ) ≤ 2*N*ν n s) →
      (∀ s, |(x.sizes s:ℝ)/N-ν n s| ≤ K*(Real.log N^ell/scale N p)) ∧
      (∀ s t, |x.edges s t/((p:ℝ)*(N:ℝ)^2)-ν n s*ν n t| ≤
        K*(Real.log N^ell/scale N p)) := by
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
  intro N hN hlog₀ p hS1 x hx hsize
  have hp0 := p.property.1
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hS1' : 1 ≤ scale N p := hS1
  have hS : 0 < scale N p := lt_of_lt_of_le zero_lt_one hS1
  have hlog : 1 ≤ Real.log (N : ℝ) ^ ell := one_le_pow₀ hlog₀
  have hR : 0 ≤ Real.log (N : ℝ) ^ ell / scale N p := by positivity
  refine ⟨fun s => (hx.relative_sizes hN s).trans (le_mul_of_one_le_left hR hK), ?_⟩
  intro s t
  have hνs := ν_positive n s
  have hνt := ν_positive n t
  have hs0 : 0 ≤ (x.sizes s : ℝ) / N := by positivity
  have ht0 : 0 ≤ (x.sizes t : ℝ) / N := by positivity
  have hsU : (x.sizes s : ℝ) / N ≤ 2 * ν n s := by
    apply (div_le_iff₀ hNr).mpr
    nlinarith [hsize s]
  have htU : (x.sizes t : ℝ) / N ≤ 2 * ν n t := by
    apply (div_le_iff₀ hNr).mpr
    nlinarith [hsize t]
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
  exact hb.trans (mul_le_mul_of_nonneg_right (hCK s t) hR)


end MajorityDynamics.Idealized.CriticalDay

