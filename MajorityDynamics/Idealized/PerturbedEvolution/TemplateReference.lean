import MajorityDynamics.Idealized.PerturbedEvolution.TemplateRates
import MajorityDynamics.Idealized.Process.EvolutionAlgebra

noncomputable section
open Filter Topology
namespace MajorityDynamics.Idealized.PerturbedEvolution
open Universal LinearResponse PerturbedTilt
open Binomial.Approximation (Density scale)

set_option maxHeartbeats 800000 in
theorem reference_template_geometry (θ T δ : ℝ) (hθlo : 1 / 2 < θ)
    (hθhi : θ < 1) (hT : 1 < T) (hδ : 0 < δ) (n ell : ℕ)
    (hk : (n : ℝ) + 1 < 1 / (1 - θ)) :
    ∃ W : ℝ, 0 < W ∧ ∀ᶠ N : ℕ in atTop,
      ∀ p : Binomial.Probability, Density θ T N p →
      ∀ a : Process.Data, Process.Specification N p (responseHorizon θ) ell a →
      (∀ u, (N : ℝ) * ν (n + 1) u / 2 ≤
          Local.templateSizes (a.state n).sizes (a.tilt n) u ∧
        |Local.templateSizes (a.state n).sizes (a.tilt n) u - N * ν (n + 1) u| ≤
          2 * N * (N : ℝ) ^ (-tiltRate θ δ n)) ∧
      ∀ u v, |(a.state (n + 1)).edges u v| ≤ W * p * (N : ℝ) ^ 2 := by
  classical
  obtain ⟨B, hB, hν⟩ := finite_abs_bound (ν (n + 1))
  obtain ⟨M, hM, hμ⟩ := finite_abs_bound
    (fun z : History (n + 2) × History (n + 2) => μ (n + 1) z.1 z.2)
  refine ⟨4 * B ^ 2 * (2 + M) + 1, by positivity, ?_⟩
  filter_upwards [(eventually_template_rates θ T δ hθlo hθhi hT hδ n ell hk).2,
    eventually_basic θ T hθlo hθhi hT,
    Process.eventually_level_sizes (n := n + 1) θ T ell hθhi (by linarith)]
    with N hr hb hs
  intro p hp a ha
  have hp0 := p.property.1
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr hb.1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hb.1
  have hS1 : 1 ≤ scale N p := (hb.2.2 p hp).1
  have hS : 0 < scale N p := zero_lt_one.trans_le hS1
  have hsq : scale N p ^ 2 = (p : ℝ) * N := Real.sq_sqrt (by positivity)
  have hn := level_succ_lt_horizon hk
  have hx := ha.estimates (n + 1) hn
  have hsize := hs.2 p hp (a.state (n + 1)) hx
  have rates := hr p hp
  have hlog : 0 ≤ Real.log (N : ℝ) ^ ell := by
    exact pow_nonneg (by linarith [hb.2.1]) _
  have hlogS : Real.log (N : ℝ) ^ ell / scale N p ≤ 1 := rates.2.2.2.1.trans rates.1
  have hlogSq : Real.log (N : ℝ) ^ ell / ((p : ℝ) * N) ≤ 1 := by
    rw [← hsq]
    apply le_trans (div_le_div_of_nonneg_left hlog hS (by nlinarith)) hlogS
  constructor
  · intro u
    have hf : ((a.state (n + 1)).sizes u : ℝ) ≤
        Local.templateSizes (a.state n).sizes (a.tilt n) u := by
      rw [ha.evolution n hn]
      exact Nat.floor_le (Process.templateSizes_nonneg _ _ _)
    have hfu : Local.templateSizes (a.state n).sizes (a.tilt n) u <
        ((a.state (n + 1)).sizes u : ℝ) + 1 := by
      rw [ha.evolution n hn]
      exact Nat.lt_floor_add_one _
    refine ⟨(hsize u).2.1.le.trans hf, ?_⟩
    have herr : |((a.state (n + 1)).sizes u : ℝ) - N * ν (n + 1) u| ≤
        N * (N : ℝ) ^ (-tiltRate θ δ n) := by
      apply (hx.sizes u).trans
      have := mul_le_mul_of_nonneg_left rates.2.2.2.1 hN.le
      dsimp [scale] at this
      convert this using 1; ring
    have hdhalf : tiltRate θ δ n ≤ 1 := by
      have hd := (tiltRate_bounds (responseRate_pos hθlo hθhi hk) hδ).2.1
      have := responseRate_le_complement (θ := θ) (n := n)
      linarith
    have hlarge : 1 ≤ (N : ℝ) * (N : ℝ) ^ (-tiltRate θ δ n) := by
      conv_rhs => lhs; rw [← Real.rpow_one (N : ℝ)]
      rw [← Real.rpow_add hN]
      exact Real.one_le_rpow hN1 (by linarith)
    have hferr : |Local.templateSizes (a.state n).sizes (a.tilt n) u -
        ((a.state (n + 1)).sizes u : ℝ)| ≤ 1 := by rw [abs_of_nonneg (sub_nonneg.mpr hf)]; linarith
    have := (abs_sub_le (Local.templateSizes (a.state n).sizes (a.tilt n) u)
      ((a.state (n + 1)).sizes u : ℝ) (N * ν (n + 1) u)).trans (add_le_add hferr herr)
    linarith
  · intro u v
    let P : ℝ := (p : ℝ) * (a.state (n + 1)).sizes u * (a.state (n + 1)).sizes v
    have hP : 0 ≤ P := by dsimp [P]; positivity
    have hPu : ((a.state (n + 1)).sizes u : ℝ) ≤ 2 * N * B := by
      have := (hsize u).2.2.le
      have hv := (le_abs_self _).trans (hν u)
      nlinarith
    have hPv : ((a.state (n + 1)).sizes v : ℝ) ≤ 2 * N * B := by
      have := (hsize v).2.2.le
      have hv := (le_abs_self _).trans (hν v)
      nlinarith
    have hPU : P ≤ 4 * B ^ 2 * p * (N : ℝ) ^ 2 := by
      have hh := mul_le_mul hPu hPv (Nat.cast_nonneg _) (by positivity)
      have hh' := mul_le_mul_of_nonneg_left hh p.property.1.le
      dsimp [P]
      nlinarith only [hh']
    have hm : |μ (n + 1) u v / scale N p| ≤ M := by
      rw [abs_div, abs_of_pos hS]
      exact (div_le_self (abs_nonneg _) hS1).trans (hμ (u,v))
    have hc : |1 + μ (n + 1) u v / scale N p| ≤ 1 + M := by
      simpa using (abs_add_le 1 (μ (n + 1) u v / scale N p)).trans (by linarith)
    have he := hx.edges u v
    have he' : |(a.state (n + 1)).edges u v - P * (1 + μ (n + 1) u v / scale N p)| ≤ P :=
      he.trans (mul_le_of_le_one_right hP hlogSq)
    have hc' : |P * (1 + μ (n + 1) u v / scale N p)| ≤ P * (1 + M) := by
      rw [abs_mul, abs_of_nonneg hP]
      exact mul_le_mul_of_nonneg_left hc hP
    have hh := abs_sub_le ((a.state (n + 1)).edges u v)
      (P * (1 + μ (n + 1) u v / scale N p)) 0
    simp only [sub_zero] at hh
    have heU : |(a.state (n + 1)).edges u v| ≤ P * (2 + M) := by
      exact hh.trans (by nlinarith only [he', hc'])
    apply heU.trans
    have hpN0 : 0 ≤ (p : ℝ) * (N : ℝ) ^ 2 := mul_nonneg hp0.le (sq_nonneg _)
    have hprod := mul_le_mul_of_nonneg_right hPU (show 0 ≤ 2 + M by linarith)
    nlinarith only [hprod, hpN0]

end MajorityDynamics.Idealized.PerturbedEvolution
