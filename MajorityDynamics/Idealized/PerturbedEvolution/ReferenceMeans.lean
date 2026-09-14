import MajorityDynamics.Idealized.LinearResponse.Bridge
import MajorityDynamics.Idealized.LinearResponse.Reference
import MajorityDynamics.Idealized.LinearResponse.Geometry
import MajorityDynamics.Idealized.Process.EvolutionRows

/-! Uniform domains for the actual reference child means. -/
noncomputable section
open Filter Topology
namespace MajorityDynamics.Idealized.PerturbedEvolution
open Universal LinearResponse RowLimits
open Binomial.Approximation (Density scale)

set_option maxHeartbeats 800000 in
theorem reference_child_mean_bounds (θ T : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (n ell : ℕ) (hell : 1 ≤ ell)
    (hk : (n : ℝ) + 1 < 1 / (1 - θ)) :
    ∃ K : ℝ, 1 ≤ K ∧ ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      ∀ p : Binomial.Probability, Density θ T N p →
      ∀ a : Process.Data, Process.Specification N p (responseHorizon θ) ell a →
      ∀ s b t,
        |LinearResponse.childMean (a.state n).sizes s b (a.tilt n s) t -
          (p : ℝ) * ((a.state n).sizes t : ℝ)| ≤ K * Real.sqrt ((p : ℝ) * N) ∧
        c * ((p : ℝ) * N) ≤ LinearResponse.childMean (a.state n).sizes s b (a.tilt n s) t ∧
        LinearResponse.childMean (a.state n).sizes s b (a.tilt n s) t ≤ K * ((p : ℝ) * N) := by
  classical
  obtain ⟨L, R, hR, hγ, C, hC, Nr, hNr, href⟩ :=
    reference_row_data θ T hθlo hθhi hT n ell hell
  obtain ⟨A, hA, hrows⟩ := Process.row_asymptotics_of_estimates n R hR.le
  obtain ⟨G, hG, hg⟩ := finite_abs_bound
    (fun z : History (n + 1) × Bool × History (n + 1) =>
      branchMean z.1 (ν n) (γ n z.1) z.2.1 z.2.2)
  obtain ⟨v, hv, hvle⟩ := finite_common_positive (ν n) (ν_positive n)
  obtain ⟨B, hB, hνB⟩ := finite_abs_bound (ν n)
  let M := C + A * C + G + 1
  have hM : 0 < M := by dsimp [M]; positivity
  let K := 1 + M + 2 * B
  have hK : 1 ≤ K := by dsimp [K]; linarith
  have hMK : M ≤ K := by dsimp [K]; linarith
  refine ⟨K, hK, v / 4, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop Nr,
    eventually_basic θ T hθlo hθhi hT,
    eventually_small θ T hθlo hθhi hT n L hk,
    eventually_small θ T hθlo hθhi hT n 0 hk,
    eventually_rpow_neg_le (responseRate θ n) 1
      (responseRate_pos hθlo hθhi hk) zero_lt_one,
    eventually_rpow_neg_le (responseRate θ n) (v / (4 * M))
      (responseRate_pos hθlo hθhi hk) (by positivity),
    eventually_geometry θ T hθlo hθhi hT n ell 0 le_rfl hk]
      with N hNr hbasic hsmall hsmall0 hr1 hrv hgeo
  intro p hp a ha
  have hp0 : 0 < (p : ℝ) := p.property.1
  have hN : 0 < N := hbasic.1
  have hNreal : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hS : 0 < Real.sqrt ((p : ℝ) * N) := Real.sqrt_pos.mpr (by positivity)
  have hS1 : 1 ≤ Real.sqrt ((p : ℝ) * N) := (hbasic.2.2 p hp).1
  have hSq : Real.sqrt ((p : ℝ) * N) ^ 2 = (p : ℝ) * N :=
    Real.sq_sqrt (by positivity)
  have hρ0 : 0 ≤ Real.log (N : ℝ) ^ L / scale N p := by
    exact div_nonneg (pow_nonneg (show 0 ≤ Real.log (N : ℝ) by linarith [hbasic.2.1]) _) hS.le
  have hρ1 : Real.log (N : ℝ) ^ L / scale N p ≤ 1 :=
    (hsmall p hp).2.2.1.trans hr1
  choose σ hσR hσγ hσeq hσest using
    href N hNr p hp a (responseHorizon θ) ha (level_succ_lt_horizon hk)
  have htilt : (fun s => rowTilt N p (σ s)) = a.tilt n := funext hσeq
  have hrow := hrows N p (a.state n).sizes σ C C
    (Real.log (N : ℝ) ^ L / scale N p) hC.le hρ0 hσR hγ hσγ hσest
  rw [htilt] at hrow
  have hf := (hgeo p hp).2 a (responseHorizon θ) ha (level_succ_lt_horizon hk)
    (a.state n).sizes (fun t => by
      rw [sub_self, abs_zero]
      exact mul_nonneg (by linarith) (sizeScale_nonneg _ _ _))
  have hinv : 1 / Real.sqrt ((p : ℝ) * N) ≤ v / (4 * M) := by
    simpa using (hsmall0 p hp).2.2.1.trans hrv
  have hmS : M * Real.sqrt ((p : ℝ) * N) ≤ (v / 4) * ((p : ℝ) * N) := by
    have hx := (div_le_iff₀ hS).mp hinv
    have hy := mul_le_mul_of_nonneg_left hx hM.le
    have hz : M * (v / (4 * M) * Real.sqrt ((p : ℝ) * N)) =
        (v / 4) * Real.sqrt ((p : ℝ) * N) := by field_simp
    rw [hz] at hy
    have hh := mul_le_mul_of_nonneg_right hy hS.le
    nlinarith [hSq]
  intro s b t
  have hm := hrow.child_mean s b t
  have hmain : |(LinearResponse.childMean (a.state n).sizes s b (a.tilt n s) t -
      (p : ℝ) * ((a.state n).sizes t : ℝ)) / Real.sqrt ((p : ℝ) * N)| ≤ M := by
    have htri := abs_add_le
      ((Process.childMean (a.state n).sizes (a.tilt n) s b t - (p : ℝ) * ((a.state n).sizes t : ℝ)) /
        Real.sqrt ((p : ℝ) * N) - branchMean s (ν n) (γ n s) b t)
      (branchMean s (ν n) (γ n s) b t)
    have hc := mul_le_mul_of_nonneg_left hρ1
      (show 0 ≤ C + A * C by positivity)
    have hg' := hg (s,b,t)
    simp only [sub_add_cancel] at htri
    change |(LinearResponse.childMean (a.state n).sizes s b (a.tilt n s) t -
      (p : ℝ) * ((a.state n).sizes t : ℝ)) / Real.sqrt ((p : ℝ) * N)| ≤ _ at htri
    dsimp at hg'
    dsimp [M]
    linarith
  have habs : |LinearResponse.childMean (a.state n).sizes s b (a.tilt n s) t -
      (p : ℝ) * ((a.state n).sizes t : ℝ)| ≤ M * Real.sqrt ((p : ℝ) * N) := by
    rw [abs_div, abs_of_pos hS] at hmain
    exact (div_le_iff₀ hS).mp hmain
  refine ⟨habs.trans (mul_le_mul_of_nonneg_right hMK hS.le), ?_, ?_⟩
  · have hl := mul_lt_mul_of_pos_left (hf.ref_lower t) p.property.1
    have hv' := mul_le_mul_of_nonneg_left (hvle t) (show 0 ≤ (p : ℝ) * N by positivity)
    have he := (abs_le.mp habs).1
    nlinarith
  · have hu := mul_lt_mul_of_pos_left (hf.ref_upper t) p.property.1
    have hb := (le_abs_self (ν n t)).trans (hνB t)
    have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * (p : ℝ) * N by positivity)
    have he := (abs_le.mp habs).2
    have hsle : Real.sqrt ((p : ℝ) * N) ≤ (p : ℝ) * N := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hsle hM.le
    dsimp [K]
    nlinarith

end MajorityDynamics.Idealized.PerturbedEvolution
