import MajorityDynamics.Idealized.CriticalDay.Geometry
import MajorityDynamics.Idealized.CriticalDay.ReferenceBounds
import MajorityDynamics.Idealized.PerturbedTilt.TargetAlgebra

/-! Uniform approximation of the actual faithful edge target by epsilon. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace MajorityDynamics.Idealized.CriticalDay
open Universal LinearResponse PerturbedTilt
open Binomial.Approximation (Density)

def targetRate (θ δ : ℝ) : ℝ := min (rate θ) δ / 2

theorem targetRate_bounds {θ δ : ℝ} (hκ : 0 < rate θ) (hδ : 0 < δ) :
    0 < targetRate θ δ ∧ targetRate θ δ < rate θ ∧ targetRate θ δ < δ := by
  have h := lt_min hκ hδ
  have h1 := min_le_left (rate θ) δ
  have h2 := min_le_right (rate θ) δ
  unfold targetRate
  constructor
  · positivity
  · constructor <;> linarith

theorem normalized_faithful_error {T τ c r z : ℝ} (hT : 0 < T) (hτ : T⁻¹ ≤ τ)
    (hc : 0 < c) (hr : 0 ≤ r) (hz : |z| ≤ T * c * r) :
    |z / (τ * c)| ≤ T ^ 2 * r := by
  have hτ0 : 0 < τ := (inv_pos.mpr hT).trans_le hτ
  have hTτ : 1 ≤ T * τ := by
    have := mul_le_mul_of_nonneg_left hτ hT.le
    simpa [hT.ne'] using this
  have hq : T / τ ≤ T ^ 2 := by
    apply (div_le_iff₀ hτ0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hTτ hT.le]
  rw [abs_div, abs_of_pos (mul_pos hτ0 hc)]
  calc
    _ ≤ (T * c * r) / (τ * c) := div_le_div_of_nonneg_right hz (by positivity)
    _ = (T / τ) * r := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hq hr

def edgeTarget {n : ℕ} (N : ℕ) (p : ℝ) (a : Process.Data) (τ : ℝ)
    (η : History (n + 1) → ℤ) (e : History (n + 1) → History (n + 1) → ℤ)
    (s : History (n + 1)) : Row (n + 1) := WithLp.toLp 2 (fun t =>
      ((e s t : ℝ) / (η s : ℝ) - (a.state n).edges s t / ((a.state n).sizes s : ℝ)) /
        (τ * betaScale N p n * (p * N)))

theorem faithful_target (θ T δ : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hδ : 0 < δ) (n ell : ℕ) (hk : (n : ℝ) + 1 = 1 / (1 - θ)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ p : Binomial.Probability, Density θ T N p →
      ∀ a : Process.Data, Process.Specification N p (responseHorizon θ) ell a →
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ η : History (n + 1) → ℤ, ∀ e : History (n + 1) → History (n + 1) → ℤ,
      FaithfulNumericalData N (p : ℝ) T δ τ a n η e →
      ∀ s t, |edgeTarget N (p : ℝ) a τ η e s t - ε n t| ≤ K * (N : ℝ) ^ (-targetRate θ δ) := by
  classical
  have hT0 : 0 < T := by linarith
  have hκ := rate_pos hθlo hθhi
  obtain ⟨hρ, hρκ, hρδ⟩ := targetRate_bounds hκ hδ
  have hsingle (z : History (n + 1) × History (n + 1)) :=
    target_scalar_control (ν_positive n z.1) (ν_positive n z.2) (ε n z.1) (ε n z.2)
  choose a ha K hK hctl using hsingle
  obtain ⟨a₀, ha₀, halower⟩ := RowLimits.finite_common_positive a ha
  let K₀ := 1 + ∑ z, |K z|
  have hK₀ : 0 < K₀ := by dsimp [K₀]; positivity
  have hKbound : ∀ z, K z ≤ K₀ := by
    intro z
    have := Finset.single_le_sum (fun z _ => abs_nonneg (K z)) (Finset.mem_univ z)
    dsimp [K₀]
    linarith [le_abs_self (K z)]
  obtain ⟨Kr, hKr, href⟩ := reference_coordinates θ T hθlo hθhi hT n ell
  refine ⟨K₀, hK₀, ?_⟩
  filter_upwards [href, faithful_geometry θ T δ hθlo hθhi hT hδ n ell hk,
    eventually_basic θ T hθlo hθhi hT,
    beta_small θ T hθlo hθhi hT n hk,
    eventually_poly_log_le Kr (responseRate θ 0) (targetRate θ δ) 0 (by linarith) (by unfold rate at hρκ; linarith),
    eventually_poly_log_le T (rate θ) (targetRate θ δ) 0 hT0.le hρκ,
    eventually_poly_log_le (T ^ 2) δ (targetRate θ δ) 0 (sq_nonneg _) hρδ,
    eventually_rpow_neg_le (targetRate θ δ) (a₀ / 2) hρ (half_pos ha₀)]
      with N href hgeo hbasic hsmall hr1 hr2 hr3 hr4
  simp only [pow_zero, mul_one] at hr1 hr2 hr3
  intro p hp b hb τ hτ hτT η e hf s t
  obtain ⟨hη, _, _, hrefposAll⟩ := hgeo p hp b hb τ hτ hτT η e hf
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr hbasic.1
  have hp0 := p.property.1
  have hτ0 : 0 < τ := (inv_pos.mpr hT0).trans_le hτ
  have hβ : 0 < betaScale N (p : ℝ) n := by unfold betaScale; positivity
  have hrefpos : (0 : ℝ) < (b.state n).sizes s := Nat.cast_pos.mpr (hrefposAll s)
  have hηpos : (0 : ℝ) < η s := by exact_mod_cast hη s
  have hc := href p hp (b.state n) (hb.estimates n (Nat.lt_of_succ_lt (critical_level_lt_horizon hk)))
  let S := sizeScale N (p : ℝ) n
  let B := betaScale N (p : ℝ) n
  have hscale : S = B * N := sizeScale_eq N hbasic.1 (p : ℝ) n
  have hnum : |((η s : ℝ) - ((b.state n).sizes s : ℝ)) / (τ * B * N) - ε n s| ≤
      T ^ 2 * (N : ℝ) ^ (-δ) := by
    have heq : ((η s : ℝ) - ((b.state n).sizes s : ℝ)) / (τ * B * N) - ε n s =
        ((η s : ℝ) - ((b.state n).sizes s : ℝ) - τ * S * ε n s) / (τ * S) := by
      rw [hscale]
      field_simp [show B ≠ 0 from hβ.ne']
    rw [heq]
    apply normalized_faithful_error hT0 hτ (show 0 < S by dsimp [S, sizeScale]; positivity)
      (Real.rpow_nonneg (Nat.cast_nonneg N) _) (hf.sizes s)
  have hedge : |((e s t : ℝ) - (b.state n).edges s t *
      (1 + τ * B * (ε n s / ν n s + ε n t / ν n t))) / (τ * B * (p : ℝ) * (N : ℝ) ^ 2)| ≤
      T ^ 2 * (N : ℝ) ^ (-δ) := by
    have heq : τ * B * (p : ℝ) * (N : ℝ) ^ 2 = τ * (B * (N : ℝ) ^ 2 * (p : ℝ)) := by ring
    rw [heq]
    apply normalized_faithful_error hT0 hτ (by dsimp [B]; positivity)
      (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    convert hf.edges s t using 1
    ring
  have hβsmall : B ≤ (N : ℝ) ^ (-rate θ) := hsmall p hp
  let x : Fin 5 → ℝ := ![((b.state n).sizes s : ℝ) / N,
    (b.state n).edges s t / ((p : ℝ) * (N : ℝ) ^ 2), τ * B,
    ((η s : ℝ) - ((b.state n).sizes s : ℝ)) / (τ * B * N) - ε n s,
    ((e s t : ℝ) - (b.state n).edges s t * (1 + τ * B * (ε n s / ν n s + ε n t / ν n t))) /
      (τ * B * (p : ℝ) * (N : ℝ) ^ 2)]
  have hx : ∀ i, |x i - targetPoint (ν n s) (ν n t) i| ≤ (N : ℝ) ^ (-targetRate θ δ) := by
    intro i
    fin_cases i
    · exact (hc.1 s).trans hr1
    · exact (hc.2 s t).trans hr1
    · change |τ * B - 0| ≤ _
      rw [sub_zero, abs_of_pos (mul_pos hτ0 hβ)]
      exact (mul_le_mul hτT hβsmall hβ.le hT0.le).trans hr2
    · simpa [x, targetPoint] using hnum.trans hr3
    · simpa [x, targetPoint] using hedge.trans hr3
  have hc' := hctl (s,t) ((N : ℝ) ^ (-targetRate θ δ))
    (Real.rpow_nonneg (Nat.cast_nonneg N) _) (hr4.trans_lt ((half_lt_self ha₀).trans_le (halower (s,t)))) x hx
  have heq : targetFunction (ν n s) (ν n t) (ε n s) (ε n t) x = edgeTarget N (p : ℝ) b τ η e s t := by
    exact target_rescale hN.ne' hp0.ne' (mul_pos hτ0 hβ).ne' hrefpos.ne' hηpos.ne' _ _ _ _
  rw [heq] at hc'
  exact hc'.trans (mul_le_mul_of_nonneg_right (hKbound (s,t)) (Real.rpow_nonneg (Nat.cast_nonneg N) _))

end MajorityDynamics.Idealized.CriticalDay
