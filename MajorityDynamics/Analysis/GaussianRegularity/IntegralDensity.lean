import MajorityDynamics.Analysis.GaussianRegularity.Integral
import MajorityDynamics.Analysis.GaussianRegularity.Density

/-!
# Uniform envelopes for diagonal Gaussian densities

Scalar density and score estimates give a common Gaussian envelope on bounded
mean and positive variance boxes. A finite-product difference estimate transfers
this bound to the joint density, with the product parameter distance. These
pointwise estimates are independent of the conditioning region.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal
namespace MajorityDynamics.Analysis.GaussianRegularity

/-- The explicit scalar score envelope has a pure Gaussian majorant. -/
theorem envelope_gaussian_bound {M a b : ℝ} (hM : 0 ≤ M) (ha : 0 < a) (hb : 0 < b) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ x, envelope M a b x ≤ C * Real.exp (-c * x ^ 2) := by
  let A := (1 + (1 + M) / a + ((1 + M ^ 2) / a ^ 2 + 1 / (2 * a))) *
    ((Real.sqrt (2 * Real.pi * a))⁻¹ * Real.exp (M ^ 2 / (2 * a)))
  let c := 1 / (4 * b)
  have hA : 0 < A := by dsimp [A]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨A * (1 + 2 / c), c / 2, by positivity, by positivity, ?_⟩
  intro x
  calc
    envelope M a b x = A * ((1 + x ^ 2) * Real.exp (-c * x ^ 2)) := by
      dsimp [envelope, A, c]
      have he : -x ^ 2 / (4 * b) = -(1 / (4 * b)) * x ^ 2 := by ring
      rw [he]
      ring
    _ ≤ A * ((1 + 2 / c) * Real.exp (-(c / 2) * x ^ 2)) :=
      mul_le_mul_of_nonneg_left (quadratic_mul_gaussian_le hc x) hA.le
    _ = _ := by ring

/-- Bounds on each parameter coordinate give a common radial envelope for
both the product density and its parameter differences. -/
theorem density_uniform_envelopes {d : ℕ} {M a b : ℝ}
    (hM : 0 ≤ M) (ha : 0 < a) (hb : 0 < b) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    (∀ (m v x : ConditionalGaussian.Space d),
      (∀ i, |m i| ≤ M) → (∀ i, a ≤ v i) → (∀ i, v i ≤ b) →
      ‖density m v x‖ ≤ C * Real.exp (-c * ‖x‖ ^ 2)) ∧
    (∀ (m v m' v' x : ConditionalGaussian.Space d),
      (∀ i, |m i| ≤ M) → (∀ i, a ≤ v i) → (∀ i, v i ≤ b) →
      (∀ i, |m' i| ≤ M) → (∀ i, a ≤ v' i) → (∀ i, v' i ≤ b) →
      ‖density m v x - density m' v' x‖ ≤
        (2 * d * C * Real.exp (-c * ‖x‖ ^ 2)) * ‖(m,v) - (m',v')‖) := by
  obtain ⟨C, c, hC, hc, he⟩ := envelope_gaussian_bound hM ha hb
  refine ⟨C ^ d, c, by positivity, hc, ?_, ?_⟩
  · intro m v x hm hv hvb
    unfold density
    rw [norm_prod]
    calc
      _ ≤ ∏ i : Fin d, C * Real.exp (-c * (x i) ^ 2) := by
        apply Finset.prod_le_prod (fun i _ => norm_nonneg _)
        intro i _
        exact (scalarDensity_le_common_envelope ha (hv i) (hvb i) (hm i)).trans (he (x i))
      _ = _ := prod_gaussian_envelope C c x
  · intro m v m' v' x hm hv hvb hm' hv' hvb'
    have hn (i : Fin d) : |m i - m' i| + |v i - v' i| ≤ 2 * ‖(m,v) - (m',v')‖ := by
      have h1 := PiLp.norm_apply_le (m - m') i
      have h2 := PiLp.norm_apply_le (v - v') i
      have h3 : ‖m - m'‖ ≤ ‖(m,v) - (m',v')‖ := norm_fst_le (m - m', v - v')
      have h4 : ‖v - v'‖ ≤ ‖(m,v) - (m',v')‖ := norm_snd_le (m - m', v - v')
      change |m i - m' i| ≤ ‖m - m'‖ at h1
      change |v i - v' i| ≤ ‖v - v'‖ at h2
      linarith
    have hp := norm_prod_sub_prod_le_envelope Finset.univ
      (fun i => scalarDensity (m i) (v i) (x i))
      (fun i => scalarDensity (m' i) (v' i) (x i))
      (fun i => C * Real.exp (-c * (x i) ^ 2))
      (δ := 2 * ‖(m,v) - (m',v')‖) (by positivity)
      (fun i _ => by positivity)
      (fun i _ => (scalarDensity_le_common_envelope ha (hv i) (hvb i) (hm i)).trans (he (x i)))
      (fun i _ => (scalarDensity_le_common_envelope ha (hv' i) (hvb' i) (hm' i)).trans (he (x i)))
      (fun i _ => (scalarDensity_sub_le_envelope ha (hv i) (hvb i) (hv' i) (hvb' i) (hm i) (hm' i)).trans
        (mul_le_mul (he (x i)) (hn i) (by positivity) (by positivity)))
    simp only [Finset.card_fin, prod_gaussian_envelope] at hp
    change ‖density m v x - density m' v' x‖ ≤ _ at hp
    calc
      _ ≤ _ := hp
      _ = _ := by ring

end MajorityDynamics.Analysis.GaussianRegularity
