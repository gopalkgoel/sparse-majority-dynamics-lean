import MajorityDynamics.Literature.RandomGraph.JumblednessAnalysis

namespace MajorityDynamics.Literature.RandomGraph

lemma subsetEntropy_le {N w : ℝ} (hw : 0 < w) (hN : 0 < N) :
    subsetEntropy N w ≤ N := by
  have h := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hN hw)) hw.le
  have he : w * (N / w - 1) = N - w := by field_simp
  rw [he] at h
  dsimp [subsetEntropy]
  linarith

lemma gaussian_sqrt_ge_entropy {N d u w μ K : ℝ}
    (hu : 0 < u) (hw : 0 < w) (hd : 0 < d) (hN : 0 < N)
    (hμ : 0 < μ) (hμbound : μ ≤ d * u * w / N) (hK : 4 ≤ K) :
    8 * subsetEntropy N w ≤ (K * Real.sqrt (d * u * w)) ^ 2 / (2 * μ) := by
  have hs : Real.sqrt (d * u * w) ^ 2 = d * u * w := Real.sq_sqrt (by positivity)
  have hb := (le_div_iff₀ hN).mp hμbound
  have he := subsetEntropy_le hw hN
  apply (le_div_iff₀ (show 0 < 2 * μ by positivity)).mpr
  rw [mul_pow, hs]
  have hc : 16 ≤ K ^ 2 := by nlinarith
  have hp : 0 ≤ d * u * w := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hc hp,
    mul_le_mul_of_nonneg_right he hμ.le]

/-- The binomial Bennett exponent at the discrepancy scale dominates the
entropy of choosing the larger set, uniformly in the balanced size range. -/
lemma bennett_sqrt_ge_entropy {N d u w μ K : ℝ}
    (hu : 0 < u) (hw : 0 < w) (hd : 0 < d) (hwN : w ≤ N)
    (hbalanced : w ≤ d * u) (hμ : 0 < μ) (hμbound : μ ≤ d * u * w / N)
    (hK : 1 ≤ K) :
    K / 6 * subsetEntropy N w ≤
      μ * ((1 + K * Real.sqrt (d * u * w) / μ) *
        Real.log (1 + K * Real.sqrt (d * u * w) / μ) -
          K * Real.sqrt (d * u * w) / μ) := by
  let s := Real.sqrt (d * u * w)
  have hs : 0 < s := by dsimp [s]; positivity
  have hs2 : s ^ 2 = d * u * w := Real.sq_sqrt (by positivity)
  have hN : 0 < N := hw.trans_le hwN
  have hK0 : 0 < K := by linarith
  have hws : w ≤ s := by nlinarith [mul_le_mul_of_nonneg_right hbalanced hw.le]
  have hy : 1 ≤ s / w := (one_le_div hw).mpr hws
  have he := scaled_bennett_entropy hw hwN hy hK
  have hsw : s / w * w = s := by field_simp
  have hksw : K * (s / w) * w = K * s := by field_simp
  rw [hsw, hksw] at he
  have hb : μ * N ≤ s ^ 2 := by
    have := (le_div_iff₀ hN).mp hμbound
    nlinarith
  have hratio : K * N / s ≤ K * s / μ := by
    apply (div_le_div_iff₀ hs hμ).mpr
    nlinarith [mul_le_mul_of_nonneg_left hb hK0.le]
  have hl := Real.log_le_log (by positivity : 0 < 1 + K * N / s)
    (show 1 + K * N / s ≤ 1 + K * s / μ by linarith)
  have hscaled := mul_le_mul_of_nonneg_left hl (show 0 ≤ K * s by positivity)
  have hbennett := bennett_ge_half_mul_log (show 0 ≤ K * s / μ by positivity)
  have hmul := mul_le_mul_of_nonneg_left hbennett hμ.le
  have hid : μ * (K * s / μ / 2 * Real.log (1 + K * s / μ)) =
      K * s * Real.log (1 + K * s / μ) / 2 := by field_simp
  rw [hid] at hmul
  change K / 6 * subsetEntropy N w ≤
    μ * ((1 + K * s / μ) * Real.log (1 + K * s / μ) - K * s / μ)
  linarith

end MajorityDynamics.Literature.RandomGraph
