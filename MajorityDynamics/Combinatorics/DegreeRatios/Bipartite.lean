import MajorityDynamics.Combinatorics.DegreeRatios.Bridges

noncomputable section

namespace MajorityDynamics.Combinatorics.DegreeRatios

theorem bipartite_estimate_of_large {T p : ℝ} {n : ℕ} {ell m d : ℤ}
    (hT : 1 < T) (hlarge : LargeParameters T n p)
    (hw : BipartiteWindow T n p ell m d) : BipartiteEstimate (errorConstant T) n p ell m d := by
  have hT0 : 0 < T := by linarith
  have hn0 : (0 : ℝ) < n := by linarith [hlarge.1]
  have hnr : 64 * T ≤ (n : ℝ) := hlarge.1
  have hell : (n : ℝ) ≤ T * ell := by
    have hh := mul_le_mul_of_nonneg_left hw.1 hT0.le
    have hid : T * (T⁻¹ * (n : ℝ)) = n := by field_simp
    rwa [hid] at hh
  have hell1r : (1 : ℝ) ≤ ell := by
    by_contra hc
    have hh := mul_lt_mul_of_pos_left (lt_of_not_ge hc) hT0
    nlinarith
  have hell1 : (1 : ℤ) ≤ ell := by exact_mod_cast hell1r
  have hell0 : 0 ≤ ell := by omega
  let N := (ell * (n : ℤ)).toNat
  have hNc : (N : ℝ) = (ell : ℝ) * n := by
    dsimp [N]
    rw [int_toNat_cast (by positivity)]
    push_cast
    rfl
  have hcap : (n : ℝ) ^ 2 ≤ 4 * T * (N : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hell hn0.le
    rw [hNc]
    have hh0 : 0 ≤ T * (ell : ℝ) * n := by positivity
    nlinarith
  have hmw : |(m : ℝ) - p * (N : ℝ)| ≤ T * (n : ℝ) ^ 2 * p / Real.sqrt (p * n) := by
    simpa only [hNc, mul_assoc] using hw.2.2.1
  have br := window_bounds hT hlarge hcap (by linarith : (n : ℝ) - 1 ≤ n)
    le_rfl hmw hw.2.2.2
  have hm0 : (0 : ℤ) ≤ m := by exact_mod_cast br.count_pos.le
  have hd0 : (0 : ℤ) ≤ d := by exact_mod_cast br.degree_nonneg
  have hmc := int_toNat_cast hm0
  have hdc := int_toNat_cast hd0
  have b : RemovalBounds T n p N m.toNat n d.toNat := by
    simpa only [hmc, hdc] using br
  have nd := natural_domain b
  have hsub : (m - d).toNat = m.toNat - d.toNat := Int.toNat_sub'' hm0 hd0
  have hres : ((ell - 1) * (n : ℤ)).toNat = N - n := by
    dsimp [N]
    rw [sub_mul, one_mul, Int.toNat_sub']
  have hratio : bipartiteRatio n ell m d = removalRatio N m.toNat n d.toNat := by
    simp only [bipartiteRatio, removalRatio, hres, hsub, N]
  have hdm : d ≤ m := by
    have hh : (d : ℝ) ≤ m := by simpa only [hmc, hdc] using (show (d.toNat : ℝ) ≤ m.toNat by exact_mod_cast nd.degree_count_le)
    exact_mod_cast hh
  have hmN : m ≤ ell * n := by
    have hh : (m : ℝ) ≤ (ell : ℝ) * n := by
      simpa only [hmc, hNc] using (show (m.toNat : ℝ) ≤ N by exact_mod_cast nd.count_le)
    exact_mod_cast hh
  have hrN : m - d ≤ (ell - 1) * n := by
    have hres0 : (0 : ℤ) ≤ (ell - 1) * n := by positivity
    have hmrest0 : 0 ≤ m - d := sub_nonneg.mpr hdm
    have hh : ((m - d).toNat : ℤ) ≤ ((ell - 1) * (n : ℤ)).toNat := by
      exact_mod_cast (show (m - d).toNat ≤ ((ell - 1) * (n : ℤ)).toNat by
        simpa only [hsub, hres] using nd.residual_le)
    simpa only [Int.toNat_of_nonneg hmrest0, Int.toNat_of_nonneg hres0] using hh
  refine ⟨⟨hell1, hd0, hdm, hm0, hmN, hrN, ?_, ?_⟩, ?_, ?_⟩
  · exact_mod_cast Nat.choose_pos nd.count_le
  · rw [hres, hsub]
    exact_mod_cast Nat.choose_pos nd.residual_le
  · rw [hratio]
    exact nd.ratio_pos
  · rw [hratio]
    have he := removal_estimate hT0.le hlarge.2.1 b
    simpa only [hdc] using he

end MajorityDynamics.Combinatorics.DegreeRatios
