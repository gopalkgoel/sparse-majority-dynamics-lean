import MajorityDynamics.Combinatorics.DegreeRatios.Bridges

noncomputable section

namespace MajorityDynamics.Combinatorics.DegreeRatios

theorem graph_estimate_of_large {T p : ℝ} {n : ℕ} {m d : ℤ}
    (hT : 1 < T) (hlarge : LargeParameters T n p)
    (hw : GraphWindow T n p m d) : GraphEstimate (errorConstant T) n p m d := by
  have hT0 : 0 < T := by linarith
  have hn64r : (64 : ℝ) ≤ n := by linarith [hlarge.1]
  have hn : 3 ≤ n := by exact_mod_cast (show (3 : ℝ) ≤ n by linarith)
  have hnc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hEc := edgeCapacity_cast (n := n) (by omega)
  have hcap : (n : ℝ) ^ 2 ≤ 4 * T * (edgeCapacity n : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hT.le (by positivity : (0 : ℝ) ≤ edgeCapacity n)
    nlinarith
  have hmw : |(m : ℝ) - p * (edgeCapacity n : ℝ)| ≤
      T * (n : ℝ) ^ 2 * p / Real.sqrt (p * n) := by
    have hid : p * (edgeCapacity n : ℝ) = p * n * ((n : ℝ) - 1) / 2 := by
      rw [hEc]
      ring
    simpa only [hid] using hw.1
  have br := window_bounds (h := ((n - 1 : ℕ) : ℝ)) hT hlarge hcap (by rw [hnc])
    (by rw [hnc]; linarith) hmw hw.2
  have hm0 : (0 : ℤ) ≤ m := by exact_mod_cast br.count_pos.le
  have hd0 : (0 : ℤ) ≤ d := by exact_mod_cast br.degree_nonneg
  have hmc := int_toNat_cast hm0
  have hdc := int_toNat_cast hd0
  have b : RemovalBounds T n p (edgeCapacity n) m.toNat ((n - 1 : ℕ) : ℝ) d.toNat := by
    simpa only [hmc, hdc] using br
  have nd := natural_domain b
  have hsub : (m - d).toNat = m.toNat - d.toNat := Int.toNat_sub'' hm0 hd0
  have hdm : d ≤ m := by
    have hh : (d : ℝ) ≤ m := by simpa only [hmc, hdc] using (show (d.toNat : ℝ) ≤ m.toNat by exact_mod_cast nd.degree_count_le)
    exact_mod_cast hh
  have hmN : m ≤ (edgeCapacity n : ℤ) := by
    have hh : (m : ℝ) ≤ edgeCapacity n := by
      simpa only [hmc] using (show (m.toNat : ℝ) ≤ edgeCapacity n by exact_mod_cast nd.count_le)
    exact_mod_cast hh
  have hrN : m - d ≤ (edgeCapacity (n - 1) : ℤ) := by
    have hh : ((m - d).toNat : ℤ) ≤ edgeCapacity (n - 1) := by
      exact_mod_cast (show (m - d).toNat ≤ edgeCapacity (n - 1) by
        simpa only [hsub, edgeCapacity_pred hn] using nd.residual_le)
    simpa only [Int.toNat_of_nonneg (sub_nonneg.mpr hdm)] using hh
  have hcap2 : (n * (n - 1) : ℕ) = 2 * edgeCapacity n := (edgeCapacity_double n).symm
  have hpred2 : (n - 1) * (n - 2) = 2 * edgeCapacity (n - 1) := by
    rw [edgeCapacity_double]
    congr 1
  have htwo : (2 * m).toNat = 2 * m.toNat := by omega
  have htwosub : (2 * m - 2 * d).toNat = 2 * m.toNat - 2 * d.toNat := by omega
  have hgp : 0 < graphRatio n m d := by
    rw [graphRatio_bridge hn hm0 hd0]
    exact div_pos nd.double.ratio_pos nd.ratio_pos
  refine ⟨⟨hd0, hdm, hm0, hmN, hrN, by omega, ?_, by omega, ?_, ?_, ?_, ?_, ?_⟩,
    hgp, ?_⟩
  · rw [hcap2]
    exact_mod_cast (show 2 * m ≤ 2 * (edgeCapacity n : ℤ) by omega)
  · rw [hpred2]
    exact_mod_cast (show 2 * m - 2 * d ≤ 2 * (edgeCapacity (n - 1) : ℤ) by omega)
  · exact_mod_cast Nat.choose_pos nd.count_le
  · rw [edgeCapacity_pred hn, hsub]
    exact_mod_cast Nat.choose_pos nd.residual_le
  · rw [hcap2, htwo]
    exact_mod_cast Nat.choose_pos nd.double.count_le
  · rw [hpred2, htwosub, edgeCapacity_pred hn]
    have hh : 2 * m.toNat - 2 * d.toNat ≤ 2 * (edgeCapacity n - (n - 1)) := by
      have ht := nd.double.residual_le
      omega
    exact_mod_cast Nat.choose_pos hh
  · rw [graphRatio_bridge hn hm0 hd0,
      Real.log_div nd.double.ratio_pos.ne' nd.ratio_pos.ne']
    have he := graph_removal_estimate hT0.le hlarge.2.1 b
    simpa only [hdc] using he

end MajorityDynamics.Combinatorics.DegreeRatios
