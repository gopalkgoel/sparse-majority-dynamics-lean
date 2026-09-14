import MajorityDynamics.Combinatorics.DegreeRatios.Main
import MajorityDynamics.Combinatorics.DegreeRatios.AnalyticBudget
import MajorityDynamics.Combinatorics.DegreeRatios.SparseUniform

/-! Degree-ratio estimates with the original logarithmic error constant,
including densities proportional to `n^(-1/2)`. -/
noncomputable section
open Filter
namespace MajorityDynamics.Combinatorics.DegreeRatios

def SparseGraphDegreeRatioTheorem : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 3 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ p : ℝ, SparseDensityWindow θ T n p →
        ∀ m d : ℤ, GraphWindow T n p m d → GraphEstimate C n p m d

def SparseBipartiteDegreeRatioTheorem : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 3 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ p : ℝ, SparseDensityWindow θ T n p →
        ∀ ell m d : ℤ, BipartiteWindow T n p ell m d → BipartiteEstimate C n p ell m d

def SparseDegreeRatiosTheorem : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 3 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ p : ℝ, SparseDensityWindow θ T n p →
        (∀ m d : ℤ, GraphWindow T n p m d → GraphEstimate C n p m d) ∧
        (∀ ell m d : ℤ, BipartiteWindow T n p ell m d → BipartiteEstimate C n p ell m d)

set_option maxHeartbeats 1600000 in
theorem window_bounds_sparse {T p : ℝ} {n : ℕ} {N m h d : ℝ}
    (hT : 1 < T) (hlarge : SparseLargeParameters T n p)
    (hcap : (n : ℝ) ^ 2 ≤ 4 * T * N)
    (hhlo : (n : ℝ) - 1 ≤ h) (hhhi : h ≤ n)
    (hmwindow : |m - p * N| ≤ T * (n : ℝ) ^ 2 * p / Real.sqrt (p * n))
    (hdwindow : |d - p * n| ≤ Real.sqrt (p * n) * Real.log (n : ℝ)) :
    RemovalBounds T n p N m h d := by
  rcases hlarge with ⟨hnsize, hlog, hp, hpsmall, hsparse, hscale⟩
  have hT0 : 0 < T := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hn64 : (64 : ℝ) ≤ n := by linarith
  have hN : 0 < N := by
    by_contra hc
    have hh := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 4 * T) (le_of_not_gt hc)
    nlinarith [sq_pos_of_pos hn0]
  have hNbig : 16 * (n : ℝ) ≤ N := by
    have hh := mul_le_mul_of_nonneg_right hnsize hn0.le
    by_contra hc
    have hhpos := mul_pos hT0 (sub_pos.mpr (lt_of_not_ge hc))
    nlinarith
  have hh0 : 0 ≤ h := by linarith
  have hK : 0 < relativeConstant T := by dsimp [relativeConstant]; positivity
  have hu0 : 0 < p * (n : ℝ) := mul_pos hp hn0
  have hs0 : 0 < Real.sqrt (p * n) := Real.sqrt_pos.mpr (mul_pos hp hn0)
  have hss : Real.sqrt (p * n) ^ 2 = p * n := Real.sq_sqrt (by positivity)
  have hL0 : 0 ≤ Real.log (n : ℝ) := by linarith
  have hsK : 2 * relativeConstant T ≤ Real.sqrt (p * n) := by
    nlinarith [mul_nonneg hK.le hL0]
  have hsL : 2 * Real.log (n : ℝ) ≤ Real.sqrt (p * n) := by
    nlinarith [mul_nonneg hK.le hL0]
  have hdev : |d - p * n| ≤ p * n / 2 := by
    have hh := mul_le_mul_of_nonneg_left hsL hs0.le
    nlinarith
  have hd0 : 0 ≤ d := by linarith [(abs_le.mp hdev).1]
  have hdu : d ≤ 2 * (p * n) := by linarith [(abs_le.mp hdev).2]
  have hdh : d ≤ h := by
    have hh := mul_le_mul_of_nonneg_right hpsmall hn0.le
    linarith
  have hcapT : T * (n : ℝ) ^ 2 ≤ relativeConstant T * N := by
    have hh := mul_le_mul_of_nonneg_left hcap hT0.le
    dsimp [relativeConstant]
    nlinarith
  have hdevm : |m - p * N| ≤ p * N / 2 := by
    have hh : T * (n : ℝ) ^ 2 * p ≤ relativeConstant T * (p * N) := by
      have ht := mul_le_mul_of_nonneg_right hcapT hp.le
      nlinarith
    have hh2 := mul_le_mul_of_nonneg_right hsK (mul_pos hp hN).le
    have hbound : T * (n : ℝ) ^ 2 * p / Real.sqrt (p * n) ≤ p * N / 2 := by
      apply (div_le_iff₀ hs0).mpr
      nlinarith
    exact hmwindow.trans hbound
  have hmlo : p * N / 2 ≤ m := by linarith [(abs_le.mp hdevm).1]
  have hmhi : m ≤ 3 / 2 * p * N := by linarith [(abs_le.mp hdevm).2]
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hmlo
  have hmhalf : 2 * m ≤ N := by
    have hh := mul_le_mul_of_nonneg_right hpsmall hN.le
    linarith
  have hmN : m < N := by linarith
  have hcount : 2 * d ≤ m := by
    have hh := mul_le_mul_of_nonneg_left hNbig hp.le
    nlinarith
  have hroom : 2 * (h - d) ≤ N - m := by linarith
  have hcaperr : h ^ 2 / N ≤ 4 * T := by
    apply (div_le_iff₀ hN).mpr
    have hh := (sq_le_sq₀ hh0 hn0.le).mpr hhhi
    nlinarith
  have hmerr : d ^ 2 / m ≤ 2 * T := by
    apply (div_le_iff₀ hm0).mpr
    have hd2 := (sq_le_sq₀ hd0 (by positivity : 0 ≤ 2 * (p * n))).mpr hdu
    have h1 := mul_le_mul_of_nonneg_left hcap (by positivity : 0 ≤ 4 * p ^ 2)
    have h2 := mul_le_mul_of_nonneg_left hmlo (by positivity : 0 ≤ 32 * T * p)
    have h3 := mul_le_mul_of_nonneg_right hpsmall (by positivity : 0 ≤ 32 * T * m)
    nlinarith
  have hrerr : (h - d) ^ 2 / (N - m) ≤ 8 * T := by
    apply (div_le_iff₀ (sub_pos.mpr hmN)).mpr
    have hh := (sq_le_sq₀ (sub_nonneg.mpr hdh) hn0.le).mpr (show h - d ≤ n by linarith)
    have ht := mul_le_mul_of_nonneg_left hmhalf hT0.le
    nlinarith
  refine ⟨hN, hm0, hmN, hd0, hdh, by linarith, hcount, hroom, hcaperr, hmerr, hrerr, ?_⟩
  let t := (m - p * N) / (p * N)
  have hpN : 0 < p * N := mul_pos hp hN
  have hqt : m / N = p * (1 + t) := by
    dsimp [t]
    field_simp
    ring
  have ht : |t| ≤ 1 / 2 := by
    dsimp [t]
    rw [abs_div, abs_of_pos hpN, div_le_iff₀ hpN]
    linarith
  have hrelative : Real.sqrt (p * n) * |t| ≤ relativeConstant T := by
    dsimp [t]
    rw [abs_div, abs_of_pos hpN, ← mul_div_assoc, div_le_iff₀ hpN]
    have hh := (le_div_iff₀ hs0).mp hmwindow
    have hh2 := mul_le_mul_of_nonneg_right hcapT hp.le
    nlinarith
  have hqsmall : |m / N| ≤ 1 / 2 := by
    rw [abs_of_pos (div_pos hm0 hN), div_le_iff₀ hN]
    linarith
  have hcenter : |h * p - p * n| ≤ p := by
    apply abs_le.mpr
    have h1 := mul_le_mul_of_nonneg_right hhlo hp.le
    have h2 := mul_le_mul_of_nonneg_right hhhi hp.le
    constructor <;> nlinarith
  have he := density_error_bound_budget hn0.le hp (by linarith : p ≤ 1) rfl
    hd0 hdh hhhi hdu hcenter hdwindow hK.le hlog ht hrelative hqt hqsmall hsparse
  apply he.trans
  have hh := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 4 * relativeConstant T ^ 2 + 2)
  nlinarith

theorem graph_estimate_of_large_sparse {T p : ℝ} {n : ℕ} {m d : ℤ}
    (hT : 1 < T) (hlarge : SparseLargeParameters T n p)
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
  have br := window_bounds_sparse (h := ((n - 1 : ℕ) : ℝ)) hT hlarge hcap (by rw [hnc])
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

theorem bipartite_estimate_of_large_sparse {T p : ℝ} {n : ℕ} {ell m d : ℤ}
    (hT : 1 < T) (hlarge : SparseLargeParameters T n p)
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
  have br := window_bounds_sparse hT hlarge hcap (by linarith : (n : ℝ) - 1 ≤ n)
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

theorem degree_ratios_sparse : SparseDegreeRatiosTheorem := by
  intro θ T hθlo hθhi hT
  have hT0 : 0 < T := by linarith
  obtain ⟨n₀, hn₀⟩ := (eventually_atTop.mp (eventually_sparse_large_parameters θ T hθlo hθhi hT))
  refine ⟨errorConstant T, max 3 n₀, ?_, le_max_left _ _, ?_⟩
  · dsimp [errorConstant, relativeConstant]
    positivity
  · intro n hn p hp
    have hl := hn₀ n (le_trans (le_max_right _ _) hn) p hp
    exact ⟨fun m d hw => graph_estimate_of_large_sparse hT hl hw,
      fun ell m d hw => bipartite_estimate_of_large_sparse hT hl hw⟩

theorem graph_degree_ratio_sparse : SparseGraphDegreeRatioTheorem := by
  intro θ T hθlo hθhi hT
  obtain ⟨C, n₀, hC, hn₀, hall⟩ := degree_ratios_sparse θ T hθlo hθhi hT
  exact ⟨C, n₀, hC, hn₀, fun n hn p hp => (hall n hn p hp).1⟩

theorem bipartite_degree_ratio_sparse : SparseBipartiteDegreeRatioTheorem := by
  intro θ T hθlo hθhi hT
  obtain ⟨C, n₀, hC, hn₀, hall⟩ := degree_ratios_sparse θ T hθlo hθhi hT
  exact ⟨C, n₀, hC, hn₀, fun n hn p hp => (hall n hn p hp).2⟩

end MajorityDynamics.Combinatorics.DegreeRatios

