import MajorityDynamics.Probability.NeighborhoodBulk.SparseEnumeration
import MajorityDynamics.Probability.NeighborhoodBulk.BipartiteGrowth

noncomputable section
open Filter
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodBulk
open MajorityDynamics.Literature.DegreeEnumeration

def bipartiteTotals (θ K : ℝ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc ⌊(n : ℝ) / K⌋₊ ⌈K * n⌉₊) ×ˢ graphTotals θ K n

theorem bipartiteTotals_nonempty (θ K : ℝ) (hK : 1 ≤ K) (n : ℕ) :
    (bipartiteTotals θ K n).Nonempty := by
  have hK0 : 0 < K := by linarith
  have hleft : (Finset.Icc ⌊(n : ℝ) / K⌋₊ ⌈K * n⌉₊).Nonempty := by
    apply Finset.nonempty_Icc.mpr
    have hh : (n : ℝ) / K ≤ K * n := by
      apply (div_le_iff₀ hK0).mpr
      have hKsq : 1 ≤ K ^ 2 := one_le_pow₀ hK
      nlinarith [mul_le_mul_of_nonneg_right hKsq (show (0 : ℝ) ≤ n by positivity)]
    have hcast := (Nat.floor_le (show 0 ≤ (n : ℝ) / K by positivity)).trans
      (hh.trans (Nat.le_ceil (K * n)))
    exact_mod_cast hcast
  exact hleft.product (graphTotals_nonempty θ K hK n)

theorem bipartite_scale_mem_totals {θ K : ℝ} {n ell m : ℕ} (hK : 0 < K)
    (h : BipartiteScaleWindow θ K n ell m) : (ell, m) ∈ bipartiteTotals θ K n := by
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, graph_scale_mem_totals hK h.2.2⟩
  · have hh := (Nat.floor_le (show 0 ≤ (n : ℝ) / K by positivity)).trans h.1
    exact_mod_cast hh
  · have hh := h.2.1.trans (Nat.le_ceil (K * n))
    exact_mod_cast hh

theorem eventually_bipartiteTotals_scale (θ K : ℝ) (hθ : θ < 1) (hK : 0 < K) :
    ∀ᶠ n : ℕ in atTop, ∀ q ∈ bipartiteTotals θ K n, BipartiteScaleWindow θ (2 * K) n q.1 q.2 := by
  have hn := tendsto_natCast_atTop_atTop (R := ℝ)
  filter_upwards [eventually_graphTotals_scale θ K hθ hK,
    hn.eventually (eventually_ge_atTop (2 * K)),
    (hn.const_mul_atTop hK).eventually (eventually_ge_atTop 1)] with n hs hnlo hnhi
  intro q hq
  obtain ⟨hell, hm⟩ := Finset.mem_product.mp hq
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hell
  have hlo' : (⌊(n : ℝ) / K⌋₊ : ℝ) ≤ q.1 := by exact_mod_cast hlo
  have hhi' : (q.1 : ℝ) ≤ ⌈K * n⌉₊ := by exact_mod_cast hhi
  have hnlo' : 2 ≤ (n : ℝ) / K := (le_div_iff₀ hK).mpr (by nlinarith)
  refine ⟨?_, ?_, hs q.2 hm⟩
  · have he : (n : ℝ) / (2 * K) = ((n : ℝ) / K) / 2 := by ring
    rw [he]
    nlinarith [Nat.lt_floor_add_one ((n : ℝ) / K)]
  · nlinarith [Nat.ceil_lt_add_one (show 0 ≤ K * (n : ℝ) by positivity)]

theorem bipartite_enumeration_sparse (θ K : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hK : 1 ≤ K) :
    ∀ᶠ n : ℕ in atTop, ∀ ell m : ℕ, BipartiteScaleWindow θ K n ell m →
      ∀ (a : Fin ell → ℕ) (b : Fin n → ℕ), BipartiteSourceData (7 / 12) ell n m a b →
        RelativeApproximation (1 / 2) ((bipartiteDegreeLaw (Fin ell) (Fin n) m).real {(a, b)})
          ((bipartiteBinomialLaw (Fin ell) (Fin n) m).real {(a, b)} * bipartiteCorrection m a b) := by
  have hK0 : 0 < K := by linarith
  obtain ⟨μ₀, hμ₀, hsource⟩ := bipartite_enumeration_uniform_finite
  have hs := eventually_bipartiteTotals_scale θ K hθ1 hK0
  have hdom : ∀ᶠ n in atTop, ∀ q ∈ bipartiteTotals θ K n,
      0 < q.1 ∧ q.2 ≤ q.1 * n ∧ bipartiteDensity q.1 n q.2 < μ₀ ∧
        0 < bipartiteErrorScale (7 / 12) q.1 n q.2 := by
    filter_upwards [hs, eventually_bipartite_scale_domain θ (2 * K) μ₀ hθ0 (by linarith) hμ₀]
      with n hn hcap
    exact fun q hq => hcap q.1 q.2 (hn q hq)
  have hgrowth : ∀ ell m : ℕ → ℕ, (∀ n, (ell n, m n) ∈ bipartiteTotals θ K n) →
      Asymptotics.IsLittleO atTop
        (fun n => ((ell n : ℝ) + n) ^ (5 - 5 * (7 / 12 : ℝ)))
        (fun n => (ell n : ℝ) * n * (m n : ℝ) ^ (3 - 5 * (7 / 12 : ℝ))) ∧
      ∀ r : ℝ, 0 < r → Asymptotics.IsLittleO atTop
        (fun n => (ell n : ℝ) * Real.log n ^ r + (n : ℝ) * Real.log (ell n) ^ r)
        (fun n => (m n : ℝ)) := by
    intro ell m hm
    have hscale : ∀ᶠ n in atTop, BipartiteScaleWindow θ (2 * K) n (ell n) (m n) := by
      filter_upwards [hs] with n hn
      exact hn _ (hm n)
    exact ⟨bipartite_scale_power_growth θ (2 * K) hθ1 (by linarith) ell m hscale,
      bipartite_scale_log_growth θ (2 * K) hθ1 (by linarith) ell m hscale⟩
  obtain ⟨C, hC, hc⟩ := hsource (7 / 12) (by norm_num) (by norm_num)
    (bipartiteTotals θ K) (bipartiteTotals_nonempty θ K hK) hdom hgrowth
  filter_upwards [hc, eventually_bipartite_error_small θ K ((2 * C)⁻¹) hθ1 hK (by positivity)]
    with n hn he
  intro ell m hm a b hd
  apply (hn (ell, m) (bipartite_scale_mem_totals hK0 hm) a b hd).mono
  have hh := mul_le_mul_of_nonneg_left (he ell m hm) hC.le
  have hidentity : C * (2 * C)⁻¹ = (1 / 2 : ℝ) := by field_simp
  exact hh.trans_eq hidentity

theorem eventually_bipartite_input_scale (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ,
      MajorityDynamics.Combinatorics.DegreeRatios.DensityWindow θ T n p →
        ∀ (ell m : ℤ) (a : Fin ell.toNat → ℤ) (b : Fin n → ℤ),
          BipartiteInput T n p ell m a b →
            BipartiteScaleWindow θ (4 * T ^ 2) n ell.toNat m.toNat := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_graph_probability_range θ T hθlo hθhi hT,
    eventually_density_log_le_rpow θ T 2 (1 / 2) hθhi (by linarith)
      (by norm_num) (by norm_num)] with n hn hprob hsmall
  intro p hp ell m a b hd
  have hT0 : 0 < T := by linarith
  have hn0 : 0 < n := by omega
  have hn0r : (0 : ℝ) < n := by exact_mod_cast hn0
  have hp0 := (hprob p hp).1
  have hx : 0 < p * n := mul_pos hp0 hn0r
  have hellr : (0 : ℝ) < ell := (div_pos hn0r hT0).trans_le hd.1
  have hell : 0 < ell := by exact_mod_cast hellr
  have heleq : (ell.toNat : ℝ) = ell := by exact_mod_cast Int.toNat_of_nonneg hell.le
  have helln : (0 : ℝ) < ell.toNat := by simpa only [heleq] using hellr
  have hc := bipartite_input_centered hn0 hell hp0 hd
  have hs : 2 * Real.log n ≤ Real.sqrt (p * n) := by
    simpa only [Real.sqrt_eq_rpow] using hsmall p hp
  have hav := average_ge_half hx.le hc.1.1 hs
  have havhi : leftAverage ell.toNat m.toNat ≤ 3 * (p * n) / 2 := by
    have hh := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg (p * n))
    nlinarith [(abs_le.mp hc.1.1).2, Real.sq_sqrt hx.le]
  have hmlo : p * n * (ell : ℝ) / 2 ≤ m.toNat := by
    have hh := (le_div_iff₀ helln).mp hav
    rw [heleq] at hh
    nlinarith
  have hmhi : (m.toNat : ℝ) ≤ 3 * p * n * (ell : ℝ) / 2 := by
    have hh := (div_le_iff₀ helln).mp havhi
    rw [heleq] at hh
    nlinarith
  have he : (n : ℝ) ^ (-θ) * (n : ℝ) ^ 2 = (n : ℝ) ^ (2 - θ) := by
    rw [← Real.rpow_two, ← Real.rpow_add hn0r]
    congr 1
    ring
  have hlo := mul_le_mul_of_nonneg_right hp.1.le (sq_nonneg (n : ℝ))
  have hhi := mul_le_mul_of_nonneg_right hp.2.le (sq_nonneg (n : ℝ))
  rw [mul_assoc, he] at hlo hhi
  have hK : T ≤ 4 * T ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heleq]
    exact (div_le_div_of_nonneg_left hn0r.le hT0 hK).trans hd.1
  · rw [heleq]
    exact hd.2.1.trans (mul_le_mul_of_nonneg_right hK hn0r.le)
  · have hh := mul_le_mul_of_nonneg_left hd.1 (by positivity : 0 ≤ p * n / 2)
    have hhalf : p * (n : ℝ) ^ 2 / (2 * T) ≤ (m.toNat : ℝ) := by
      have hi : p * n / 2 * ((n : ℝ) / T) = p * (n : ℝ) ^ 2 / (2 * T) := by ring
      rw [hi] at hh
      nlinarith
    have hlow := mul_le_mul_of_nonneg_right hlo (show 0 ≤ (2 * T)⁻¹ by positivity)
    have hpow : 0 ≤ (n : ℝ) ^ (2 - θ) := Real.rpow_nonneg hn0r.le _
    have hi : T⁻¹ * (n : ℝ) ^ (2 - θ) * (2 * T)⁻¹ =
        2 * ((4 * T ^ 2)⁻¹ * (n : ℝ) ^ (2 - θ)) := by ring
    rw [hi] at hlow
    have hm' : p * (n : ℝ) ^ 2 * (2 * T)⁻¹ ≤ m.toNat := by simpa only [div_eq_mul_inv] using hhalf
    have hnonneg : 0 ≤ (4 * T ^ 2)⁻¹ * (n : ℝ) ^ (2 - θ) := by positivity
    linarith
  · have hh := mul_le_mul_of_nonneg_left hd.2.1 (by positivity : 0 ≤ 3 * p * n / 2)
    have hm' : (m.toNat : ℝ) ≤ 3 * T * p * (n : ℝ) ^ 2 / 2 := by nlinarith
    have hu := mul_le_mul_of_nonneg_left hhi (show 0 ≤ 3 * T / 2 by positivity)
    have hnonneg : 0 ≤ T ^ 2 * (n : ℝ) ^ (2 - θ) := by positivity
    nlinarith

theorem eventually_bipartite_input_nonempty (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ,
      MajorityDynamics.Combinatorics.DegreeRatios.DensityWindow θ T n p →
        ∀ (ell m : ℤ) (a : Fin ell.toNat → ℤ) (b : Fin n → ℤ),
          BipartiteInput T n p ell m a b →
            (MajorityDynamics.Probability.FixedDegreeSampling.bipartiteFamily
              (fun i => (a i).toNat) (fun j => (b j).toNat)).Nonempty := by
  filter_upwards [eventually_bipartite_input_scale θ T hθlo hθhi hT,
    eventually_bipartite_source_data θ T hθlo hθhi hT,
    bipartite_enumeration_sparse θ (4 * T ^ 2) (by linarith) hθhi (by nlinarith)] with n hs hd he
  intro p hp ell m a b h
  have hdata := hd p hp ell m a b h
  exact bipartiteFamily_nonempty_of_enumeration (fun i => (a i).toNat) (fun j => (b j).toNat)
    hdata (by norm_num) (he ell.toNat m.toNat (hs p hp ell m a b h) _ _ hdata)

end MajorityDynamics.Probability.NeighborhoodBulk
