import MajorityDynamics.Probability.NeighborhoodBulk.BandEnumeration
import MajorityDynamics.Probability.NeighborhoodBulk.BipartiteBandGrowth

noncomputable section
open Filter
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodBulk
open MajorityDynamics.Literature.DegreeEnumeration

def bipartiteBandTotals (θ η K : ℝ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc ⌊(n : ℝ) / K⌋₊ ⌈K * n⌉₊) ×ˢ graphBandTotals θ η K n

theorem bipartiteBandTotals_nonempty (θ η K : ℝ) (hηθ : η ≤ θ) (hθ : θ < 1) (hK : 1 ≤ K) (n : ℕ) :
    (bipartiteBandTotals θ η K n).Nonempty := by
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
  exact hleft.product (graphBandTotals_nonempty θ η K hηθ hθ hK n)

theorem bipartite_band_mem_totals {θ η K : ℝ} {n ell m : ℕ} (hK : 0 < K)
    (h : BipartiteBandWindow θ η K n ell m) : (ell, m) ∈ bipartiteBandTotals θ η K n := by
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, graph_band_mem_totals hK h.2.2⟩
  · have hh := (Nat.floor_le (show 0 ≤ (n : ℝ) / K by positivity)).trans h.1
    exact_mod_cast hh
  · have hh := h.2.1.trans (Nat.le_ceil (K * n))
    exact_mod_cast hh

theorem eventually_bipartiteBandTotals_scale (θ η K : ℝ) (hθ : θ < 1) (hη : η < 1) (hK : 0 < K) :
    ∀ᶠ n : ℕ in atTop, ∀ q ∈ bipartiteBandTotals θ η K n, BipartiteBandWindow θ η (2 * K) n q.1 q.2 := by
  have hn := tendsto_natCast_atTop_atTop (R := ℝ)
  filter_upwards [eventually_graphBandTotals_scale θ η K hθ hη hK,
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

theorem bipartite_enumeration_band (θ η K : ℝ) (hη0 : 0 < η) (hηθ : η ≤ θ) (hθ1 : θ < 1) (hK : 1 ≤ K) :
    ∀ᶠ n : ℕ in atTop, ∀ ell m : ℕ, BipartiteBandWindow θ η K n ell m →
      ∀ (a : Fin ell → ℕ) (b : Fin n → ℕ), BipartiteSourceData (7 / 12) ell n m a b →
        RelativeApproximation (1 / 2) ((bipartiteDegreeLaw (Fin ell) (Fin n) m).real {(a, b)})
          ((bipartiteBinomialLaw (Fin ell) (Fin n) m).real {(a, b)} * bipartiteCorrection m a b) := by
  have hK0 : 0 < K := by linarith
  obtain ⟨μ₀, hμ₀, hsource⟩ := bipartite_enumeration_uniform_finite
  have hs := eventually_bipartiteBandTotals_scale θ η K hθ1 (hηθ.trans_lt hθ1) hK0
  have hdom : ∀ᶠ n in atTop, ∀ q ∈ bipartiteBandTotals θ η K n,
      0 < q.1 ∧ q.2 ≤ q.1 * n ∧ bipartiteDensity q.1 n q.2 < μ₀ ∧
        0 < bipartiteErrorScale (7 / 12) q.1 n q.2 := by
    filter_upwards [hs, eventually_bipartite_band_domain θ η (2 * K) μ₀ hη0 (by linarith) hμ₀]
      with n hn hcap
    exact fun q hq => hcap q.1 q.2 (hn q hq)
  have hgrowth : ∀ ell m : ℕ → ℕ, (∀ n, (ell n, m n) ∈ bipartiteBandTotals θ η K n) →
      Asymptotics.IsLittleO atTop
        (fun n => ((ell n : ℝ) + n) ^ (5 - 5 * (7 / 12 : ℝ)))
        (fun n => (ell n : ℝ) * n * (m n : ℝ) ^ (3 - 5 * (7 / 12 : ℝ))) ∧
      ∀ r : ℝ, 0 < r → Asymptotics.IsLittleO atTop
        (fun n => (ell n : ℝ) * Real.log n ^ r + (n : ℝ) * Real.log (ell n) ^ r)
        (fun n => (m n : ℝ)) := by
    intro ell m hm
    have hscale : ∀ᶠ n in atTop, BipartiteBandWindow θ η (2 * K) n (ell n) (m n) := by
      filter_upwards [hs] with n hn
      exact hn _ (hm n)
    exact ⟨bipartite_band_power_growth θ η (2 * K) hθ1 (by linarith) ell m hscale,
      bipartite_band_log_growth θ η (2 * K) hθ1 (by linarith) ell m hscale⟩
  obtain ⟨C, hC, hc⟩ := hsource (7 / 12) (by norm_num) (by norm_num)
    (bipartiteBandTotals θ η K) (bipartiteBandTotals_nonempty θ η K hηθ hθ1 hK) hdom hgrowth
  filter_upwards [hc, eventually_bipartite_band_error_small θ η K ((2 * C)⁻¹) hθ1 hK (by positivity)]
    with n hn he
  intro ell m hm a b hd
  apply (hn (ell, m) (bipartite_band_mem_totals hK0 hm) a b hd).mono
  have hh := mul_le_mul_of_nonneg_left (he ell m hm) hC.le
  have hidentity : C * (2 * C)⁻¹ = (1 / 2 : ℝ) := by field_simp
  exact hh.trans_eq hidentity


end MajorityDynamics.Probability.NeighborhoodBulk
