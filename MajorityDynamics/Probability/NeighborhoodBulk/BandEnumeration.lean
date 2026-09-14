import MajorityDynamics.Probability.NeighborhoodBulk.BandSourceGrowth

/-! Application of the graph source with all polynomial-scale growth and
uniformity obligations discharged. No graphicality hypothesis is required. -/
noncomputable section
open Filter
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodBulk
open MajorityDynamics.Literature.DegreeEnumeration

def graphBandTotals (θ η K : ℝ) (n : ℕ) : Finset ℕ :=
  Finset.Icc ⌊K⁻¹ * (n : ℝ) ^ (2 - θ)⌋₊ ⌈K * (n : ℝ) ^ (2 - η)⌉₊

theorem graphBandTotals_nonempty (θ η K : ℝ) (hηθ : η ≤ θ) (hθ : θ < 1) (hK : 1 ≤ K) (n : ℕ) : (graphBandTotals θ η K n).Nonempty := by
  have hK0 : 0 < K := by linarith
  have hi : K⁻¹ ≤ K := by
    have : K⁻¹ ≤ 1 := (inv_le_one₀ hK0).mpr hK
    linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [graphBandTotals, Real.zero_rpow (by linarith : 2 - θ ≠ 0),
      Real.zero_rpow (by linarith : 2 - η ≠ 0)]
  have hpow : (n : ℝ) ^ (2 - θ) ≤ (n : ℝ) ^ (2 - η) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)
  apply Finset.nonempty_Icc.mpr
  have hh := (Nat.floor_le (show 0 ≤ K⁻¹ * (n : ℝ) ^ (2 - θ) by positivity)).trans
    ((mul_le_mul hi hpow (by positivity) hK0.le).trans
      (Nat.le_ceil (K * (n : ℝ) ^ (2 - η))))
  exact_mod_cast hh

theorem graph_band_mem_totals {θ η K : ℝ} {n m : ℕ} (hK : 0 < K)
    (h : GraphBandWindow θ η K n m) : m ∈ graphBandTotals θ η K n := by
  apply Finset.mem_Icc.mpr
  constructor
  · have hh := (Nat.floor_le (show 0 ≤ K⁻¹ * (n : ℝ) ^ (2 - θ) by positivity)).trans h.1
    exact_mod_cast hh
  · have hh := h.2.trans (Nat.le_ceil (K * (n : ℝ) ^ (2 - η)))
    exact_mod_cast hh

theorem eventually_graphBandTotals_scale (θ η K : ℝ) (hθ : θ < 1) (hη : η < 1) (hK : 0 < K) :
    ∀ᶠ n : ℕ in atTop, ∀ m ∈ graphBandTotals θ η K n, GraphBandWindow θ η (2 * K) n m := by
  have hn := tendsto_natCast_atTop_atTop (R := ℝ)
  have hl := (((tendsto_rpow_atTop (by linarith : 0 < 2 - θ)).comp hn).const_mul_atTop
    (show 0 < K⁻¹ by positivity)).eventually (eventually_ge_atTop 2)
  have hu := (((tendsto_rpow_atTop (by linarith : 0 < 2 - η)).comp hn).const_mul_atTop hK).eventually
    (eventually_ge_atTop 1)
  filter_upwards [hl, hu] with n hnlo hnhi
  simp only [Function.comp_apply] at hnlo hnhi
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hm
  have hlo' : (⌊K⁻¹ * (n : ℝ) ^ (2 - θ)⌋₊ : ℝ) ≤ m := by exact_mod_cast hlo
  have hhi' : (m : ℝ) ≤ ⌈K * (n : ℝ) ^ (2 - η)⌉₊ := by exact_mod_cast hhi
  constructor
  · have he : (2 * K)⁻¹ * (n : ℝ) ^ (2 - θ) = K⁻¹ * (n : ℝ) ^ (2 - θ) / 2 := by ring
    rw [he]
    nlinarith [Nat.lt_floor_add_one (K⁻¹ * (n : ℝ) ^ (2 - θ))]
  · have hh := Nat.ceil_lt_add_one (show 0 ≤ K * (n : ℝ) ^ (2 - η) by positivity)
    nlinarith

theorem graph_enumeration_band (θ η K : ℝ) (hη0 : 0 < η) (hηθ : η ≤ θ) (hθ1 : θ < 1) (hK : 1 ≤ K) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, GraphBandWindow θ η K n m →
      ∀ d : Fin n → ℕ, GraphSourceData (7 / 12) n m d →
        RelativeApproximation (1 / 2) ((graphDegreeLaw (Fin n) m).real {d})
          ((graphBinomialLaw (Fin n) m).real {d} * graphCorrection m d) := by
  have hK0 : 0 < K := by linarith
  obtain ⟨μ₀, hμ₀, hsource⟩ := graph_enumeration_uniform_finite
  have hs := eventually_graphBandTotals_scale θ η K hθ1 (hηθ.trans_lt hθ1) hK0
  have hdom : ∀ᶠ n in atTop, ∀ m ∈ graphBandTotals θ η K n,
      m ≤ n.choose 2 ∧ graphDensity n m ≤ μ₀ ∧ 0 < graphErrorScale (7 / 12) n m := by
    filter_upwards [hs, eventually_graph_band_domain θ η (2 * K) μ₀ hη0 (by positivity) hμ₀]
      with n hn hcap
    exact fun m hm => hcap m (hn m hm)
  have hgrowth : ∀ m : ℕ → ℕ, (∀ n, m n ∈ graphBandTotals θ η K n) → ∀ r : ℝ, 0 < r →
      Asymptotics.IsLittleO atTop (fun n : ℕ => Real.log n ^ r / (n : ℝ))
        (fun n => graphDensity n (m n)) := by
    intro m hm r _
    apply graph_band_log_growth θ η (2 * K) hθ1 (by positivity) m ?_ r
    filter_upwards [hs] with n hn
    exact hn (m n) (hm n)
  obtain ⟨C, hC, hc⟩ := hsource (7 / 12) (by norm_num) (by norm_num)
    (graphBandTotals θ η K) (graphBandTotals_nonempty θ η K hηθ hθ1 hK) hdom hgrowth
  filter_upwards [hc, eventually_graph_band_error_small θ η K ((2 * C)⁻¹) hθ1 hK0 (by positivity)]
    with n hn he
  intro m hm d hd
  apply (hn m (graph_band_mem_totals hK0 hm) d hd).mono
  have hh := mul_le_mul_of_nonneg_left (he m hm) hC.le
  have hidentity : C * (2 * C)⁻¹ = (1 / 2 : ℝ) := by field_simp
  exact hh.trans_eq hidentity

theorem graphFamily_nonempty_band (θ η K : ℝ) (hη0 : 0 < η) (hηθ : η ≤ θ) (hθ1 : θ < 1) (hK : 1 ≤ K) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, GraphBandWindow θ η K n m →
      ∀ d : Fin n → ℕ, GraphSourceData (7 / 12) n m d →
        (MajorityDynamics.Probability.FixedDegreeSampling.graphFamily d).Nonempty := by
  filter_upwards [graph_enumeration_band θ η K hη0 hηθ hθ1 hK] with n hn
  intro m hm d hd
  exact graphFamily_nonempty_of_enumeration d hd (by norm_num) (hn m hm d hd)


end MajorityDynamics.Probability.NeighborhoodBulk
