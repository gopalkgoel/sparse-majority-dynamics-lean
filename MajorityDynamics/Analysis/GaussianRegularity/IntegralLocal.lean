import MajorityDynamics.Analysis.GaussianRegularity.IntegralDensity
import MajorityDynamics.Analysis.GaussianRegularity.Domain
import MajorityDynamics.Analysis.GaussianRegularity.Law

noncomputable section
open Set MeasureTheory
open scoped NNReal
namespace MajorityDynamics.Analysis.GaussianRegularity

private theorem continuous_density_argument {d : ℕ} (m v : ConditionalGaussian.Space d) :
    Continuous (fun x : ConditionalGaussian.Space d => density m v x) := by
  unfold density scalarDensity
  fun_prop

/-- Polynomially weighted Gaussian integrals over an arbitrary fixed region
are uniformly Lipschitz on each bounded positive-variance parameter box. -/
theorem lipschitzOn_weighted_density_integral {d r : ℕ} {a R : ℝ}
    (ha : 0 < a) (hR : 0 < R) (O : Set (ConditionalGaussian.Space d))
    {f : ConditionalGaussian.Space d → ℝ} (hf : Continuous f)
    (hgrowth : ∃ C : ℝ, ∃ n : ℕ, ∀ x, ‖f x‖ ≤ C * ‖x‖ ^ n) :
    ∃ L : ℝ≥0, LipschitzOnWith L
      (fun p : Parameters d r => ∫ x in O, f x * density p.1.1 p.1.2 x)
      (parameterBox a R) := by
  obtain ⟨K, n, hK⟩ := hgrowth
  have hK' (x : ConditionalGaussian.Space d) : ‖f x‖ ≤ |K| * ‖x‖ ^ n :=
    (hK x).trans (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity))
  obtain ⟨C, c, hC, hc, hbound, hdiff⟩ := density_uniform_envelopes (d := d) hR.le ha hR
  have hcoords (p : Parameters d r) (hp : p ∈ parameterBox a R) :
      (∀ i, |p.1.1 i| ≤ R) ∧ (∀ i, a ≤ p.1.2 i) ∧ (∀ i, p.1.2 i ≤ R) := by
    refine ⟨?_, hp.2, ?_⟩
    · intro i
      exact (PiLp.norm_apply_le p.1.1 i).trans
        ((norm_fst_le p.1).trans ((norm_fst_le p).trans hp.1))
    · intro i
      exact (le_abs_self _).trans ((PiLp.norm_apply_le p.1.2 i).trans
        ((norm_snd_le p.1).trans ((norm_fst_le p).trans hp.1)))
  let B : ConditionalGaussian.Space d → ℝ :=
    fun x => (2 * d * C * |K|) * (‖x‖ ^ n * Real.exp (-c * ‖x‖ ^ 2))
  have hB : Integrable B (volume.restrict O) :=
    ((integrable_norm_pow_mul_gaussian hc n).const_mul (2*d*C*|K|)).restrict
  have hBpos (x) : 0 ≤ B x := by dsimp [B]; positivity
  have hInt (p : Parameters d r) (hp : p ∈ parameterBox a R) :
      Integrable (fun x => f x * density p.1.1 p.1.2 x) (volume.restrict O) := by
    have hi := ((integrable_norm_pow_mul_gaussian (d := d) hc n).const_mul (C*|K|)).restrict (s := O)
    apply hi.mono' (hf.mul (continuous_density_argument _ _)).aestronglyMeasurable
    apply ae_of_all
    intro x
    simp only [Pi.mul_apply, norm_mul]
    obtain ⟨hm,hv,hvb⟩ := hcoords p hp
    calc
      _ ≤ (|K| * ‖x‖ ^ n) * (C * Real.exp (-c * ‖x‖ ^ 2)) :=
        mul_le_mul (hK' x) (hbound _ _ _ hm hv hvb) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  refine ⟨Real.toNNReal (∫ x in O, B x),
    lipschitzOnWith_integral_of_envelope hB hBpos hInt ?_⟩
  intro p hp q hq x
  obtain ⟨hm,hv,hvb⟩ := hcoords p hp
  obtain ⟨hm',hv',hvb'⟩ := hcoords q hq
  rw [← mul_sub, norm_mul]
  have hd := hdiff p.1.1 p.1.2 q.1.1 q.1.2 x hm hv hvb hm' hv' hvb'
  have hpq : ‖p.1 - q.1‖ ≤ ‖p - q‖ := norm_fst_le (p-q)
  calc
    _ ≤ (|K| * ‖x‖ ^ n) *
        ((2 * d * C * Real.exp (-c * ‖x‖ ^ 2)) * ‖p.1 - q.1‖) :=
      mul_le_mul (hK' x) hd (norm_nonneg _) (by positivity)
    _ ≤ (|K| * ‖x‖ ^ n) *
        ((2 * d * C * Real.exp (-c * ‖x‖ ^ 2)) * ‖p - q‖) := by
      gcongr
    _ = B x * ‖p - q‖ := by dsimp [B]; ring

/-- The preceding fixed-region estimate for the actual Gaussian law. -/
theorem lipschitzOn_weighted_law_integral {d r : ℕ} {a R : ℝ}
    (ha : 0 < a) (hR : 0 < R) (O : Set (ConditionalGaussian.Space d))
    {f : ConditionalGaussian.Space d → ℝ} (hf : Continuous f)
    (hgrowth : ∃ C : ℝ, ∃ n : ℕ, ∀ x, ‖f x‖ ≤ C * ‖x‖ ^ n) :
    ∃ L : ℝ≥0, LipschitzOnWith L
      (fun p : Parameters d r => ∫ x in O, f x ∂law p)
      (parameterBox a R) := by
  obtain ⟨L,hL⟩ := lipschitzOn_weighted_density_integral (r := r) ha hR O hf hgrowth
  have heq (p : Parameters d r) (hp : p ∈ parameterBox a R) :
      (∫ x in O, f x ∂law p) = ∫ x in O, f x * density p.1.1 p.1.2 x := by
    rw [setIntegral_law_eq_density p (fun i => ha.trans_le (hp.2 i)) O f]
    apply integral_congr_ae
    exact ae_of_all _ fun x => mul_comm _ _
  refine ⟨L, ?_⟩
  intro p hp q hq
  dsimp only
  rw [heq p hp, heq q hq]
  exact hL hp hq

/-- Joint local Lipschitz regularity in mean and positive diagonal variance,
for every continuous polynomial multiplier and every fixed region. -/
theorem locallyLipschitzOn_weighted_law_integral {d r : ℕ}
    (O : Set (ConditionalGaussian.Space d)) {f : ConditionalGaussian.Space d → ℝ}
    (hf : Continuous f)
    (hgrowth : ∃ C : ℝ, ∃ n : ℕ, ∀ x, ‖f x‖ ≤ C * ‖x‖ ^ n) :
    LocallyLipschitzOn {p : Parameters d r | positiveVariance p}
      (fun p => ∫ x in O, f x ∂law p) := by
  intro p hp
  obtain ⟨a,R,ha,hR,hbox⟩ := exists_parameterBox_mem_nhds hp
  obtain ⟨L,hL⟩ := lipschitzOn_weighted_law_integral ha hR O hf hgrowth
  exact ⟨L, parameterBox a R, mem_nhdsWithin_of_mem_nhds hbox, hL⟩

end MajorityDynamics.Analysis.GaussianRegularity
