import MajorityDynamics.Idealized.PerturbedEvolution.TemplateEdges
import MajorityDynamics.Idealized.PerturbedEvolution.TemplateSizes
import MajorityDynamics.Idealized.PerturbedEvolution.ReferenceMeans
import MajorityDynamics.Idealized.PerturbedEvolution.TemplateParentEdges
import MajorityDynamics.Idealized.PerturbedEvolution.TemplateReference

noncomputable section
open Filter Topology
namespace MajorityDynamics.Idealized.PerturbedEvolution
open Universal LinearResponse PerturbedTilt
open Binomial.Approximation (Density scale)

/-- Uniform conversion of the additive size response to a ratio response. -/
theorem size_ratio_response_uniform {N x z zf v v₀ τ h e r K E : ℝ}
    (hN : 0 < N) (hv₀ : 0 < v₀) (hv : v₀ ≤ v)
    (hz : N * v / 2 ≤ z) (hclose : |z - N * v| ≤ 2 * N * r)
    (hfloor : |zf - z| ≤ 1) (hτ : 0 ≤ τ) (hh : 0 ≤ h)
    (hr : 0 ≤ r) (hlarge : 1 ≤ N * h * r) (he : |e| ≤ E)
    (herr : |x - zf - τ * N * h * e| ≤ K * N * h * r) :
    |x / z - (1 + τ * h * (e / v))| ≤
      (2 / v₀ * (K + 1) + 4 / v₀ ^ 2 * (τ * E)) * h * r := by
  have hvpos : 0 < v := hv₀.trans_le hv
  have hE : 0 ≤ E := (abs_nonneg _).trans he
  have hK : 0 ≤ K := by
    have hh0 : 0 < N * h * r := zero_lt_one.trans_le hlarge
    apply nonneg_of_mul_nonneg_right _ hh0
    nlinarith only [(abs_nonneg _).trans herr]
  have habs : |x - z - τ * N * h * e| ≤ N * ((K + 1) * h * r) := by
    have hid : x - z - τ * N * h * e = (x - zf - τ * N * h * e) + (zf - z) := by ring
    rw [hid]
    exact (abs_add_le _ _).trans ((add_le_add herr hfloor).trans (by nlinarith only [hlarge]))
  have hratio := size_ratio_response hN hvpos hz
    (show |z - N * v| ≤ N * (2 * r) by nlinarith only [hclose]) hτ hh he habs
  have hvrec : 1 / v ≤ 1 / v₀ := one_div_le_one_div_of_le hv₀ hv
  have hvrec2 : 1 / v ^ 2 ≤ 1 / v₀ ^ 2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos hv₀) (pow_le_pow_left₀ hv₀.le hv 2)
  apply hratio.trans
  have h1 := mul_le_mul_of_nonneg_right hvrec (show 0 ≤ 2 * ((K + 1) * h * r) by positivity)
  have h2 := mul_le_mul_of_nonneg_right hvrec2 (show 0 ≤ 4 * r * (τ * h * E) by positivity)
  convert add_le_add h1 h2 using 1 <;> ring

/-- The conditional-mean response gives a common relative error constant. -/
theorem child_mean_relative_uniform {n N : ℕ} {p : Binomial.Probability}
    {a : Process.Data} {sizes : Local.Sizes n} {q : Local.Tilt n}
    {τ T R C κ c : ℝ} (hN : 0 < N) (hc : 0 < c) (hC : 0 ≤ C)
    (hT : 0 ≤ T) (_hτ : 0 ≤ τ) (hτT : τ ≤ T)
    (hresponse : ∀ s, ResponseConclusion N p a n sizes s τ R C κ)
    (σ : History (n + 1) → Row (n + 1))
    (hσ : ∀ s t, |σ s t| ≤ R)
    (hq : ∀ s, q s = processEffectiveTilt N p a n sizes s τ (σ s))
    (hmean : ∀ s b t, c * ((p : ℝ) * N) ≤
      LinearResponse.childMean (a.state n).sizes s b (a.tilt n s) t) :
    ∀ s b t, |Process.childMean sizes q s b t /
      Process.childMean (a.state n).sizes (a.tilt n) s b t - 1| ≤
      (C * T / c) * betaScale N p n := by
  intro s b t
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hpN : 0 < (p : ℝ) * N := mul_pos p.property.1 hNr
  have hβ := betaScale_nonneg N (p : ℝ) n
  apply relative_mean_error (mul_pos hc hpN) (hmean s b t) hβ (by positivity)
  have hm := (hresponse s).child_mean_response (σ s) (hσ s) b t
  have hm' : |Process.childMean sizes q s b t -
      Process.childMean (a.state n).sizes (a.tilt n) s b t| ≤
      C * (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)) := by
    simpa only [Process.childMean, LinearResponse.childMean, hq s] using hm
  apply hm'.trans
  have ht := mul_le_mul_of_nonneg_left hτT
    (show 0 ≤ C * betaScale N (p : ℝ) n * ((p : ℝ) * N) by positivity)
  convert ht using 1 <;> field_simp

set_option maxHeartbeats 1200000 in
/-- Uniform Step 5 once the two reference-only geometry bounds and the F2
parent ratio estimate have been supplied. These assumptions contain no target
edge-template conclusion. -/
theorem template_edges_of_reference_bounds (θ T δ : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hδ : 0 < δ)
    (n ell : ℕ) (hell : 1 ≤ ell) (hk : (n : ℝ) + 1 < 1 / (1 - θ))
    (W Jp : ℝ) (hW : 0 < W) (hJp : 0 < Jp)
    (hgeometry : ∀ᶠ N : ℕ in atTop,
      ∀ p : Binomial.Probability, Density θ T N p →
      ∀ a : Process.Data, Process.Specification N p (responseHorizon θ) ell a →
      (∀ u, (N : ℝ) * ν (n + 1) u / 2 ≤ Local.templateSizes (a.state n).sizes (a.tilt n) u ∧
        |Local.templateSizes (a.state n).sizes (a.tilt n) u - N * ν (n + 1) u| ≤
          2 * N * (N : ℝ) ^ (-tiltRate θ δ n)) ∧
      (∀ u v, |(a.state (n + 1)).edges u v| ≤ W * (p : ℝ) * (N : ℝ) ^ 2))
    (hparent : ∀ᶠ N : ℕ in atTop,
      ∀ p : Binomial.Probability, Density θ T N p →
      ∀ a : Process.Data, Process.Specification N p (responseHorizon θ) ell a →
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ η : History (n + 1) → ℤ, ∀ e : History (n + 1) → History (n + 1) → ℤ,
      FaithfulNumericalData N (p : ℝ) T δ τ a n η e →
      ∀ s t, |(e s t : ℝ) / (a.state n).edges s t - 1| ≤ Jp * betaScale N p n) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ p : Binomial.Probability, Density θ T N p →
      ∀ a : Process.Data, Process.Specification N p (responseHorizon θ) ell a →
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ η : History (n + 1) → ℤ, ∀ e : History (n + 1) → History (n + 1) → ℤ,
      FaithfulNumericalData N (p : ℝ) T δ τ a n η e →
      ∀ q : Local.Tilt n, Local.Solves (naturalSizes η) (realEdges e) q →
      ∀ u v : History (n + 2),
        |Local.templateEdges (naturalSizes η) (realEdges e) q u v -
          (a.state (n + 1)).edges u v * (1 + τ * betaScale N p (n + 1) *
          (ε (n + 1) u / ν (n + 1) u + ε (n + 1) v / ν (n + 1) v))| ≤
          K * betaScale N p (n + 1) * (N : ℝ) ^ (-tiltRate θ δ n) * (N : ℝ) ^ 2 * p := by
  classical
  have hT0 : 0 < T := by linarith
  obtain ⟨Ks, hKs, Ns, hNs, hsizes⟩ := template_sizes_spec θ T δ hθlo hθhi hT hδ n ell hell hk
  obtain ⟨T₀, _, R, _, C, hC, B₀, _, Nr, hNr, hresponse⟩ :=
    perturbed_tilt_response_spec θ T δ hθlo hθhi hT hδ n ell hell hk
  obtain ⟨Km, _, c, hc, hmeans⟩ := reference_child_mean_bounds θ T hθlo hθhi hT n ell hell hk
  obtain ⟨v₀, hv₀, hv⟩ := RowLimits.finite_common_positive (ν (n + 1)) (ν_positive (n + 1))
  obtain ⟨E, hE, hε⟩ := finite_abs_bound (ε (n + 1))
  obtain ⟨M, hM, hratio⟩ := finite_abs_bound (fun u => ε (n + 1) u / ν (n + 1) u)
  let B := T * M
  let A := 2 / v₀ * (Ks + 1) + 4 / v₀ ^ 2 * (T * E)
  let J := Jp + C * T / c + 1
  let K := W * (4 * (4 * B ^ 2 + 5 * B * A + A ^ 2 + 3 * A) + 8 * J * (1 + 2 * B))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hJ : 0 < J := by dsimp [J]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨hρ, hrates⟩ := eventually_template_rates θ T δ hθlo hθhi hT hδ n ell hk
  have hevent : ∀ᶠ N : ℕ in atTop,
      0 < N ∧ Ns ≤ N ∧ Nr ≤ N ∧
      (∀ p : Binomial.Probability, Density θ T N p →
      ∀ a : Process.Data, Process.Specification N p (responseHorizon θ) ell a →
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ η : History (n + 1) → ℤ, ∀ e : History (n + 1) → History (n + 1) → ℤ,
      FaithfulNumericalData N (p : ℝ) T δ τ a n η e →
      ∀ q : Local.Tilt n, Local.Solves (naturalSizes η) (realEdges e) q →
      ∀ u v : History (n + 2),
        |Local.templateEdges (naturalSizes η) (realEdges e) q u v -
          (a.state (n + 1)).edges u v * (1 + τ * betaScale N p (n + 1) *
          (ε (n + 1) u / ν (n + 1) u + ε (n + 1) v / ν (n + 1) v))| ≤
          K * betaScale N p (n + 1) * (N : ℝ) ^ (-tiltRate θ δ n) * (N : ℝ) ^ 2 * p) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), eventually_ge_atTop Ns,
      eventually_ge_atTop Nr, hgeometry, hparent, hmeans, hrates,
      eventually_rpow_neg_le (tiltRate θ δ n) (1 / (8 * J)) hρ (by positivity)]
      with N hN hNs' hNr' hgeom hpar hm hr hsmall
    refine ⟨hN, hNs', hNr', ?_⟩
    intro p hp a ha τ hτ hτT η e hf q hq u v
    have hNr0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hτ0 : 0 ≤ τ := (inv_pos.mpr hT0).le.trans hτ
    let r := (N : ℝ) ^ (-tiltRate θ δ n)
    let h := betaScale N (p : ℝ) (n + 1)
    let b := betaScale N (p : ℝ) n
    have hr0 : 0 ≤ r := Real.rpow_nonneg hNr0.le _
    have hh0 : 0 ≤ h := betaScale_nonneg _ _ _
    have hb0 : 0 ≤ b := betaScale_nonneg _ _ _
    obtain ⟨hr1, _, hiS, _, _, hhR, hlarge⟩ := hr p hp
    have hh1 : h ≤ 1 := hhR.trans hr1
    have hd1 : h * r ≤ 1 := by nlinarith
    have hsq : h ^ 2 ≤ h * r := by nlinarith
    have hS : 0 < Real.sqrt ((p : ℝ) * N) := Real.sqrt_pos.mpr (mul_pos p.property.1 hNr0)
    have hbhr : b ≤ h * r := by
      have hid : b = h * (1 / Real.sqrt ((p : ℝ) * N)) := by
        dsimp [b, h]
        rw [betaScale_succ]
        field_simp
      rw [hid]
      exact mul_le_mul_of_nonneg_left hiS hh0
    have hEsmall : J * b ≤ 1 / 8 := by
      have hbR : b ≤ r := hbhr.trans (by nlinarith)
      have ht := mul_le_mul_of_nonneg_left (hbR.trans hsmall) hJ.le
      have hid : J * (1 / (8 * J)) = 1 / 8 := by field_simp
      exact ht.trans_eq hid
    obtain ⟨hgeo, hedge⟩ := hgeom p hp a ha
    obtain ⟨_, hresp, hsolved⟩ := hresponse N hNr' p hp a ha τ hτ hτT η e hf
    obtain ⟨σ, hrespq, hσ, _⟩ := hsolved q hq
    have hmeanlow := fun s b t => (hm p hp a ha s b t).2.1
    have hmeanrel := child_mean_relative_uniform hN hc hC.le hT0.le hτ0 hτT
      hresp σ hσ hrespq hmeanlow
    have hevol := ha.evolution n (level_succ_lt_horizon hk)
    have hrefedge : ∀ u v, Local.templateEdges (a.state n).sizes (a.state n).edges (a.tilt n) u v =
        (a.state (n + 1)).edges u v := by intro u v; rw [hevol]; rfl
    have hrefsize : ∀ u, ((a.state (n + 1)).sizes u : ℝ) =
        (⌊Local.templateSizes (a.state n).sizes (a.tilt n) u⌋₊ : ℝ) := by
      intro u; rw [hevol]; rfl
    have hsize : ∀ w, |Local.templateSizes (naturalSizes η) q w /
        Local.templateSizes (a.state n).sizes (a.tilt n) w -
        (1 + (τ * (ε (n + 1) w / ν (n + 1) w)) * h)| ≤ A * (h * r) := by
      intro w
      have hfloor : |((a.state (n + 1)).sizes w : ℝ) -
          Local.templateSizes (a.state n).sizes (a.tilt n) w| ≤ 1 := by
        rw [hrefsize w, abs_le]
        have hl := Nat.floor_le (Process.templateSizes_nonneg (a.state n).sizes (a.tilt n) w)
        have hu := Nat.lt_floor_add_one (Local.templateSizes (a.state n).sizes (a.tilt n) w)
        constructor <;> linarith
      have hs := hsizes N hNs' p hp a ha τ hτ hτT η e hf q hq w
      rw [sizeScale_succ_eq N hN] at hs hlarge
      have hrat := size_ratio_response_uniform hNr0 hv₀ (hv w) (hgeo w).1 (hgeo w).2 hfloor
        hτ0 hh0 hr0 (by simpa [h, r, mul_assoc] using hlarge) (hε w)
        (by simpa [h, r, mul_assoc, mul_left_comm, mul_comm] using hs)
      have hcoef : 2 / v₀ * (Ks + 1) + 4 / v₀ ^ 2 * (τ * E) ≤ A := by
        dsimp [A]
        gcongr
      have ht := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hh0 hr0)
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        hrat.trans (by simpa [mul_assoc] using ht)
    have hcoef : ∀ w, |τ * (ε (n + 1) w / ν (n + 1) w)| ≤ B := by
      intro w
      rw [abs_mul, abs_of_nonneg hτ0]
      exact mul_le_mul hτT (hratio w) (abs_nonneg _) hT0.le
    have hmeans' : ∀ s bb t, |Process.childMean (naturalSizes η) q s bb t /
        Process.childMean (a.state n).sizes (a.tilt n) s bb t - 1| ≤ J * b := by
      intro s bb t
      apply (hmeanrel s bb t).trans
      apply mul_le_mul_of_nonneg_right _ hb0
      dsimp [J]
      linarith
    have hpar' : ∀ s t, |realEdges e s t / (a.state n).edges s t - 1| ≤ J * b := by
      intro s t
      apply (hpar p hp a ha τ hτ hτT η e hf s t).trans
      apply mul_le_mul_of_nonneg_right _ hb0
      dsimp [J]
      have : 0 ≤ C * T / c := by positivity
      linarith
    have hrawpos : ∀ w, 0 < Local.templateSizes (a.state n).sizes (a.tilt n) w := fun w =>
      (half_pos (mul_pos hNr0 (ν_positive (n + 1) w))).trans_le (hgeo w).1
    have hmpos : ∀ s bb t, 0 < Process.childMean (a.state n).sizes (a.tilt n) s bb t := fun s bb t =>
      (mul_pos hc (mul_pos p.property.1 hNr0)).trans_le (hmeanlow s bb t)
    have herr := templateEdges_error_of_relative_bounds (naturalSizes η) (a.state n).sizes
      (realEdges e) (a.state n).edges q (a.tilt n) u v
      (τ * (ε (n + 1) u / ν (n + 1) u)) (τ * (ε (n + 1) v / ν (n + 1) v))
      h (h * r) A B J (J * b) (W * (p : ℝ) * (N : ℝ) ^ 2)
      (hrawpos u).ne' (hrawpos v).ne'
      (hmpos (parent u) (last u) (parent v)).ne' (hmpos (parent v) (last v) (parent u)).ne'
      ((ha.solvable n (level_succ_lt_horizon hk)).edges_pos (parent u) (parent v)).ne'
      hh0 hh1 (mul_nonneg hh0 hr0) hd1 hsq hA hB (hcoef u) (hcoef v) (hsize u) (hsize v)
      (mul_nonneg hJ.le hb0) hEsmall (mul_le_mul_of_nonneg_left hbhr hJ.le)
      (hmeans' (parent u) (last u) (parent v)) (hmeans' (parent v) (last v) (parent u))
      (hpar' (parent u) (parent v)) (by rw [hrefedge]; exact hedge u v)
    rw [hrefedge] at herr
    convert herr using 1 <;> dsimp [K, h, r] <;> ring
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hevent
  refine ⟨K, hK, max 1 N₀, le_max_left _ _, ?_⟩
  intro N hN
  exact (hN₀ N ((le_max_right _ _).trans hN)).2.2.2

/-- The complete uniform edge estimate in Theorem 5.4(c), with the reference
process, solving tilt, and local template all literal. -/
theorem template_edges_spec (θ T δ : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hδ : 0 < δ) (n ell : ℕ) (hell : 1 ≤ ell)
    (hk : (n : ℝ) + 1 < 1 / (1 - θ)) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ p : Binomial.Probability, Density θ T N p →
      ∀ a : Process.Data, Process.Specification N p (responseHorizon θ) ell a →
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ η : History (n + 1) → ℤ, ∀ e : History (n + 1) → History (n + 1) → ℤ,
      FaithfulNumericalData N (p : ℝ) T δ τ a n η e →
      ∀ q : Local.Tilt n, Local.Solves (naturalSizes η) (realEdges e) q →
      ∀ u v : History (n + 2),
        |Local.templateEdges (naturalSizes η) (realEdges e) q u v -
          (a.state (n + 1)).edges u v * (1 + τ * betaScale N p (n + 1) *
          (ε (n + 1) u / ν (n + 1) u + ε (n + 1) v / ν (n + 1) v))| ≤
          K * betaScale N p (n + 1) * (N : ℝ) ^ (-tiltRate θ δ n) * (N : ℝ) ^ 2 * p := by
  obtain ⟨W, hW, hgeom⟩ := reference_template_geometry θ T δ hθlo hθhi hT hδ n ell hk
  obtain ⟨J, hJ, hpar⟩ := faithful_parent_edge_relative θ T δ hθlo hθhi hT hδ n ell hk
  exact template_edges_of_reference_bounds θ T δ hθlo hθhi hT hδ n ell hell hk W J hW hJ hgeom hpar

end MajorityDynamics.Idealized.PerturbedEvolution
