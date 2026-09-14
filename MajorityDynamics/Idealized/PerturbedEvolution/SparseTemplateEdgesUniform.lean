import MajorityDynamics.Idealized.PerturbedEvolution.TemplateEdgesUniform
import MajorityDynamics.Idealized.PerturbedTilt.SparseAssembly
import MajorityDynamics.Idealized.PerturbedTilt.SparseAdmissibilityEdges
import MajorityDynamics.Idealized.PerturbedEvolution.SparseTemplateSizes
import MajorityDynamics.Idealized.PerturbedEvolution.SparseReferenceMeans
import MajorityDynamics.Idealized.PerturbedEvolution.SparseTemplateParentEdges
import MajorityDynamics.Idealized.PerturbedEvolution.SparseTemplateReference

noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators
namespace MajorityDynamics.Idealized.PerturbedEvolution
open Universal LinearResponse PerturbedTilt RowLimits
open Binomial.Approximation (SparseRange scale)
set_option maxHeartbeats 3000000

theorem template_edges_of_reference_bounds_sparse (θ T δ : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hδ : 0 < δ)
    (n ell : ℕ) (hell : 1 ≤ ell) (D : ℕ) (hDlt : n + 1 < D)
    (W Jp : ℝ) (hW : 0 < W) (hJp : 0 < Jp)
    (hgeometry : ∀ᶠ N : ℕ in atTop,
      ∀ p : Binomial.Probability, SparseRange θ T N p → ResponseSmall θ N p n →
      ∀ a : Process.Data, Process.Specification N p D ell a →
      (∀ u, (N : ℝ) * ν (n + 1) u / 2 ≤ Local.templateSizes (a.state n).sizes (a.tilt n) u ∧
        |Local.templateSizes (a.state n).sizes (a.tilt n) u - N * ν (n + 1) u| ≤
          2 * N * (N : ℝ) ^ (-sparseTiltRate θ δ)) ∧
      (∀ u v, |(a.state (n + 1)).edges u v| ≤ W * (p : ℝ) * (N : ℝ) ^ 2))
    (hparent : ∀ᶠ N : ℕ in atTop,
      ∀ p : Binomial.Probability, SparseRange θ T N p → ResponseSmall θ N p n →
      ∀ a : Process.Data, Process.Specification N p D ell a →
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ η : History (n + 1) → ℤ, ∀ e : History (n + 1) → History (n + 1) → ℤ,
      FaithfulNumericalData N (p : ℝ) T δ τ a n η e →
      ∀ s t, |(e s t : ℝ) / (a.state n).edges s t - 1| ≤ Jp * betaScale N p n) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ p : Binomial.Probability, SparseRange θ T N p → ResponseSmall θ N p n →
      ∀ a : Process.Data, Process.Specification N p D ell a →
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ η : History (n + 1) → ℤ, ∀ e : History (n + 1) → History (n + 1) → ℤ,
      FaithfulNumericalData N (p : ℝ) T δ τ a n η e →
      ∀ q : Local.Tilt n, Local.Solves (naturalSizes η) (realEdges e) q →
      ∀ u v : History (n + 2),
        |Local.templateEdges (naturalSizes η) (realEdges e) q u v -
          (a.state (n + 1)).edges u v * (1 + τ * betaScale N p (n + 1) *
          (ε (n + 1) u / ν (n + 1) u + ε (n + 1) v / ν (n + 1) v))| ≤
          K * betaScale N p (n + 1) * (N : ℝ) ^ (-sparseTiltRate θ δ) * (N : ℝ) ^ 2 * p := by
  classical
  have hT0 : 0 < T := by linarith
  obtain ⟨Ks, hKs, Ns, hNs, hsizes⟩ := template_sizes_spec_sparse θ T δ hθlo hθhi hT hδ n ell hell D hDlt
  obtain ⟨T₀, _, R, _, C, hC, B₀, _, Nr, hNr, hresponse⟩ :=
    perturbed_tilt_response_spec_sparse θ T δ hθlo hθhi hT hδ n ell hell D hDlt
  obtain ⟨Km, _, c, hc, hmeans⟩ := reference_child_mean_bounds_sparse θ T hθlo hθhi hT n ell hell D hDlt
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
  obtain ⟨hρ, hrates⟩ := eventually_template_rates_sparse θ T δ hθlo hθhi hT hδ n ell
  have hevent : ∀ᶠ N : ℕ in atTop,
      0 < N ∧ Ns ≤ N ∧ Nr ≤ N ∧
      (∀ p : Binomial.Probability, SparseRange θ T N p → ResponseSmall θ N p n →
      ∀ a : Process.Data, Process.Specification N p D ell a →
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ η : History (n + 1) → ℤ, ∀ e : History (n + 1) → History (n + 1) → ℤ,
      FaithfulNumericalData N (p : ℝ) T δ τ a n η e →
      ∀ q : Local.Tilt n, Local.Solves (naturalSizes η) (realEdges e) q →
      ∀ u v : History (n + 2),
        |Local.templateEdges (naturalSizes η) (realEdges e) q u v -
          (a.state (n + 1)).edges u v * (1 + τ * betaScale N p (n + 1) *
          (ε (n + 1) u / ν (n + 1) u + ε (n + 1) v / ν (n + 1) v))| ≤
          K * betaScale N p (n + 1) * (N : ℝ) ^ (-sparseTiltRate θ δ) * (N : ℝ) ^ 2 * p) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), eventually_ge_atTop Ns,
      eventually_ge_atTop Nr, hgeometry, hparent, hmeans, hrates,
      eventually_rpow_neg_le (sparseTiltRate θ δ) (1 / (8 * J)) hρ (by positivity)]
      with N hN hNs' hNr' hgeom hpar hm hr hsmall
    refine ⟨hN, hNs', hNr', ?_⟩
    intro p hp hsub a ha τ hτ hτT η e hf q hq u v
    have hNr0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hτ0 : 0 ≤ τ := (inv_pos.mpr hT0).le.trans hτ
    let r := (N : ℝ) ^ (-sparseTiltRate θ δ)
    let h := betaScale N (p : ℝ) (n + 1)
    let b := betaScale N (p : ℝ) n
    have hr0 : 0 ≤ r := Real.rpow_nonneg hNr0.le _
    have hh0 : 0 ≤ h := betaScale_nonneg _ _ _
    have hb0 : 0 ≤ b := betaScale_nonneg _ _ _
    obtain ⟨hr1, _, hiS, _, _, hhR, hlarge⟩ := hr p hp hsub
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
    obtain ⟨hgeo, hedge⟩ := hgeom p hp hsub a ha
    obtain ⟨_, hresp, hsolved⟩ := hresponse N hNr' p hp hsub a ha τ hτ hτT η e hf
    obtain ⟨σ, hrespq, hσ, _⟩ := hsolved q hq
    have hmeanlow := fun s b t => (hm p hp hsub a ha s b t).2.1
    have hmeanrel := child_mean_relative_uniform hN hc hC.le hT0.le hτ0 hτT
      hresp σ hσ hrespq hmeanlow
    have hevol := ha.evolution n hDlt
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
      have hs := hsizes N hNs' p hp hsub a ha τ hτ hτT η e hf q hq w
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
      apply (hpar p hp hsub a ha τ hτ hτT η e hf s t).trans
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
      ((ha.solvable n hDlt).edges_pos (parent u) (parent v)).ne'
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

theorem template_edges_spec_sparse (θ T δ : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hδ : 0 < δ) (n ell : ℕ) (hell : 1 ≤ ell)
    (D : ℕ) (hDlt : n + 1 < D) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ p : Binomial.Probability, SparseRange θ T N p → ResponseSmall θ N p n →
      ∀ a : Process.Data, Process.Specification N p D ell a →
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ η : History (n + 1) → ℤ, ∀ e : History (n + 1) → History (n + 1) → ℤ,
      FaithfulNumericalData N (p : ℝ) T δ τ a n η e →
      ∀ q : Local.Tilt n, Local.Solves (naturalSizes η) (realEdges e) q →
      ∀ u v : History (n + 2),
        |Local.templateEdges (naturalSizes η) (realEdges e) q u v -
          (a.state (n + 1)).edges u v * (1 + τ * betaScale N p (n + 1) *
          (ε (n + 1) u / ν (n + 1) u + ε (n + 1) v / ν (n + 1) v))| ≤
          K * betaScale N p (n + 1) * (N : ℝ) ^ (-sparseTiltRate θ δ) * (N : ℝ) ^ 2 * p := by
  obtain ⟨W, hW, hgeom⟩ := reference_template_geometry_sparse θ T δ hθlo hθhi hT hδ n ell D hDlt
  obtain ⟨J, hJ, hpar⟩ := faithful_parent_edge_relative_sparse θ T δ hθlo hθhi hT hδ n ell D hDlt
  exact template_edges_of_reference_bounds_sparse θ T δ hθlo hθhi hT hδ n ell hell D hDlt W J hW hJ hgeom hpar

end MajorityDynamics.Idealized.PerturbedEvolution

