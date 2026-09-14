import MajorityDynamics.Idealized.PerturbedEvolution.TemplateSizes
import MajorityDynamics.Idealized.PerturbedTilt.SparseAssembly
import MajorityDynamics.Idealized.PerturbedTilt.SparseAdmissibilityEdges
import MajorityDynamics.Idealized.PerturbedEvolution.SparseTemplateRates

noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators
namespace MajorityDynamics.Idealized.PerturbedEvolution
open Universal LinearResponse PerturbedTilt RowLimits
open Binomial.Approximation (SparseRange scale)
set_option maxHeartbeats 3000000

theorem template_sizes_spec_sparse (θ T δ : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hδ : 0 < δ) (n ell : ℕ) (hell : 1 ≤ ell)
    (D : ℕ) (hDlt : n + 1 < D) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ p : Binomial.Probability, SparseRange θ T N p → ResponseSmall θ N p n →
      ∀ a : Process.Data, Process.Specification N p D ell a →
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ η : History (n + 1) → ℤ, ∀ e : History (n + 1) → History (n + 1) → ℤ,
      FaithfulNumericalData N (p : ℝ) T δ τ a n η e →
      ∀ q : Local.Tilt n, Local.Solves (naturalSizes η) (realEdges e) q →
      ∀ u : History (n + 2),
        |Local.templateSizes (naturalSizes η) q u - ((a.state (n + 1)).sizes u : ℝ) -
          τ * sizeScale N p (n + 1) * ε (n + 1) u| ≤
            K * sizeScale N p (n + 1) * (N : ℝ) ^ (-sparseTiltRate θ δ) := by
  classical
  have hT0 : 0 < T := by linarith
  obtain ⟨T₀, _, R, _, C, hC, B, hB, Nr, hNr, hresponse⟩ :=
    perturbed_tilt_response_spec_sparse θ T δ hθlo hθhi hT hδ n ell hell D hDlt
  obtain ⟨K₀, hK₀, href⟩ := reference_coordinates_sparse θ T hθlo hθhi hT n ell
  let A := comparisonConstant n T
  have hA : 0 ≤ A := (by positivity : 0 ≤ T).trans (comparisonConstant_ge n hT0.le)
  let G := fun sb : History (n + 1) × Bool =>
    |ν (n + 1) (append sb.1 sb.2) / ν n sb.1| *
      ∑ t, |(∫ x, x t ∂childLaw n sb.1 sb.2) - (∫ x, x t ∂historyLaw n sb.1)|
  obtain ⟨G₀, hG₀, hG⟩ := finite_abs_bound G
  obtain ⟨V, hV, hνV⟩ := finite_abs_bound (ν n)
  obtain ⟨E, hE, hεE⟩ := finite_abs_bound
    (fun sb : History (n + 1) × Bool => ε (n + 1) (append sb.1 sb.2) / ν n sb.1)
  let X := V + K₀ + A
  let L := C + G₀ * B
  let K := A + X * T * L + (K₀ + A) * T * E + 1
  have hX : 0 ≤ X := by dsimp [X]; linarith
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨_, hrates⟩ := eventually_template_rates_sparse θ T δ hθlo hθhi hT hδ n ell
  have hevent : ∀ᶠ N : ℕ in atTop, (0 < N) ∧ Nr ≤ N ∧
      (∀ p : Binomial.Probability, SparseRange θ T N p → ResponseSmall θ N p n →
      ∀ a : Process.Data, Process.Specification N p D ell a →
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ η : History (n + 1) → ℤ, ∀ e : History (n + 1) → History (n + 1) → ℤ,
      FaithfulNumericalData N (p : ℝ) T δ τ a n η e →
      ∀ q : Local.Tilt n, Local.Solves (naturalSizes η) (realEdges e) q →
      ∀ u : History (n + 2),
        |Local.templateSizes (naturalSizes η) q u - ((a.state (n + 1)).sizes u : ℝ) -
          τ * sizeScale N p (n + 1) * ε (n + 1) u| ≤
            K * sizeScale N p (n + 1) * (N : ℝ) ^ (-sparseTiltRate θ δ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), eventually_ge_atTop Nr,
      faithful_geometry_sparse θ T δ hθlo hθhi hT hδ n ell D hDlt, href, hrates]
      with N hN hNrN hgeo hrefN hrateN
    refine ⟨hN, hNrN, ?_⟩
    intro p hp hsub a ha τ hτ hτT η e hf q hq u
    have hp0 := p.property.1
    have hNr0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hτ0 : 0 < τ := (inv_pos.mpr hT0).trans_le hτ
    obtain ⟨htilt, hresp, hsolve⟩ := hresponse N hNrN p hp hsub a ha τ hτ hτT η e hf
    obtain ⟨σ, hσq, hσR, hσβ⟩ := hsolve q hq
    obtain ⟨_, hcast, hclose, _⟩ := hgeo p hp hsub a ha τ hτ hτT η e hf
    obtain ⟨hrefsize, _⟩ := hrefN p hp hsub (a.state n)
      (ha.estimates n (Nat.lt_of_succ_lt hDlt))
    obtain ⟨hr1, hrκ, hinv, _, hβr, _, hfloor⟩ := hrateN p hp hsub
    let r := (N : ℝ) ^ (-sparseTiltRate θ δ)
    let b₀ := betaScale N p n
    let b₁ := betaScale N p (n + 1)
    have hr : 0 ≤ r := Real.rpow_nonneg hNr0.le _
    have hb₀ : 0 ≤ b₀ := betaScale_nonneg _ _ _
    have hb₁ : 0 < b₁ := by dsimp [b₁, betaScale]; positivity
    have hS : 0 < scale N p := by dsimp [scale]; positivity
    have hbcompare : b₀ ≤ b₁ * r := by
      have hid : b₀ = b₁ * (1 / scale N p) := by
        dsimp [b₀, b₁]
        rw [betaScale_succ]
        change betaScale N p n = betaScale N p n * scale N p * (1 / scale N p)
        field_simp
      rw [hid]
      exact mul_le_mul_of_nonneg_left hinv hb₁.le
    let s := parent u
    let b := last u
    have hu : append s b = u := append_parent_last u
    let x := ((naturalSizes η s : ℕ) : ℝ)
    let x₀ := ((a.state n).sizes s : ℝ)
    have hx : 0 ≤ x := Nat.cast_nonneg _
    have hparent : |x - x₀| ≤ A * (N : ℝ) * b₀ := by
      simpa only [x, x₀, hcast s, sizeScale_eq N hN, A, b₀, mul_comm, mul_left_comm,
        mul_assoc] using hclose s
    have hrefsize' : |x₀ - (N : ℝ) * ν n s| ≤ K₀ * (N : ℝ) * r := by
      have h0 := (hrefsize s).trans (mul_le_mul_of_nonneg_left hrκ (by linarith : 0 ≤ K₀))
      have hid : x₀ - (N : ℝ) * ν n s = (x₀ / N - ν n s) * N := by field_simp
      rw [hid, abs_mul, abs_of_pos hNr0]
      simpa only [mul_assoc, mul_comm, mul_left_comm, r, x₀] using
        mul_le_mul_of_nonneg_right h0 hNr0.le
    have hsize : |x - (N : ℝ) * ν n s| ≤ (K₀ + A) * (N : ℝ) * r := by
      have h0 := (abs_sub_le x x₀ ((N : ℝ) * ν n s)).trans (add_le_add hparent hrefsize')
      have h1 := mul_le_mul_of_nonneg_left hβr (mul_nonneg hA hNr0.le)
      change A * (N : ℝ) * b₀ ≤ A * (N : ℝ) * r at h1
      linarith only [h0, h1]
    have hxU : x ≤ X * (N : ℝ) := by
      have h0 := (abs_le.mp hsize).2
      have h1 := mul_le_mul_of_nonneg_left hr1
        (show 0 ≤ (K₀ + A) * (N : ℝ) by positivity)
      have h2 := mul_le_mul_of_nonneg_left ((le_abs_self (ν n s)).trans (hνV s)) hNr0.le
      dsimp [X]
      nlinarith only [h0, h1, h2]
    have hgauss : |gaussianSplitResponse n s b (σ s) - ε (n + 1) (append s b) / ν n s| ≤
        G₀ * B * r := by
      have h0 := gaussianSplitResponse_error s b (σ s) (WithLp.toLp 2 (β n s)) (hσβ s)
      rw [gaussianSplitResponse_beta] at h0
      have h1 : G (s, b) ≤ G₀ := (le_abs_self _).trans (hG (s, b))
      exact h0.trans (by simpa [G, r, mul_assoc] using
        mul_le_mul_of_nonneg_right h1 (mul_nonneg hB.le hr))
    have hnormalized := (hresp s).split_response (σ s) (hσR s) b
    rw [← hσq s] at hnormalized
    have hnormalized' : |(splitProbability (naturalSizes η) s b (q s) -
        splitProbability (a.state n).sizes s b (a.tilt n s)) / (τ * b₁) -
        gaussianSplitResponse n s b (σ s)| ≤ C * r := by
      have hid : τ * betaScale N p n * Real.sqrt ((p : ℝ) * N) = τ * b₁ := by
        dsimp [b₁]; rw [betaScale_succ]; ring
      rw [hid] at hnormalized
      exact hnormalized.trans (mul_le_mul_of_nonneg_left hrκ hC.le)
    have hsplit := split_response_error (mul_pos hτ0 hb₁) hnormalized' hgauss
    have hsplit' : |Local.splitProbability (naturalSizes η) q s b -
        Local.splitProbability (a.state n).sizes (a.tilt n) s b -
        τ * b₁ * (ε (n + 1) (append s b) / ν n s)| ≤ T * b₁ * L * r := by
      have h0 : τ * b₁ * (C * r + G₀ * B * r) ≤ T * b₁ * L * r := by
        dsimp [L]
        nlinarith only [mul_le_mul_of_nonneg_right hτT (mul_nonneg hb₁.le
          (show 0 ≤ (C + G₀ * B) * r by positivity))]
      exact hsplit.trans h0
    have hP₀ := reference_split_abs_le_one (a.state n).sizes (a.tilt n) s b
      ((ha.solvable n hDlt).conditioning_pos s)
    have hprop := size_propagation_error hx (ν_positive n s).ne' hP₀ hparent hsize hsplit'
    have hε : |τ * b₁ * (ε (n + 1) (append s b) / ν n s)| ≤ T * b₁ * E := by
      rw [abs_mul, abs_mul, abs_of_pos hτ0, abs_of_pos hb₁]
      exact mul_le_mul (mul_le_mul_of_nonneg_right hτT hb₁.le) (hεE (s, b))
        (abs_nonneg _) (by positivity)
    have hbound : |x * Local.splitProbability (naturalSizes η) q s b -
        x₀ * Local.splitProbability (a.state n).sizes (a.tilt n) s b -
        τ * b₁ * (N : ℝ) * ε (n + 1) (append s b)| ≤
        (K - 1) * sizeScale N p (n + 1) * r := by
      apply hprop.trans
      have h1 := mul_le_mul_of_nonneg_left hbcompare (mul_nonneg hA hNr0.le)
      have h2 := mul_le_mul_of_nonneg_right hxU (show 0 ≤ T * b₁ * L * r by positivity)
      have h3 := mul_le_mul_of_nonneg_left hε
        (show 0 ≤ (K₀ + A) * (N : ℝ) * r by positivity)
      rw [sizeScale_succ_eq N hN]
      dsimp only [K]
      nlinarith only [h1, h2, h3]
    have hraw : |Local.templateSizes (naturalSizes η) q u -
        Local.templateSizes (a.state n).sizes (a.tilt n) u -
        τ * sizeScale N p (n + 1) * ε (n + 1) u| ≤
        (K - 1) * sizeScale N p (n + 1) * r := by
      simpa only [Local.templateSizes, x, x₀, s, b, hu, sizeScale_succ_eq N hN,
        b₁, mul_assoc, mul_comm, mul_left_comm] using hbound
    have hrounded := size_error_floor
      (Process.templateSizes_nonneg (a.state n).sizes (a.tilt n) u) hraw
    have hevol : ((a.state (n + 1)).sizes u : ℝ) =
        (⌊Local.templateSizes (a.state n).sizes (a.tilt n) u⌋₊ : ℝ) := by
      rw [ha.evolution n hDlt]
      rfl
    rw [hevol]
    exact hrounded.trans (by dsimp [r] at *; nlinarith only [hfloor])
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hevent
  refine ⟨K, hK, max 1 N₀, le_max_left _ _, ?_⟩
  intro N hN
  exact (hN₀ N ((le_max_right _ _).trans hN)).2.2

end MajorityDynamics.Idealized.PerturbedEvolution

