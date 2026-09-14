import MajorityDynamics.Binomial.GaussianComparisonSparse
import MajorityDynamics.Idealized.RowLimits.Approximation

/-! Sparse-range normalized moment comparisons without any balance restriction.
The exact diagonal trials, tie events, means and variances are retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped BigOperators
namespace MajorityDynamics.Idealized.RowLimits
open Binomial Binomial.Approximation Analysis.ConditionalGaussian Universal

theorem gaussian_comparison_sparse_finite {ι : Type*} [Fintype ι]
    (θ T : ℝ) (hθ : 1 / 2 < θ) (hθ' : θ < 1) (hT : 1 < T)
    (d : ℕ) (hd : 0 < d) (r : ι → ℕ)
    (M : ∀ j, Fin (r j) → Fin d → ℤ) (hM : ∀ j, OrthogonalRows (M j))
    (strict : ∀ j, Fin (r j) → Bool) (c : ι → ℝ) (e : ι → Fin d → ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ p : Probability, SparseRange θ T N p →
      ∀ η : Fin d → ℕ, Sizes T N η → ∀ α : Fin d → ℝ,
      (∀ i, |α i| < T) → ∀ j,
      |(∫ a in inequalityEvent (fun k i => (M j k i : ℝ)) (strict j),
          monomial (c j) (e j) (centered p η a) ∂Binomial.law η (gaussianTilt p η α)) -
        (∫ x in gaussianEvent (M j) p η, monomial (c j) (e j) x ∂gaussianLaw p η α)| ≤
        C * (scale N p) ^ (((∑ i, e j i : ℕ) : ℝ) - 1) *
          (Real.log N) ^ (3 + (∑ i, e j i) + d) := by
  classical
  choose C hC N₀ h using fun j =>
    gaussian_comparison_sparse θ T hθ hθ' hT d hd (r j) (M j) (hM j) (strict j) (c j) (e j)
  let C' : ℝ := 1 + ∑ j, |C j|
  have hC' : 0 < C' := by dsimp [C']; positivity
  refine ⟨C', hC', max 1 (Finset.univ.sup N₀), le_max_left _ _, ?_⟩
  intro N hN p hp η hη α hα j
  have hNj : N₀ j ≤ N :=
    (Finset.le_sup (f := N₀) (Finset.mem_univ j)).trans ((le_max_right _ _).trans hN)
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hbound := h j N hNj p hp η hη α hα
  have hCj : C j ≤ C' := by
    have hi := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => abs_nonneg (C i))
      (Finset.mem_univ j)
    dsimp [C']
    linarith [le_abs_self (C j)]
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
  apply hbound.trans
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_right hCj
    exact Real.rpow_nonneg (Real.sqrt_nonneg _) _
  · positivity


theorem normalized_gaussian_comparison_sparse_finite {ι : Type*} [Fintype ι]
    (θ T : ℝ) (hθ : 1 / 2 < θ) (hθ' : θ < 1) (hT : 1 < T)
    (d : ℕ) (hd : 0 < d) (r : ι → ℕ)
    (M : ∀ j, Fin (r j) → Fin d → ℤ) (hM : ∀ j, OrthogonalRows (M j))
    (strict : ∀ j, Fin (r j) → Bool) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ p : Probability, SparseRange θ T N p →
      ∀ η : Fin d → ℕ, Sizes T N η → ∀ σ ν : Fin d → ℝ,
      (∀ i, |σ i / ν i * Real.sqrt ((η i : ℝ) / N)| < T) → ∀ j,
      ∀ o : MomentKind d,
      |(∫ a in inequalityEvent (fun k i => (M j k i : ℝ)) (strict j),
          momentValue o (fun i => centered p η a i / scale N p)
          ∂Binomial.law η (gaussianTilt p η
            (fun i => σ i / ν i * Real.sqrt ((η i : ℝ) / N)))) -
        (∫ x in Analysis.GaussianRegularity.event (fun k i => (M j k i : ℝ))
          (WithLp.toLp 2 (fun k => (p : ℝ) * (∑ i, (M j k i : ℝ) * η i) / scale N p)),
          momentValue o x.ofLp ∂Analysis.ConditionalGaussian.gaussianLaw
            (Matrix.diagonal (fun i => (η i : ℝ) / N))
            (WithLp.toLp 2 (fun i => σ i * η i / ((N : ℝ) * ν i))))| ≤
        C * (Real.log N) ^ (3 + (∑ i, momentExponent o i) + d) / scale N p := by
  classical
  obtain ⟨C, hC, N₀, hN₀, h⟩ := gaussian_comparison_sparse_finite (ι := ι × MomentKind d)
    θ T hθ hθ' hT d hd (fun j => r j.1) (fun j => M j.1)
    (fun j => hM j.1) (fun j => strict j.1) (fun _ => 1)
    (fun j => momentExponent j.2)
  refine ⟨C, hC, N₀, hN₀, ?_⟩
  intro N hN p hp η hη σ ν hα j o
  have hn : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (hN₀.trans hN)
  have ha : 0 < scale N p := Real.sqrt_pos.mpr
    (mul_pos p.property.1 (Nat.cast_pos.mpr hn))
  have hb := h N hN p hp η hη
    (fun i => σ i / ν i * Real.sqrt ((η i : ℝ) / N)) hα (j, o)
  have hc := normalized_monomial_comparison
    (Binomial.law η (gaussianTilt p η
      (fun i => σ i / ν i * Real.sqrt ((η i : ℝ) / N))))
    (Binomial.Approximation.gaussianLaw p η
      (fun i => σ i / ν i * Real.sqrt ((η i : ℝ) / N)))
    (inequalityEvent (fun k i => (M j k i : ℝ)) (strict j))
    (gaussianEvent (M j) p η) (centered p η) id 1 (momentExponent o)
    (scale N p) C ((Real.log N) ^ (3 + (∑ i, momentExponent o i) + d)) ha hb
  simp only [moment_monomial] at hc
  rw [gaussianEvent_normalized N hn p η (M j)] at hc
  have he := (setIntegral_map_equiv
    (μ := Binomial.Approximation.gaussianLaw p η
      (fun i => σ i / ν i * Real.sqrt ((η i : ℝ) / N)))
    (normalizeEquiv (scale N p) ha.ne')
    (fun x => momentValue o x.ofLp)
    (Analysis.GaussianRegularity.event (fun k i => (M j k i : ℝ))
      (WithLp.toLp 2 (fun k => (p : ℝ) * (∑ i, (M j k i : ℝ) * η i) / scale N p)))).symm
  change (∫ x in normalize (scale N p) ⁻¹' _,
    momentValue o (fun i => x i / scale N p) ∂_) =
    ∫ y in _, momentValue o y.ofLp ∂Measure.map (normalize (scale N p)) _ at he
  rw [show scale N p = Real.sqrt ((p : ℝ) * N) from rfl,
    map_normalize_row p N hn η σ ν] at he
  change _ = _ at he
  simp only [id_eq, scale] at hc ⊢
  rw [he] at hc
  exact hc


end MajorityDynamics.Idealized.RowLimits

