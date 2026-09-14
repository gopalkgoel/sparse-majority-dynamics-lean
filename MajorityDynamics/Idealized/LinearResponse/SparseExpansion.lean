import MajorityDynamics.Idealized.LinearResponse.Expansion
import MajorityDynamics.Binomial.TiltedExpansionSparse
noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators
namespace MajorityDynamics.Idealized.LinearResponse
open Universal Process RowLimits Binomial.Approximation
variable {n : ℕ}
theorem tilted_expansion_finite_sparse {ι : Type*} [Fintype ι] (θ T : ℝ) (hθ : 1 / 2 < θ)
    (hθ' : θ < 1) (hT : 1 < T) (d : ℕ) (hd : 0 < d) (r : ι → ℕ)
    (M : ∀ j, Fin (r j) → Fin d → ℝ) (strict : ∀ j, Fin (r j) → Bool)
    (e : ι → Fin d → ℕ) (k : ι → ℕ) (hk : ∀ j, ∑ i, e j i = k j) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ p : Binomial.Probability, SparseRange θ T N p →
      ∀ ref old new : Fin d → ℕ, Sizes T N ref → (∀ i, 0 < old i ∧ 0 < new i) →
      (∀ i, |(old i : ℝ) - ref i| < T * N / scale N p ∧
        |(new i : ℝ) - ref i| < T * N / scale N p) →
      ∀ q₀ q₁ : Fin d → Binomial.Probability,
      (∀ i, |(q₀ i : ℝ) - p| < T * (p : ℝ) / scale N p ∧
        |(q₁ i : ℝ) - p| < T * (p : ℝ) / scale N p) →
      ‖tiltDifference p ref old new q₀ q₁‖ < T / (scale N p * (Real.log N) ^ 2) → ∀ j,
      |moment (M j) (strict j) p ref new q₁ (monomial 1 (e j)) -
          moment (M j) (strict j) p ref old q₀ (monomial 1 (e j)) -
          (∑ i, tiltDifference p ref old new q₀ q₁ i *
            moment (M j) (strict j) p ref old q₀ (fun x => x i * monomial 1 (e j) x)) +
          (∑ i, tiltDifference p ref old new q₀ q₁ i *
            (∫ a, centered p ref a i ∂Binomial.law old q₀) *
            moment (M j) (strict j) p ref old q₀ (monomial 1 (e j)))| ≤
        C * max (p : ℝ) (‖tiltDifference p ref old new q₀ q₁‖ ^ 2 * ((p : ℝ) * N) *
          (Real.log N) ^ 2) * (scale N p) ^ (k j) * (Real.log N) ^ (2 + k j) := by
  classical
  choose C hC N₀ h using fun j =>
    tilted_expansion_sparse θ T hθ hθ' hT d hd (r j) (M j) (strict j) 1 (e j)
  refine ⟨1 + ∑ j, |C j|, by positivity, max 1 (Finset.univ.sup N₀), le_max_left _ _, ?_⟩
  intro N hN p hp ref old new href hpos htr q₀ q₁ hq hβ j
  have hNj : N₀ j ≤ N :=
    (Finset.le_sup (f := N₀) (Finset.mem_univ j)).trans ((le_max_right _ _).trans hN)
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hb := h j N hNj p hp ref old new href hpos htr q₀ q₁ hq hβ
  dsimp only at hb
  rw [hk j] at hb
  have hCj : C j ≤ 1 + ∑ j, |C j| := by
    have hi := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => abs_nonneg (C i))
      (Finset.mem_univ j)
    linarith [le_abs_self (C j)]
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
  have hmax : 0 ≤ max (p : ℝ) (‖tiltDifference p ref old new q₀ q₁‖ ^ 2 * ((p : ℝ) * N) *
      (Real.log N) ^ 2) := le_max_of_le_left p.property.1.le
  refine hb.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hlog _)
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (Real.sqrt_nonneg _) _)
  exact mul_le_mul_of_nonneg_right hCj hmax

theorem row_expansions_sparse (θ T : ℝ) (hθ : 1 / 2 < θ) (hθ' : θ < 1) (hT : 1 < T) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ p : Binomial.Probability, SparseRange θ T N p →
      ∀ ref sizes : Local.Sizes n, Sizes T N ref → ∀ s : History (n + 1),
      (∀ t, 0 < Local.trials ref s t ∧ 0 < Local.trials sizes s t) →
      (∀ t, |(Local.trials ref s t : ℝ) - ref t| < T * N / scale N p ∧
        |(Local.trials sizes s t : ℝ) - ref t| < T * N / scale N p) →
      ∀ q₀ q₁ : History (n + 1) → Binomial.Probability,
      (∀ t, |(q₀ t : ℝ) - p| < T * (p : ℝ) / scale N p ∧
        |(q₁ t : ℝ) - p| < T * (p : ℝ) / scale N p) →
      ‖tiltDifference p ref (Local.trials ref s) (Local.trials sizes s) q₀ q₁‖ <
        T / (scale N p * (Real.log N) ^ 2) →
      RowExpansions N p ref sizes s q₀ q₁ (tiltDifference p ref (Local.trials ref s)
        (Local.trials sizes s) q₀ q₁)
        (C * max (p : ℝ) (‖tiltDifference p ref (Local.trials ref s) (Local.trials sizes s) q₀ q₁‖ ^ 2 *
          ((p : ℝ) * N) * (Real.log N) ^ 2) * (Real.log N) ^ 2)
        (C * max (p : ℝ) (‖tiltDifference p ref (Local.trials ref s) (Local.trials sizes s) q₀ q₁‖ ^ 2 *
          ((p : ℝ) * N) * (Real.log N) ^ 2) * scale N p * (Real.log N) ^ 3) := by
  classical
  obtain ⟨C, hC, N₀, hN₀, h⟩ := tilted_expansion_finite_sparse (ι := ExpansionIndex n) θ T hθ hθ' hT
    (Fintype.card (Fin (n + 1) → Bool)) Fintype.card_pos
    (fun j => RowLimits.eventRows n j.2.1) (fun j => eventMatrix j.1 j.2.1)
    (fun j => eventStrict j.1 j.2.1) (fun j => momentExponent j.2.2)
    (fun j => match j.2.2 with
      | Sum.inl _ => 0
      | Sum.inr (Sum.inl _) => 1
      | Sum.inr (Sum.inr _) => 2)
    (fun j => by
      rcases j with ⟨s, b, o⟩
      rcases o with _ | (i | ⟨i, j⟩)
      · exact degree_kind0
      · exact degree_kind1 i
      · simp [momentExponent, Finset.sum_add_distrib])
  refine ⟨C, hC, N₀, hN₀, ?_⟩
  intro N hN p hp ref sizes href s hpos htr q₀ q₁ hq hβ
  have hb (b : Option Bool) (o : MomentKind (Fintype.card (Fin (n + 1) → Bool))) :=
    h N hN p hp ref (Local.trials ref s) (Local.trials sizes s) href hpos htr q₀ q₁ hq hβ (s, b, o)
  have hS₀ (b : Option Bool) := eventSupport_filter ref s b
  have hS₁ (b : Option Bool) := eventSupport_filter sizes s b
  constructor
  · intro b
    have hb0 := hb b (Sum.inl ())
    dsimp only at hb0
    rw [moment_kind0_eq q₁ p ref _ _ _ (hS₁ b), moment_kind0_eq q₀ p ref _ _ _ (hS₀ b)] at hb0
    simp only [moment_kind0_first_eq q₀ p ref _ _ _ (hS₀ b)] at hb0
    exact hb0.trans (le_of_eq (by ring))
  · intro b t
    have hb1 := hb b (Sum.inr (Sum.inl t))
    dsimp only at hb1
    rw [moment_kind1_eq q₁ p ref _ _ _ (hS₁ b), moment_kind1_eq q₀ p ref _ _ _ (hS₀ b)] at hb1
    simp only [moment_kind1_first_eq q₀ p ref _ _ _ (hS₀ b)] at hb1
    exact hb1.trans (le_of_eq (by ring))

end MajorityDynamics.Idealized.LinearResponse
