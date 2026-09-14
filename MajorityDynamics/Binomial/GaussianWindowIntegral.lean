import MajorityDynamics.Binomial.GaussianWindowGeometry

/-! # From normalized Gaussian cell expectations to the full target integral -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace MajorityDynamics.Binomial.Approximation
variable {d r : ℕ}

theorem gaussian_window_integral_error (M : Fin r → Fin d → ℤ) (strict : Fin r → Bool)
    (p : Probability) (η : Fin d → ℕ) (α : Fin d → ℝ) (c : ℝ) (e : Fin d → ℕ)
    (L : ℝ) (hL : 0 ≤ L) (hpos : 0 < (gaussianLaw p η α).real (gaussianCellWindow p η L)) :
    let S := rectangleWindow (fun i => (p : ℝ) * η i) (fun _ => L)
    let f := restrictedObservable (fun j i => (M j i : ℝ)) strict p η (monomial c e)
    let H := |c| * (L + 1) ^ (∑ i, e i)
    |(∫ x in gaussianEvent M p η, monomial c e x ∂gaussianLaw p η α) -
      gaussianCellExpectation p η α S f| ≤
      |c| * (∑ i, (e i : ℝ)) * (L + 1) ^ (∑ i, e i) / (L + 1) +
      2 * H * (gaussianLaw p η α).real (gaussianBoundary M p η) +
      Real.sqrt (∫ x, monomial c e x ^ 2 ∂gaussianLaw p η α) *
        Real.sqrt ((gaussianLaw p η α).real (gaussianCellWindow p η L)ᶜ) +
      H * (gaussianLaw p η α).real (gaussianCellWindow p η L)ᶜ := by
  classical
  dsimp only
  let S := rectangleWindow (fun i => (p : ℝ) * η i) (fun _ => L)
  let f := restrictedObservable (fun j i => (M j i : ℝ)) strict p η (monomial c e)
  let F := gaussianRestrictedObservable M p η c e
  have hR : 0 < L + 1 := by linarith
  have hbound (a : Fin d → ℕ) (ha : a ∈ S) : ∀ i, |centered p η a i| ≤ L + 1 := by
    intro i
    exact ((mem_rectangleWindow _ _ _).mp ha i).trans (by linarith)
  have h := Analysis.normalized_cell_integral_error (gaussianLaw p η α) S (gaussianCell p η)
    (fun a _ => gaussianCell_measurable p η a)
    (fun a _ b _ hab => gaussianCell_disjoint p η a b hab) hpos f (|c| * (L + 1) ^ (∑ i, e i))
    (fun a ha => restrictedObservable_abs_le (fun j i => (M j i : ℝ)) strict p η c e (L + 1) hR.le a (hbound a ha))
    F (integrable_gaussianRestrictedObservable M p η α c e) (gaussianBoundary M p η)
    (gaussianBoundary_measurable M p η) (|c| * (∑ i, (e i : ℝ)) * (L + 1) ^ (∑ i, e i) / (L + 1))
    (2 * (|c| * (L + 1) ^ (∑ i, e i))) (by positivity) (by positivity) (by
      intro a ha x hx
      apply gaussian_cell_observable_error M strict p η a x c e (L + 1) hR (hbound a ha) _ hx
      exact gaussianCellWindow_coordinate_bound p η L (Set.mem_iUnion₂.mpr ⟨a, ha, hx⟩))
  have htail := Analysis.tail_moment_sqrt (gaussianLaw p η α) (monomial c e)
    (memLp_gaussian_monomial p η α c e) (gaussianCellWindow p η L)ᶜ (gaussianCellWindow_measurable p η L).compl
  have hFtail : (∫ x in (gaussianCellWindow p η L)ᶜ, |F x| ∂gaussianLaw p η α) ≤
      ∫ x in (gaussianCellWindow p η L)ᶜ, |monomial c e x| ∂gaussianLaw p η α := by
    apply integral_mono (integrable_gaussianRestrictedObservable M p η α c e).abs.integrableOn
      (integrable_gaussian_monomial p η α c e).abs.integrableOn
    intro x
    change |(gaussianEvent M p η).indicator (monomial c e) x| ≤ |monomial c e x|
    by_cases hx : x ∈ gaussianEvent M p η <;> simp [hx]
  have hnorm : Analysis.normalizedCellExpectation (gaussianLaw p η α) S (gaussianCell p η) f =
      gaussianCellExpectation p η α S f := rfl
  rw [hnorm] at h
  have hFint : (∫ x, F x ∂gaussianLaw p η α) = ∫ x in gaussianEvent M p η, monomial c e x ∂gaussianLaw p η α :=
    integral_indicator (gaussianEvent_measurable M p η)
  rw [hFint] at h
  have hft := hFtail.trans htail
  dsimp only [gaussianCellWindow, S, f] at h hft ⊢
  linarith only [h, hft]

end MajorityDynamics.Binomial.Approximation
