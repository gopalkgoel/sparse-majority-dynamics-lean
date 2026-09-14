import MajorityDynamics.Binomial.GaussianWindowIntegral

/-! # Quantitative comparison of the actual binomial and Gaussian moments -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace MajorityDynamics.Binomial.Approximation
variable {d r : ℕ}

set_option maxHeartbeats 800000 in
/-- All lattice, normalization, polynomial, tie-boundary, and tail errors are
explicit. The uniform endpoint specializes the displayed window conditions. -/
theorem gaussian_window_comparison (M : Fin r → Fin d → ℤ) (strict : Fin r → Bool)
    (p : Probability) (η : Fin d → ℕ) (α : Fin d → ℝ) (c : ℝ) (e : Fin d → ℕ)
    (L R ε : ℝ) (hL : 1 ≤ L) (hR : 0 ≤ R) (hη : ∀ i, 0 < η i) (hηR : ∀ i, (η i : ℝ) ≤ R)
    (hcomp : ∀ i, L ≤ ((η i : ℝ) - (p : ℝ) * η i) / 2)
    (hsucc : ∀ i, L ≤ ((p : ℝ) * η i) / 2)
    (hpoint : gaussianWindowError p η (fun _ => L) ≤ 1 / 4)
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 2) (hcellsmall : 4 * d * ε ≤ 1 / 4)
    (hcell : ∀ a ∈ rectangleWindow (fun i => (p : ℝ) * η i) (fun _ => L), ∀ i,
      |(gaussianReal (gaussianMean p η α i) (gaussianVariance p η i)).real
        (Ico (centered p η a i) (centered p η a i + 1)) -
        gaussianPDFReal (gaussianMean p η α i) (gaussianVariance p η i) (centered p η a i)| ≤
      ε * gaussianPDFReal (gaussianMean p η α i) (gaussianVariance p η i) (centered p η a i)) :
    let H := |c| * (L + 1) ^ (∑ i, e i)
    |(∫ a in inequalityEvent (fun j i => (M j i : ℝ)) strict,
        monomial c e (centered p η a) ∂law η (gaussianTilt p η α)) -
      (∫ x in gaussianEvent M p η, monomial c e x ∂gaussianLaw p η α)| ≤
      8 * H * gaussianWindowError p η (fun _ => L) + 32 * H * d * ε +
      2 * (|c| * R ^ (∑ i, e i)) * (law η (gaussianTilt p η α)).real
        (rectangle (fun i => (p : ℝ) * η i) (fun _ => L))ᶜ +
      |c| * (∑ i, (e i : ℝ)) * (L + 1) ^ (∑ i, e i) / (L + 1) +
      2 * H * (gaussianLaw p η α).real (gaussianBoundary M p η) +
      Real.sqrt (∫ x, monomial c e x ^ 2 ∂gaussianLaw p η α) *
        Real.sqrt ((gaussianLaw p η α).real (gaussianCellWindow p η L)ᶜ) +
      H * (gaussianLaw p η α).real (gaussianCellWindow p η L)ᶜ := by
  classical
  dsimp only
  let S := rectangleWindow (fun i => (p : ℝ) * η i) (fun _ => L)
  let f := restrictedObservable (fun j i => (M j i : ℝ)) strict p η (monomial c e)
  have hL0 : 0 ≤ L := by linarith
  have hRwin : 0 ≤ L + 1 := by linarith
  have hμ (i : Fin d) : 0 < (p : ℝ) * η i := mul_pos p.property.1 (by exact_mod_cast hη i)
  have hS : S.Nonempty := rectangleWindow_nonempty _ _ (fun i => (hμ i).le) (fun _ => hL)
  have hrect : ∀ a ∈ S, a ∈ rectangle (fun i => (p : ℝ) * η i) (fun _ => L) :=
    fun a ha => (mem_rectangleWindow _ _ _).mp ha
  have hcenter (i : Fin d) : (p : ℝ) * η i < η i := by
    have hi : (0 : ℝ) < η i := by exact_mod_cast hη i
    nlinarith [p.property.2]
  have hsupp (a : Fin d → ℕ) (ha : a ∈ S) : ∀ i, a i ≤ η i := by
    apply rectangle_support η (fun i => (p : ℝ) * η i) (fun _ => L) _ (hrect a ha)
    intro i
    have hc := hcenter i
    have hl := hcomp i
    linarith
  have hglobal (a : Fin d → ℕ) (ha : ∀ i, a i ≤ η i) : ∀ i, |centered p η a i| ≤ R := by
    intro i
    apply abs_le.mpr
    have hai : (a i : ℝ) ≤ η i := by exact_mod_cast ha i
    have ha0 : (0 : ℝ) ≤ a i := Nat.cast_nonneg _
    have hc := hcenter i
    have hm := hμ i
    have hr := hηR i
    change -R ≤ (a i : ℝ) - (p : ℝ) * η i ∧ (a i : ℝ) - (p : ℝ) * η i ≤ R
    constructor <;> linarith
  have hfS : ∀ a ∈ S, |f a| ≤ |c| * (L + 1) ^ (∑ i, e i) := by
    intro a ha
    apply restrictedObservable_abs_le _ strict p η c e (L + 1) hRwin a
    intro i
    exact (hrect a ha i).trans (by linarith)
  have hbin := finite_gaussian_comparison p η α (fun _ => L) hη (fun _ => hL0) hcomp hsucc
    S hS hrect f (|c| * (L + 1) ^ (∑ i, e i)) (by positivity) hfS hpoint
  have hcells := finite_cell_comparison p η α hη S hS ε (|c| * (L + 1) ^ (∑ i, e i))
    hε hεsmall hcellsmall f (by positivity) hfS hcell
  have hmass : 0 < (law η (gaussianTilt p η α)).real S := by
    rw [show (S : Set (Fin d → ℕ)) = rectangle (fun i => (p : ℝ) * η i) (fun _ => L) from coe_rectangleWindow _ _]
    apply rectangle_mass_pos η (gaussianTilt p η α) _ _ (fun i => (hμ i).le) (fun _ => hL)
    intro i
    have hc := hcenter i
    have hl := hcomp i
    linarith
  have hgaussmass : 0 < (gaussianLaw p η α).real (gaussianCellWindow p η L) := by
    obtain ⟨a, ha⟩ := hS
    have hcellpos : 0 < gaussianCellMass p η α a := by
      rw [gaussianCellMass_eq_prod]
      apply Finset.prod_pos
      intro i _
      exact (log_weight_error _ _ ε (gaussianPDFReal_pos _ _ _ (ne_of_gt (hμ i))) hεsmall (hcell a ha i)).1
    exact hcellpos.trans_le (measureReal_mono (fun x hx => Set.mem_iUnion₂.mpr ⟨a, ha, hx⟩))
  have htrunc := finiteExpectation_truncation_error η (gaussianTilt p η α) S hmass f
    (|c| * R ^ (∑ i, e i))
    (fun a ha => restrictedObservable_abs_le _ strict p η c e R hR a (hglobal a (hsupp a ha)))
    (ae_restrict_of_ae (by
      filter_upwards [law_ae_box η (gaussianTilt p η α)] with a ha
      exact restrictedObservable_abs_le _ strict p η c e R hR a (hglobal a ha)))
  have hcont := gaussian_window_integral_error M strict p η α c e L hL0 hgaussmass
  dsimp only at hcont
  let J := ∫ x in gaussianEvent M p η, monomial c e x ∂gaussianLaw p η α
  rw [abs_sub_comm] at hcells hcont
  have hmid := (abs_sub_le (finiteExpectation η (gaussianTilt p η α) S f)
    (gaussianLatticeExpectation p η α S f) J).trans (add_le_add hbin
      ((abs_sub_le (gaussianLatticeExpectation p η α S f) (gaussianCellExpectation p η α S f) J).trans
        (add_le_add hcells hcont)))
  have hchain := (abs_sub_le (∫ a, f a ∂law η (gaussianTilt p η α))
    (finiteExpectation η (gaussianTilt p η α) S f) J).trans (add_le_add htrunc hmid)
  simp only [f, integral_restrictedObservable, S, coe_rectangleWindow] at hchain
  change _ ≤ _ at hchain
  simpa only [J, moment, add_assoc, add_left_comm, add_comm] using hchain

end MajorityDynamics.Binomial.Approximation
