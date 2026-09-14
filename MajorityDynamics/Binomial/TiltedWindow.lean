import MajorityDynamics.Binomial.ObservableBounds

/-! # Quantitative different-trial expansion for the original A.2 moments

All integrals below are unconditioned product-binomial integrals. Window
geometry and explicit tail masses remain parameters for the uniform asymptotic
application; neither a likelihood identity nor a conditional expansion is assumed.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace MajorityDynamics.Binomial.Approximation

variable {d r : ℕ}

theorem productTilt_eq (p : Probability) (ref old new : Fin d → ℕ)
    (q₀ q₁ : Fin d → Probability) (a : Fin d → ℕ) :
    productTilt old new (fun i => (p : ℝ) * ref i) q₀ q₁ a =
      ∑ i, tiltDifference p ref old new q₀ q₁ i * centered p ref a i := rfl

theorem tilted_window (M : Fin r → Fin d → ℝ) (strict : Fin r → Bool)
    (p : Probability) (ref old new : Fin d → ℕ) (q₀ q₁ : Fin d → Probability)
    (c : ℝ) (e : Fin d → ℕ) (L R : ℝ) (hL : 1 ≤ L) (hLR : L ≤ R)
    (h₀ : ∀ i, (p : ℝ) * ref i < old i) (h₁ : ∀ i, (p : ℝ) * ref i < new i)
    (hL₀ : ∀ i, L ≤ ((old i : ℝ) - (p : ℝ) * ref i) / 2)
    (hL₁ : ∀ i, L ≤ ((new i : ℝ) - (p : ℝ) * ref i) / 2)
    (hRref : ∀ i, (p : ℝ) * ref i ≤ R)
    (hR₀ : ∀ i, (old i : ℝ) - (p : ℝ) * ref i ≤ R)
    (hR₁ : ∀ i, (new i : ℝ) - (p : ℝ) * ref i ≤ R)
    (hb : d * ‖tiltDifference p ref old new q₀ q₁‖ * L ≤ 1 / 4)
    (hδ : likelihoodErrorBound old new (fun i => (p : ℝ) * ref i) (fun _ => L) ≤ 1 / 4) :
    let β := tiltDifference p ref old new q₀ q₁
    let H := |c| * L ^ (∑ i, e i)
    let G := |c| * R ^ (∑ i, e i)
    let b := d * ‖β‖ * L
    let Z := d * ‖β‖ * R
    let S := rectangle (fun i => (p : ℝ) * ref i) (fun _ => L)
    let E₀ := moment M strict p ref old q₀ (monomial c e)
    |moment M strict p ref new q₁ (monomial c e) - E₀ -
      (∑ i, β i * moment M strict p ref old q₀ (fun x => x i * monomial c e x)) +
      (∑ i, β i * (∫ a, centered p ref a i ∂law old q₀) * E₀)| ≤
      12 * H * b ^ 2 + 8 * H * likelihoodErrorBound old new
        (fun i => (p : ℝ) * ref i) (fun _ => L) +
      2 * G * (law new q₁).real Sᶜ +
      2 * G * (1 + b + 2 * Z) * (law old q₀).real Sᶜ := by
  classical
  dsimp only
  let center : Fin d → ℝ := fun i => (p : ℝ) * ref i
  let S := rectangleWindow center (fun _ => L)
  let f := restrictedObservable M strict p ref (monomial c e)
  let β := tiltDifference p ref old new q₀ q₁
  let z := productTilt old new center q₀ q₁
  have hL0 : 0 ≤ L := by linarith
  have hR0 : 0 ≤ R := hL0.trans hLR
  have hcenter : ∀ i, 0 ≤ center i := fun i => mul_nonneg p.property.1.le (Nat.cast_nonneg _)
  have hS := rectangleWindow_nonempty center (fun _ => L) hcenter (fun _ => hL)
  have hrect : ∀ a ∈ S, a ∈ rectangle center (fun _ => L) :=
    fun a ha => (mem_rectangleWindow _ _ _).mp ha
  have hmass (η : Fin d → ℕ) (q : Fin d → Probability)
      (hη : ∀ i, center i < η i) (hηL : ∀ i, L ≤ ((η i : ℝ) - center i) / 2) :
      0 < (law η q).real S := by
    rw [show (S : Set (Fin d → ℕ)) = rectangle center (fun _ => L) from coe_rectangleWindow _ _]
    apply rectangle_mass_pos η q center (fun _ => L) hcenter (fun _ => hL)
    intro i
    have hi := hη i
    have hli := hηL i
    linarith
  have hfS : ∀ a ∈ S, |f a| ≤ |c| * L ^ (∑ i, e i) := by
    intro a ha
    exact restrictedObservable_abs_le M strict p ref c e L hL0 a (hrect a ha)
  have hzS : ∀ a ∈ S, |z a| ≤ d * ‖β‖ * L := by
    intro a ha
    exact linearTilt_abs_le β (centered p ref a) L (hrect a ha)
  have hwindow := window_tilt_expansion old new center (fun _ => L) q₀ q₁ S hS hrect
    h₀ h₁ (fun _ => hL0) hL₀ hL₁ f (|c| * L ^ (∑ i, e i)) (d * ‖β‖ * L)
    (by positivity) (by positivity) hb hδ hfS hzS
  have hglobal (η : Fin d → ℕ) (q : Fin d → Probability)
      (hη : ∀ i, (η i : ℝ) - center i ≤ R) :
      ∀ᵐ a ∂law η q, ∀ i, |centered p ref a i| ≤ R := by
    filter_upwards [law_ae_box η q] with a ha i
    apply abs_le.mpr
    have hai : (a i : ℝ) ≤ η i := by exact_mod_cast ha i
    have hn : (0 : ℝ) ≤ a i := Nat.cast_nonneg _
    have hr := hRref i
    have hi := hη i
    change -R ≤ (a i : ℝ) - center i ∧ (a i : ℝ) - center i ≤ R
    constructor <;> linarith
  have hfglobal (η : Fin d → ℕ) (q : Fin d → Probability)
      (hη : ∀ i, (η i : ℝ) - center i ≤ R) :
      ∀ᵐ a ∂law η q, |f a| ≤ |c| * R ^ (∑ i, e i) := by
    filter_upwards [hglobal η q hη] with a ha
    exact restrictedObservable_abs_le M strict p ref c e R hR0 a ha
  have hzglobal : ∀ᵐ a ∂law old q₀, |z a| ≤ d * ‖β‖ * R := by
    filter_upwards [hglobal old q₀ hR₀] with a ha
    exact linearTilt_abs_le β (centered p ref a) R ha
  have hfSR : ∀ a ∈ S, |f a| ≤ |c| * R ^ (∑ i, e i) := by
    intro a ha
    exact (hfS a ha).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0 hLR _) (abs_nonneg c))
  have h := expansion_transfer old new q₀ q₁ S (hmass old q₀ h₀ hL₀) (hmass new q₁ h₁ hL₁)
    f z (|c| * R ^ (∑ i, e i)) (d * ‖β‖ * R) (d * ‖β‖ * L) _
    (by positivity) (by positivity) (by positivity)
    (mul_le_mul_of_nonneg_left hLR (by positivity)) hfSR hzS
    (hfglobal old q₀ hR₀) (hfglobal new q₁ hR₁) hzglobal hwindow
  have hcross : (∫ a, z a * f a ∂law old q₀) =
      ∑ i, β i * moment M strict p ref old q₀ (fun x => x i * monomial c e x) := by
    rw [show z = fun a => ∑ i, β i * centered p ref a i from rfl, integral_linearTilt]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    rw [← integral_restrictedObservable]
    congr 1
    funext a
    by_cases ha : a ∈ inequalityEvent M strict <;> simp [f, restrictedObservable, ha]
  have hmean : (∫ a, z a ∂law old q₀) = ∑ i, β i * (∫ a, centered p ref a i ∂law old q₀) := by
    change (∫ a, ∑ i, β i * centered p ref a i ∂law old q₀) = _
    rw [integral_finsetSum _ (fun i _ => integrable_law old q₀ _)]
    simp only [integral_const_mul]
  rw [hcross, hmean] at h
  simp only [f, integral_restrictedObservable, S, coe_rectangleWindow] at h
  convert h using 1
  congr 1
  rw [Finset.sum_mul]
  ring

end MajorityDynamics.Binomial.Approximation
