import MajorityDynamics.Probability.ConditionedBinomialBox.Geometry
import MajorityDynamics.Probability.ConditionedBinomialBox.Point
import MajorityDynamics.Probability.ConditionedBinomialBox.Mixture
import MajorityDynamics.Binomial.TiltUniqueness

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace MajorityDynamics.Probability.ConditionedBinomialBox

/-- The complete rectangular-component conclusion on the original natural lattice.
Every measure below is the actual binomial law or its normalized restriction. -/
structure BoxConclusion {r d : ℕ} (M : Fin r → Fin d → ℤ) (strict : Fin r → Bool)
    (N : ℕ) (p : ℝ) (η : Fin d → ℕ) (q : Fin d → Binomial.Probability)
    (cWidth CWidth A cPoint cEvent β : ℝ) (a : Fin d → ℕ) (L : ℕ) : Prop where
  length_pos : 1 ≤ L
  width_lower : cWidth * Real.sqrt (p*N) ≤ (L : ℝ)
  width_upper : (L : ℝ) ≤ CWidth * Real.sqrt (p*N)
  membership : ∀ x, x ∈ Geometry.box a L ↔ ∀ i, a i ≤ x i ∧ x i < a i+L
  cardinality : (Geometry.box a L).card = L^d
  nonempty : (Geometry.box a L).Nonempty
  support : ∀ x ∈ Geometry.box a L, ∀ i, x i ≤ η i
  slack : ∀ x ∈ Geometry.box a L, ∀ j, 0 < ∑ i, (M j i : ℝ)*(x i : ℝ)
  inside : ∀ x ∈ Geometry.box a L,
    x ∈ Binomial.inequalityEvent (fun j i => (M j i : ℝ)) strict
  window : ∀ x ∈ Geometry.box a L, ∀ i,
    |(x i : ℝ) - (η i : ℝ)*(q i : ℝ)| ≤ A*Real.sqrt ((η i : ℝ)*(q i : ℝ))
  point : ∀ x ∈ Geometry.box a L,
    cPoint*(p*N)^(-(d : ℝ)/2) ≤ (Binomial.law η q).real {x}
  conditioned_point : ∀ x ∈ Geometry.box a L,
    cPoint*(p*N)^(-(d : ℝ)/2) ≤
      (cond (Binomial.law η q)
        (Binomial.inequalityEvent (fun j i => (M j i : ℝ)) strict)).real {x}
  box_mass : cEvent ≤ (Binomial.law η q).real (Geometry.box a L : Set (Fin d → ℕ))
  event_mass : cEvent ≤ (Binomial.law η q).real
    (Binomial.inequalityEvent (fun j i => (M j i : ℝ)) strict)
  conditioned_probability : IsProbabilityMeasure
    (cond (Binomial.law η q) (Binomial.inequalityEvent (fun j i => (M j i : ℝ)) strict))
  uniform_probability : IsProbabilityMeasure (uniformBox (Geometry.box a L))
  uniform_singleton : ∀ x, (uniformBox (Geometry.box a L)).real {x} =
    if x ∈ Geometry.box a L then 1 / ((Geometry.box a L).card : ℝ) else 0
  uniform_support : uniformBox (Geometry.box a L) (Geometry.box a L : Set (Fin d → ℕ))ᶜ = 0
  mixture : ∃ ν : Measure (Fin d → ℕ), IsProbabilityMeasure ν ∧
    cond (Binomial.law η q) (Binomial.inequalityEvent (fun j i => (M j i : ℝ)) strict) =
      ENNReal.ofReal β • uniformBox (Geometry.box a L) + ENNReal.ofReal (1-β) • ν

/-- Finite summation and normalization turn the proved geometric and atom bounds
into the complete actual-law result. The uniform endpoint discharges all inputs. -/
theorem assemble {r d : ℕ} (M : Fin r → Fin d → ℤ) (strict : Fin r → Bool)
    (N : ℕ) (p : ℝ) (η : Fin d → ℕ) (q : Fin d → Binomial.Probability)
    (cWidth CWidth A cPoint β : ℝ) (a : Fin d → ℕ) (L : ℕ)
    (hscale : 0 < p*N) (hcWidth : 0 < cWidth) (hcPoint : 0 < cPoint)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : β ≤ cPoint*cWidth^d)
    (hL : 1 ≤ L) (hwidth : cWidth * Real.sqrt (p*N) ≤ (L : ℝ))
    (hupper : (L : ℝ) ≤ CWidth * Real.sqrt (p*N))
    (hsupport : ∀ x ∈ Geometry.box a L, ∀ i, x i ≤ η i)
    (hslack : ∀ x ∈ Geometry.box a L, ∀ j, 0 < ∑ i, (M j i : ℝ)*(x i : ℝ))
    (hwindow : ∀ x ∈ Geometry.box a L, ∀ i,
      |(x i : ℝ) - (η i : ℝ)*(q i : ℝ)| ≤ A*Real.sqrt ((η i : ℝ)*(q i : ℝ)))
    (hpoint : ∀ x ∈ Geometry.box a L,
      cPoint*(p*N)^(-(d : ℝ)/2) ≤ (Binomial.law η q).real {x}) :
    BoxConclusion M strict N p η q cWidth CWidth A cPoint (cPoint*cWidth^d) β a L := by
  classical
  let E := Binomial.inequalityEvent (fun j i => (M j i : ℝ)) strict
  let B := Geometry.box a L
  let ρ := cond (Binomial.law η q) E
  have hB : B.Nonempty := Geometry.box_nonempty a hL
  have hinside : ∀ x ∈ B, x ∈ E := by
    intro x hx j
    have hj := hslack x hx j
    dsimp [E, Binomial.inequalityEvent]
    split
    · exact hj
    · exact hj.le
  have hweight : cPoint*cWidth^d ≤ (cPoint*(p*N)^(-(d : ℝ)/2)) * (B.card : ℝ) := by
    have h := width_point_cancellation d L cPoint cWidth (p*N)
      hcPoint.le hcWidth.le hscale hwidth
    simpa only [B, Geometry.card_box, Nat.cast_pow, mul_comm] using h
  have hmass : cPoint*cWidth^d ≤ (Binomial.law η q).real (B : Set (Fin d → ℕ)) :=
    hweight.trans (finset_mass_lower _ B _ hpoint)
  have hevent : cPoint*cWidth^d ≤ (Binomial.law η q).real E :=
    hmass.trans (measureReal_mono (fun x hx => hinside x hx))
  have hpos : 0 < (Binomial.law η q) E := by
    have hr : 0 < (Binomial.law η q).real E :=
      lt_of_lt_of_le (mul_pos hcPoint (pow_pos hcWidth d)) hevent
    exact ENNReal.toReal_pos_iff.mp hr |>.1
  have hE : MeasurableSet E := Set.to_countable E |>.measurableSet
  let : IsProbabilityMeasure ρ := cond_isProbabilityMeasure hpos.ne'
  have hcond : ∀ x ∈ B, cPoint*(p*N)^(-(d : ℝ)/2) ≤ ρ.real {x} := by
    intro x hx
    exact (hpoint x hx).trans (point_le_conditioned _ hE hpos (hinside x hx))
  exact {
    length_pos := hL
    width_lower := hwidth
    width_upper := hupper
    membership := Geometry.mem_box a L
    cardinality := Geometry.card_box a L
    nonempty := hB
    support := hsupport
    slack := hslack
    inside := hinside
    window := hwindow
    point := hpoint
    conditioned_point := hcond
    box_mass := hmass
    event_mass := hevent
    conditioned_probability := inferInstance
    uniform_probability := uniformBox_probability B hB
    uniform_singleton := by
      intro x
      by_cases hx : x ∈ Geometry.box a L <;>
        simpa [B, hx] using uniformBox_singleton_real B x
    uniform_support := uniformBox_support B
    mixture := exists_uniform_component ρ B hB hβ0 hβ1 hcond (hβ.trans hweight) }

end MajorityDynamics.Probability.ConditionedBinomialBox
