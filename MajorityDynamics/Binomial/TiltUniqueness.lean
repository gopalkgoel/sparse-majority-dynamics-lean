import MajorityDynamics.Binomial.Conditioning
import MajorityDynamics.Analysis.FiniteTilt
import Mathlib.Tactic.Ring

/-!
# Appendix E.1: uniqueness of conditioned binomial tilts

The theorem applies to the literal finite support of independent binomials.
No covariance-positivity or injectivity hypothesis is passed in: the sole
geometric hypothesis is the paper's exclusion of an affine hyperplane.
The proof identifies the log-likelihood parameter by the finite-sum argument
in `Analysis/FiniteTilt.lean`. `Basic.lean` connects these means to integrals
under the actual conditioned product measure.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace MajorityDynamics.Binomial

variable {ι : Type*} [Fintype ι]

theorem logOdds_strictMono : StrictMono logOdds := by
  intro p q hpq
  have h1 := Real.log_lt_log p.property.1 (show (p : ℝ) < q from hpq)
  have h2 := Real.log_lt_log (sub_pos.mpr q.property.2)
    (sub_lt_sub_left (show (p : ℝ) < q from hpq) 1)
  dsimp [logOdds]
  linarith

theorem log_mass (η : ι → ℕ) (q : ι → Probability) (a : Box η) :
    Real.log (mass η q a) =
      ∑ i, (Real.log ((η i).choose (a i) : ℝ) +
        (η i : ℝ) * Real.log (1 - (q i : ℝ)) + vector a i * logOdds (q i)) := by
  rw [mass, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro i _
    have hc : (0 : ℝ) < (η i).choose (a i) := by
      exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ (a i).isLt)
    have hp := (q i).property.1
    have h1p := sub_pos.mpr (q i).property.2
    rw [Real.log_mul (mul_pos hc (pow_pos hp _)).ne' (pow_pos h1p _).ne',
      Real.log_mul hc.ne' (pow_pos hp _).ne', Real.log_pow, Real.log_pow,
      Nat.cast_sub (Nat.le_of_lt_succ (a i).isLt)]
    dsimp [vector, logOdds]
    ring
  · intro i _
    have hc : (0 : ℝ) < (η i).choose (a i) := by
      exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ (a i).isLt)
    exact (mul_pos (mul_pos hc (pow_pos (q i).property.1 _))
      (pow_pos (sub_pos.mpr (q i).property.2) _)).ne'

theorem conditionalWeight_pos (η : ι → ℕ) (q : ι → Probability)
    {S : Finset (Box η)} (hS : S.Nonempty) (a : Box η) :
    0 < conditionalWeight η q S a :=
  div_pos (mass_pos η q a) (eventMass_pos η q hS)

theorem sum_conditionalWeight (η : ι → ℕ) (q : ι → Probability)
    {S : Finset (Box η)} (hS : S.Nonempty) :
    ∑ a ∈ S, conditionalWeight η q S a = 1 := by
  simp_rw [conditionalWeight]
  rw [← Finset.sum_div]
  exact div_self (eventMass_pos η q hS).ne'

/-- The stronger finite-support form of E.1; zero trial counts are permitted
in the statement, but full affine support excludes degenerate coordinates. -/
theorem conditionalMean_injective (η : ι → ℕ) (S : Finset (Box η))
    (hS : S.Nonempty) (hspan : Analysis.FiniteTilt.FullAffineSupport S vector) :
    Function.Injective (fun q : ι → Probability => conditionalMean η q S) := by
  intro q r hmean
  let c : ℝ := (∑ i, (η i : ℝ) *
    (Real.log (1 - (q i : ℝ)) - Real.log (1 - (r i : ℝ)))) -
    Real.log (eventMass η q S) + Real.log (eventMass η r S)
  have hlog (a : Box η) :
      Real.log (conditionalWeight η q S a) - Real.log (conditionalWeight η r S a) =
        c + ∑ i, (logOdds (q i) - logOdds (r i)) * vector a i := by
    rw [conditionalWeight, conditionalWeight,
      Real.log_div (mass_pos η q a).ne' (eventMass_pos η q hS).ne',
      Real.log_div (mass_pos η r a).ne' (eventMass_pos η r hS).ne', log_mass, log_mass]
    dsimp [c]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_sub, sub_mul]
    simp_rw [mul_comm (vector a _) (logOdds _)]
    ring
  have hz := Analysis.FiniteTilt.parameter_eq_zero S vector hspan
    (conditionalWeight η q S) (conditionalWeight η r S)
    (fun a _ => conditionalWeight_pos η q hS a)
    (fun a _ => conditionalWeight_pos η r hS a)
    (sum_conditionalWeight η q hS) (sum_conditionalWeight η r hS)
    (fun i => congrFun hmean i) (fun i => logOdds (q i) - logOdds (r i)) c
    (fun a _ => hlog a)
  funext i
  apply logOdds_strictMono.injective
  exact sub_eq_zero.mp (congrFun hz i)

/-- The original mixed weak/strict event on the ambient binomial sample space. -/
def inequalityEvent {r : ℕ} (M : Fin r → ι → ℝ) (strict : Fin r → Bool) : Set (ι → ℕ) :=
  {a | ∀ j, if strict j then 0 < ∑ i, M j i * (a i : ℝ)
    else 0 ≤ ∑ i, M j i * (a i : ℝ)}

/-- The same event enumerated inside the full binomial support. -/
def inequalitySupport {r : ℕ} (η : ι → ℕ) (M : Fin r → ι → ℝ)
    (strict : Fin r → Bool) : Finset (Box η) := by
  classical
  exact Finset.univ.filter fun a => point a ∈ inequalityEvent M strict

theorem inequalitySupport_event {r : ℕ} (η : ι → ℕ) (q : ι → Probability)
    (M : Fin r → ι → ℝ) (strict : Fin r → Bool) :
    event (inequalitySupport η M strict) =ᵐ[law η q] inequalityEvent M strict :=
  filter_event_ae_eq η q _

theorem inequalitySupport_condition {r : ℕ} (η : ι → ℕ) (q : ι → Probability)
    (M : Fin r → ι → ℝ) (strict : Fin r → Bool) :
    conditionalLaw η q (inequalitySupport η M strict) =
      ProbabilityTheory.cond (law η q) (inequalityEvent M strict) :=
  conditionalLaw_filter η q _

/-- Exact E.1 contract: positive integer trial counts, arbitrary real matrix,
original mixed inequalities, non-hyperplane support, positive event mass,
and injectivity of the integral under the actual conditioned product measure. -/
def TiltUniquenessTheorem : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ η : Fin d → ℕ, (∀ i, 1 ≤ η i) →
    ∀ (r : ℕ) (M : Fin r → Fin d → ℝ) (strict : Fin r → Bool),
      Analysis.FiniteTilt.FullAffineSupport (inequalitySupport η M strict) vector →
      (∀ q : Fin d → Probability, 0 < (law η q).real (inequalityEvent M strict)) ∧
      Function.Injective (fun q : Fin d → Probability => fun i =>
        ∫ a, (a i : ℝ) ∂ProbabilityTheory.cond (law η q) (inequalityEvent M strict))

/-- Appendix E.1, with no unproved internal or external input. -/
theorem tilt_uniqueness : TiltUniquenessTheorem := by
  intro d hd η _ r M strict hspan
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hS := hspan.nonempty
  constructor
  · intro q
    have hp := eventMass_pos η q hS
    rw [eventMass_eq_measure,
      measureReal_congr (inequalitySupport_event η q M strict)] at hp
    exact hp
  · intro q q' he
    apply conditionalMean_injective η _ hS hspan
    funext i
    change conditionalMean η q (inequalitySupport η M strict) i =
      conditionalMean η q' (inequalitySupport η M strict) i
    rw [conditionalMean_eq_integral, conditionalMean_eq_integral,
      inequalitySupport_condition, inequalitySupport_condition]
    exact congrFun he i

end MajorityDynamics.Binomial
