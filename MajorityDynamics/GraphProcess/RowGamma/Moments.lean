import MajorityDynamics.GraphProcess.RowConcentration.Expectations
import MajorityDynamics.GraphProcess.RowConcentration.Regime
import MajorityDynamics.Local.Admissibility
import MajorityDynamics.Probability.ConditionedBinomialLocalCLT.MomentsConditional

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace MajorityDynamics.GraphProcess.RowGamma
open Universal
open Probability.ConditionedBinomialLocalCLT

variable {V : Type*} [Fintype V] {n : ℕ}

/-- A fixed scalar expectation bound, independent of any requested tail exponent. -/
def secondMomentConstant (T φ : ℝ) : ℝ :=
  8 * Moments.rawConstant φ 2 + 2 * (T + 1) ^ 2

theorem secondMomentConstant_nonneg {T φ : ℝ} (hφ : 0 < φ) :
    0 ≤ secondMomentConstant T φ := by
  unfold secondMomentConstant Moments.rawConstant
  positivity

/-- The finite-regime moment estimate uses actual conditioned row marginals. -/
theorem finite_second_moment (y : Local.CoarseData V n) (q : Local.Tilt n)
    {T φ p : ℝ} (hT : 1 < T) (hφ : 0 < φ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hN : 2*T ≤ (Fintype.card V : ℝ))
    (hroot : (2*T)^2 ≤ p*Fintype.card V)
    (hsizes : ∀ s, (Fintype.card V : ℝ)/T ≤ (y.sizes s : ℝ))
    (htilt : ∀ s t, |(q s t : ℝ)-p| ≤ T*p/Real.sqrt (p*Fintype.card V))
    (hc : RowConcentration.Conditioning y q φ) (v : V) (t : History (n+1)) :
    Integrable (fun d : RowArray.Ambient y.part =>
      ((RowArray.values d v t : ℝ)-p*y.sizes t)^2/(p*Fintype.card V))
      (RowConcentration.conditionedLaw y q) ∧
    (∫ d, ((RowArray.values d v t : ℝ)-p*y.sizes t)^2/(p*Fintype.card V)
      ∂RowConcentration.conditionedLaw y q) ≤ secondMomentConstant T φ := by
  let := RowConcentration.conditioned_probability y q hφ hc
  refine ⟨Integrable.of_finite, ?_⟩
  let η := Local.trials y.sizes (y.part v)
  let qr := q (y.part v)
  let E := RowArray.rowHistory (y.part v)
  let ρ := cond (Binomial.law η qr) E
  let x : ℝ := p*Fintype.card V
  have hcard0 : 0 < (Fintype.card V : ℝ) := by linarith
  have hx : 0 < x := mul_pos hp hcard0
  have hs : 1 ≤ 2*Real.sqrt x := by
    have hh := Real.sq_sqrt hx.le
    have hh0 := Real.sqrt_nonneg x
    change (2*T)^2 ≤ x at hroot
    nlinarith [sq_nonneg (2*T)]
  have hmean (i : History (n+1)) : (η i : ℝ)*(qr i : ℝ) ≤ (2*Real.sqrt x)^2 := by
    have h := (RowConcentration.finite_mean_bounds y q hT hp hp1 hN hroot hsizes htilt (y.part v) i).1
    have hh := Real.sq_sqrt hx.le
    dsimp [η,qr,x] at *
    nlinarith
  have hmass : φ ≤ (Binomial.law η qr).real E := by
    change φ ≤ (Local.rowLaw y.sizes q (y.part v)).real (RowArray.rowHistory (y.part v))
    rw [RowConcentration.row_history_mass]
    exact hc (y.part v)
  have hmass0 : (Binomial.law η qr) E ≠ 0 :=
    (ENNReal.toReal_pos_iff.mp (hφ.trans_le hmass)).1.ne'
  let : IsProbabilityMeasure ρ := cond_isProbabilityMeasure hmass0
  have hint (f : (History (n+1) → ℕ) → ℝ) : Integrable f ρ :=
    Moments.integrable_cond η qr E hmass0 f
  have hm := Moments.raw_coordinate η qr E hφ hmass hs hmean t 2
  have hshift := (RowConcentration.finite_mean_bounds y q hT hp hp1 hN hroot hsizes htilt (y.part v) t).2
  have hshift2 : ((η t : ℝ)*(qr t : ℝ)-p*y.sizes t)^2 ≤ (T+1)^2*x := by
    have h := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ (T+1)*Real.sqrt x)).mpr hshift
    rw [sq_abs, mul_pow, Real.sq_sqrt hx.le] at h
    dsimp [η,qr]
    nlinarith
  have hpoint (a : History (n+1) → ℕ) :
      ((a t : ℝ)-p*y.sizes t)^2 ≤
        2*|(a t : ℝ)-η t*(qr t : ℝ)|^2+2*((η t : ℝ)*(qr t : ℝ)-p*y.sizes t)^2 := by
    rw [sq_abs]
    nlinarith [sq_nonneg ((a t : ℝ)-2*((η t : ℝ)*(qr t : ℝ))+p*y.sizes t)]
  have hbound : (∫ a, ((a t : ℝ)-p*y.sizes t)^2 ∂ρ) ≤
      secondMomentConstant T φ*x := by
    calc
      _ ≤ ∫ a, 2*|(a t : ℝ)-η t*(qr t : ℝ)|^2+
          2*((η t : ℝ)*(qr t : ℝ)-p*y.sizes t)^2 ∂ρ :=
        integral_mono (hint _) (hint _) hpoint
      _ = 2*(∫ a, |(a t : ℝ)-η t*(qr t : ℝ)|^2 ∂ρ)+
          2*((η t : ℝ)*(qr t : ℝ)-p*y.sizes t)^2 := by
        rw [integral_add ((hint _).const_mul _) (integrable_const _), integral_const_mul]
        simp
      _ ≤ secondMomentConstant T φ*x := by
        have hh := Real.sq_sqrt hx.le
        change (∫ a, |(a t : ℝ)-η t*(qr t : ℝ)|^2 ∂ρ) ≤ _ at hm
        rw [mul_pow, Real.sq_sqrt hx.le] at hm
        unfold secondMomentConstant
        nlinarith
  have heq : (∫ d, ((RowArray.values d v t : ℝ)-p*y.sizes t)^2/(p*Fintype.card V)
      ∂RowConcentration.conditionedLaw y q) =
      (∫ a, ((a t : ℝ)-p*y.sizes t)^2 ∂ρ)/x := by
    have h := RowConcentration.integral_row_function y q hφ hc v
      (fun a => ((a t : ℝ)-p*y.sizes t)^2/x)
    simp only [RowArray.values, RowArray.naturalRows, Binomial.point, Int.cast_natCast] at h ⊢
    rw [h, RowArray.rowCondition_eq_cond, integral_div]
    rfl
  rw [heq]
  exact (div_le_iff₀ hx).mpr hbound

universe u
/-- Original-input endpoint. The constant and threshold do not depend on a tail exponent. -/
theorem uniform_second_moment {θ T φ : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n), Local.CoreAdmissible y q T φ p →
      ∀ v t,
      Integrable (fun d : RowArray.Ambient y.part =>
        ((RowArray.values d v t : ℝ)-p*y.sizes t)^2/(p*N))
        (RowConcentration.conditionedLaw y q) ∧
      (∫ d, ((RowArray.values d v t : ℝ)-p*y.sizes t)^2/(p*N)
        ∂RowConcentration.conditionedLaw y q) ≤ secondMomentConstant T φ := by
  obtain ⟨N₀,h₀⟩ := EnumerationBounds.eventually_window hθlo hθhi hT
    (L := (2*T)^2) (by positivity) (U := 1) zero_lt_one (M := 2*T) (by linarith)
  refine ⟨N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi y q hLA v t
  have h := h₀ N hN p hlo hhi
  subst N
  exact finite_second_moment y q hT hφ h.2.1 h.2.2.2.2 h.2.2.1 h.2.2.2.1
    (fun s => by simpa [div_eq_mul_inv, mul_comm] using hLA.sizes s)
    hLA.tilt hLA.conditioning v t

end MajorityDynamics.GraphProcess.RowGamma

/-- info: 'MajorityDynamics.GraphProcess.RowGamma.secondMomentConstant_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowGamma.secondMomentConstant_nonneg

/-- info: 'MajorityDynamics.GraphProcess.RowGamma.finite_second_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowGamma.finite_second_moment

/-- info: 'MajorityDynamics.GraphProcess.RowGamma.uniform_second_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowGamma.uniform_second_moment
