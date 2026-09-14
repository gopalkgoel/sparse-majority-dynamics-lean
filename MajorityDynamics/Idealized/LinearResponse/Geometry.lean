import MajorityDynamics.Idealized.LinearResponse.Rates
import MajorityDynamics.Idealized.LinearResponse.Quotient

/-! Uniform eventual geometry of the reference and perturbed size vectors:
positivity of all residual trial counts, nonempty supports, and E.3
admissibility of the perturbed sizes with a vanishing imbalance parameter. -/

noncomputable section
open Filter Topology
open scoped BigOperators

namespace MajorityDynamics.Idealized.LinearResponse

open MajorityDynamics.Universal
open MajorityDynamics.Idealized.RowLimits
open MajorityDynamics.Idealized.Process
open MajorityDynamics.Binomial.Approximation (Density scale)

variable {n : ℕ}

/-- The E.3 imbalance parameter attached to a perturbed size vector. -/
def xiScale (N : ℕ) (p : ℝ) (n : ℕ) (T : ℝ) : ℝ :=
  ((Fintype.card (History (n + 1)) : ℝ) * T + 1) * (betaScale N p n * Real.sqrt (p * (N : ℝ)))

theorem sizeScale_eq (N : ℕ) (hN : 0 < N) (p : ℝ) (n : ℕ) :
    sizeScale N p n = betaScale N p n * N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  unfold sizeScale betaScale
  rw [div_mul_eq_mul_div, eq_div_iff hsq.ne']
  have h := Real.mul_self_sqrt hN0.le
  calc
    Real.sqrt (N : ℝ) * Real.sqrt (p * N) ^ n * Real.sqrt (N : ℝ) =
        Real.sqrt (p * N) ^ n * (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) := by ring
    _ = _ := by rw [h]

theorem betaScale_nonneg (N : ℕ) (p : ℝ) (n : ℕ) : 0 ≤ betaScale N p n := by
  unfold betaScale
  positivity

theorem sizeScale_nonneg (N : ℕ) (p : ℝ) (n : ℕ) : 0 ≤ sizeScale N p n := by
  unfold sizeScale
  positivity

theorem abs_character (r : Fin (n + 1)) (t : History (n + 1)) : |character r t| = 1 := by
  have h (b : Bool) : |sign b| = 1 := by cases b <;> norm_num [sign]
  unfold character
  exact h _

/-- A signed sum of perturbed sizes is controlled by the perturbation when the
reference sum vanishes. -/
theorem abs_sum_coeff_le (M : History (n + 1) → ℝ) (hM : ∀ t, |M t| ≤ 1)
    (ref sizes : Local.Sizes n) (hbal : ∑ t, M t * (ref t : ℝ) = 0) (E : ℝ)
    (hclose : ∀ t, |(sizes t : ℝ) - ref t| ≤ E) :
    |∑ t, M t * (sizes t : ℝ)| ≤ (Fintype.card (History (n + 1)) : ℝ) * (1 * E) := by
  have h2 : (∑ t, M t * ((sizes t : ℝ) - ref t)) =
      ∑ t, M t * (sizes t : ℝ) - ∑ t, M t * (ref t : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have h : (∑ t, M t * (sizes t : ℝ)) = ∑ t, M t * ((sizes t : ℝ) - ref t) := by
    rw [h2, hbal, sub_zero]
  rw [h]
  exact abs_sum_mul_le' M (fun t => (sizes t : ℝ) - ref t) 1 E hM hclose

/-- All size-geometry facts used by the response proof. -/
structure SizeFacts (N : ℕ) (p : Binomial.Probability) (T : ℝ) (n ell : ℕ)
    (ref sizes : Local.Sizes n) : Prop where
  ref_lower : ∀ t, (N : ℝ) * ν n t / 2 < ref t
  ref_upper : ∀ t, (ref t : ℝ) < 2 * N * ν n t
  ref_pos : ∀ t, 0 < ref t
  sizes_pos : ∀ t, 0 < sizes t
  sizes_lower : ∀ t, (N : ℝ) * ν n t / 4 ≤ sizes t
  sizes_upper : ∀ t, (sizes t : ℝ) ≤ 4 * N * ν n t
  ref_support : ∀ t, 2 * n + 5 ≤ ref t
  sizes_support : ∀ t, 2 * n + 5 ≤ sizes t
  ref_residual : ∀ s t, (N : ℝ) * ν n t / 8 ≤ residual (p : ℝ) ref ref s t
  residual : ∀ s t, (N : ℝ) * ν n t / 8 ≤ residual (p : ℝ) ref sizes s t
  perturbation : ∀ t, T * sizeScale N (p : ℝ) n ≤ (N : ℝ) * ν n t / 16
  admissible : ∀ s, AdmissibleSizes N p (ell + 1) T (xiScale N (p : ℝ) n T) s sizes
  imbalance : |nextImbalance sizes| ≤ xiScale N (p : ℝ) n T * N / Real.sqrt ((p : ℝ) * N)
  xi_pos : 0 < xiScale N (p : ℝ) n T
  xi_le : xiScale N (p : ℝ) n T ≤ T

theorem eventually_rpow_neg_le (κ ε : ℝ) (hκ : 0 < κ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-κ) ≤ ε := by
  have h := ((tendsto_rpow_neg_atTop hκ).comp tendsto_natCast_atTop_atTop).eventually
    (eventually_le_nhds hε)
  filter_upwards [h] with N hN
  exact hN

set_option maxHeartbeats 1600000 in
/-- The uniform geometry statement. `Kc` is any fixed constant to be absorbed by
`β₀√(pN) → 0`. -/
theorem eventually_geometry (θ T : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (n ell : ℕ) (Kc : ℝ) (hKc : 0 ≤ Kc) (hk : (n : ℝ) + 1 < 1 / (1 - θ)) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Binomial.Probability, Density θ T N p →
      Kc * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) ≤ 1 ∧
      ∀ (a : Process.Data) (D : ℕ), Process.Specification N p D ell a → n + 1 < D →
      ∀ sizes : Local.Sizes n,
        (∀ t, |(sizes t : ℝ) - ((a.state n).sizes t : ℝ)| ≤ T * sizeScale N (p : ℝ) n) →
        SizeFacts N p T n ell (a.state n).sizes sizes := by
  have hT0 : 0 < T := by linarith
  let : Nonempty (History (n + 1)) := ⟨(bits _).symm (fun _ => false)⟩
  obtain ⟨νmin, hνmin, hνle⟩ :=
    finite_common_positive (fun t : History (n + 1) => ν n t) (ν_positive n)
  have hd0 : (0 : ℝ) ≤ (Fintype.card (History (n + 1)) : ℝ) := Nat.cast_nonneg _
  have hκ := responseRate_pos hθlo hθhi hk
  have hK₁ : 0 < Kc + 16 * T / νmin + ((Fintype.card (History (n + 1)) : ℝ) * T + 1) + T + 1 := by
    positivity
  have hNν : ∀ᶠ N : ℕ in atTop, (8 * (n : ℝ) + 36) ≤ (N : ℝ) * νmin :=
    (tendsto_natCast_atTop_atTop.atTop_mul_const hνmin).eventually (eventually_ge_atTop _)
  filter_upwards [eventually_level_sizes (n := n) θ T ell hθhi hT0,
    eventually_basic θ T hθlo hθhi hT, eventually_small θ T hθlo hθhi hT n 0 hk,
    eventually_rpow_neg_le (responseRate θ n)
      (1 / (Kc + 16 * T / νmin + ((Fintype.card (History (n + 1)) : ℝ) * T + 1) + T + 1 + 1))
      hκ (by positivity), hNν] with N hlev hbasic hsmall hrpow hNν
  intro p hp
  obtain ⟨hNpos, hlog, hbasic⟩ := hbasic
  obtain ⟨hs1, _, hp8⟩ := hbasic p hp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hpN : 0 < (p : ℝ) * N := mul_pos p.property.1 hN0
  have hs : 0 < Real.sqrt ((p : ℝ) * N) := Real.sqrt_pos.mpr hpN
  have hβpos : 0 < betaScale N (p : ℝ) n :=
    div_pos (pow_pos hs n) (Real.sqrt_pos.mpr hN0)
  have hx0 : 0 < (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) := mul_pos hβpos hs
  have hβ : (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) ≤ (N : ℝ) ^ (-responseRate θ n) := by
    have h := (hsmall p hp).2.2.2
    simpa only [pow_zero, mul_one] using h
  have hK₁x : (Kc + 16 * T / νmin + ((Fintype.card (History (n + 1)) : ℝ) * T + 1) + T + 1) * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) ≤ 1 := by
    calc
      (Kc + 16 * T / νmin + ((Fintype.card (History (n + 1)) : ℝ) * T + 1) + T + 1) * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) ≤ (Kc + 16 * T / νmin + ((Fintype.card (History (n + 1)) : ℝ) * T + 1) + T + 1) * (1 / ((Kc + 16 * T / νmin + ((Fintype.card (History (n + 1)) : ℝ) * T + 1) + T + 1) + 1)) :=
        mul_le_mul_of_nonneg_left (hβ.trans hrpow) hK₁.le
      _ ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]
        linarith
  have hsub (c : ℝ) (hcK : c ≤ (Kc + 16 * T / νmin + ((Fintype.card (History (n + 1)) : ℝ) * T + 1) + T + 1)) : c * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) ≤ 1 :=
    (mul_le_mul_of_nonneg_right hcK hx0.le).trans hK₁x
  have hdT0 : 0 ≤ (Fintype.card (History (n + 1)) : ℝ) * T := mul_nonneg hd0 hT0.le
  have hinv0 : 0 ≤ 16 * T / νmin := by positivity
  have h16 : 16 * T / νmin * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) ≤ 1 := hsub _ (by linarith)
  have hdT : ((Fintype.card (History (n + 1)) : ℝ) * T + 1) * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) ≤ 1 := hsub _ (by linarith)
  have hTx : T * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) ≤ 1 := hsub _ (by linarith)
  refine ⟨hsub Kc (by linarith), ?_⟩
  intro a D hspec hnD sizes hclose
  have hn : n < D := Nat.lt_of_succ_lt hnD
  have hlevs := hlev.2 p hp (a.state n) (hspec.estimates n hn)
  have hsym := hspec.symmetry n hn
  -- reference bounds
  have href_lower : ∀ t, (N : ℝ) * ν n t / 2 < (a.state n).sizes t := fun t => (hlevs t).2.1
  have href_upper : ∀ t, ((a.state n).sizes t : ℝ) < 2 * N * ν n t := fun t => (hlevs t).2.2
  have href_pos : ∀ t, 0 < (a.state n).sizes t := fun t => (hlevs t).1
  -- the perturbation is small: T * sizeScale ≤ N νmin / 16
  have hβle : betaScale N (p : ℝ) n ≤ (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) := le_mul_of_one_le_right hβpos.le hs1
  have hTβ : T * betaScale N (p : ℝ) n ≤ νmin / 16 := by
    have h1 : 16 * T * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) ≤ νmin := by
      have h16' : 16 * T * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) / νmin ≤ 1 := by
        rw [← div_mul_eq_mul_div]
        exact h16
      have := (div_le_iff₀ hνmin).mp h16'
      linarith
    have h3 := mul_le_mul_of_nonneg_left hβle hT0.le
    linarith only [h1, h3]
  have hTS : T * sizeScale N (p : ℝ) n ≤ (N : ℝ) * νmin / 16 := by
    rw [sizeScale_eq N hNpos]
    have := mul_le_mul_of_nonneg_right hTβ hN0.le
    linarith
  have hNνt (t : History (n + 1)) : (N : ℝ) * νmin ≤ (N : ℝ) * ν n t :=
    mul_le_mul_of_nonneg_left (hνle t) hN0.le
  have hclose' (t : History (n + 1)) :
      ((a.state n).sizes t : ℝ) - (N : ℝ) * νmin / 16 ≤ sizes t ∧
        (sizes t : ℝ) ≤ (a.state n).sizes t + (N : ℝ) * νmin / 16 := by
    obtain ⟨h1, h2⟩ := abs_le.mp (hclose t)
    constructor <;> linarith [h1, h2]
  have hsizes_lower : ∀ t, (N : ℝ) * ν n t / 4 ≤ sizes t := by
    intro t
    have := hNνt t
    linarith [(hclose' t).1, href_lower t]
  have hsizes_upper : ∀ t, (sizes t : ℝ) ≤ 4 * N * ν n t := by
    intro t
    have := hNνt t
    linarith [(hclose' t).2, href_upper t]
  have hsizes_pos : ∀ t, 0 < sizes t := by
    intro t
    have h1 := hsizes_lower t
    have h2 : (0 : ℝ) < N * ν n t / 4 := by
      have := ν_positive n t
      positivity
    exact_mod_cast (h2.trans_le h1)
  have hsupport (t : History (n + 1)) : (2 * n + 5 : ℝ) ≤ (N : ℝ) * ν n t / 4 := by
    have := hNνt t
    linarith
  have href_support : ∀ t, 2 * n + 5 ≤ (a.state n).sizes t := by
    intro t
    have h := (hsupport t).trans (by
      linarith [href_lower t, mul_nonneg hN0.le (ν_positive n t).le] :
        (N : ℝ) * ν n t / 4 ≤ (a.state n).sizes t)
    exact_mod_cast h
  have hsizes_support : ∀ t, 2 * n + 5 ≤ sizes t := by
    intro t
    have h := (hsupport t).trans (hsizes_lower t)
    exact_mod_cast h
  have hdiag (s t : History (n + 1)) : diagonal s t ≤ 1 := by
    unfold diagonal
    split_ifs <;> norm_num
  have hpref (t : History (n + 1)) : (p : ℝ) * (a.state n).sizes t ≤ 1 / 8 * (a.state n).sizes t :=
    mul_le_mul_of_nonneg_right hp8 (Nat.cast_nonneg _)
  have hone (t : History (n + 1)) : (1 : ℝ) ≤ (N : ℝ) * ν n t / 16 := by
    have := hNνt t
    linarith
  have href_residual : ∀ s t, (N : ℝ) * ν n t / 8 ≤ residual (p : ℝ) (a.state n).sizes (a.state n).sizes s t := by
    intro s t
    unfold residual
    linarith [hdiag s t, hpref t, href_lower t, href_upper t, hone t]
  have hresidual : ∀ s t, (N : ℝ) * ν n t / 8 ≤ residual (p : ℝ) (a.state n).sizes sizes s t := by
    intro s t
    unfold residual
    linarith [hdiag s t, hpref t, href_lower t, href_upper t, hone t, (hclose' t).1, hNνt t]
  -- admissibility of the perturbed sizes
  have hS0 : 0 ≤ sizeScale N (p : ℝ) n := sizeScale_nonneg _ _ _
  have hξN : xiScale N (p : ℝ) n T * N / Real.sqrt ((p : ℝ) * N) =
      ((Fintype.card (History (n + 1)) : ℝ) * T + 1) * sizeScale N (p : ℝ) n := by
    unfold xiScale
    rw [sizeScale_eq N hNpos, div_eq_iff hs.ne']
    ring
  have hcard : (Fintype.card (History (n + 1)) : ℝ) * (1 * (T * sizeScale N (p : ℝ) n)) ≤
      ((Fintype.card (History (n + 1)) : ℝ) * T + 1) * sizeScale N (p : ℝ) n := by
    linarith only [hS0]
  have hdx : (Fintype.card (History (n + 1)) : ℝ) * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) ≤ 1 := by
    have h1 : (Fintype.card (History (n + 1)) : ℝ) ≤ (Fintype.card (History (n + 1)) : ℝ) * T + 1 := by
      have := mul_le_mul_of_nonneg_left hT.le hd0
      linarith only [this]
    exact (mul_le_mul_of_nonneg_right h1 hx0.le).trans hdT
  have hdecision : (Fintype.card (History (n + 1)) : ℝ) * (1 * (T * sizeScale N (p : ℝ) n)) ≤
      T * N / Real.sqrt ((p : ℝ) * N) := by
    rw [le_div_iff₀ hs, sizeScale_eq N hNpos]
    calc
      (Fintype.card (History (n + 1)) : ℝ) * (1 * (T * (betaScale N (p : ℝ) n * N))) *
          Real.sqrt ((p : ℝ) * N) = T * N * ((Fintype.card (History (n + 1)) : ℝ) * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N))) := by
        ring
      _ ≤ T * N * 1 := mul_le_mul_of_nonneg_left hdx (by positivity)
      _ = T * N := mul_one _
  have hbal_last : (∑ t, character (Fin.last n) t * ((a.state n).sizes t : ℝ)) = 0 :=
    symmetric_imbalance_eq_zero (a.state n) hsym (Fin.last n)
  have hnext : nextImbalance sizes = ∑ t, character (Fin.last n) t * (sizes t : ℝ) := rfl
  have himb : |nextImbalance sizes| ≤
      (Fintype.card (History (n + 1)) : ℝ) * (1 * (T * sizeScale N (p : ℝ) n)) := by
    rw [hnext]
    exact abs_sum_coeff_le _ (fun t => (abs_character _ t).le) _ _ hbal_last _ hclose
  have hlog1 : 1 ≤ Real.log (N : ℝ) := by linarith
  have hlogpow : 1 ≤ Real.log (N : ℝ) ^ ell := one_le_pow₀ hlog1
  have hclosesize (t : History (n + 1)) : |(sizes t : ℝ) - (N : ℝ) * ν n t| ≤
      (N : ℝ) / Real.sqrt ((p : ℝ) * N) * Real.log (N : ℝ) ^ (ell + 1) := by
    have h1 := (hspec.estimates n hn).sizes t
    have h2 := hclose t
    have hTS' : T * sizeScale N (p : ℝ) n ≤ (N : ℝ) / Real.sqrt ((p : ℝ) * N) * 1 := by
      rw [sizeScale_eq N hNpos, mul_one, le_div_iff₀ hs]
      calc
        T * (betaScale N (p : ℝ) n * N) * Real.sqrt ((p : ℝ) * N) = (N : ℝ) * (T * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N))) := by
          ring
        _ ≤ (N : ℝ) * 1 := mul_le_mul_of_nonneg_left hTx hN0.le
        _ = N := mul_one _
    have htri := abs_sub_le (sizes t : ℝ) ((a.state n).sizes t : ℝ) ((N : ℝ) * ν n t)
    have hNs : 0 ≤ (N : ℝ) / Real.sqrt ((p : ℝ) * N) := by positivity
    have hpow : Real.log (N : ℝ) ^ ell + 1 ≤ Real.log (N : ℝ) ^ (ell + 1) := by
      rw [pow_succ]
      have h2 : Real.log (N : ℝ) ^ ell * 2 ≤ Real.log (N : ℝ) ^ ell * Real.log (N : ℝ) :=
        mul_le_mul_of_nonneg_left hlog (by linarith only [hlogpow])
      linarith only [h2, hlogpow]
    calc
      _ ≤ |(sizes t : ℝ) - (a.state n).sizes t| + |((a.state n).sizes t : ℝ) - N * ν n t| := htri
      _ ≤ (N : ℝ) / Real.sqrt ((p : ℝ) * N) * 1 +
          (N : ℝ) / Real.sqrt ((p : ℝ) * N) * Real.log (N : ℝ) ^ ell :=
        add_le_add (h2.trans hTS') h1
      _ = (N : ℝ) / Real.sqrt ((p : ℝ) * N) * (Real.log (N : ℝ) ^ ell + 1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow hNs
  refine
    { ref_lower := href_lower
      ref_upper := href_upper
      ref_pos := href_pos
      sizes_pos := hsizes_pos
      sizes_lower := hsizes_lower
      sizes_upper := hsizes_upper
      ref_support := href_support
      sizes_support := hsizes_support
      ref_residual := href_residual
      residual := hresidual
      perturbation := fun t => by
        have := hNνt t
        linarith [hTS]
      admissible := ?_
      imbalance := ?_
      xi_pos := ?_
      xi_le := ?_ }
  · intro s
    refine ⟨hclosesize, ?_, ?_⟩
    · intro r
      have hbal : (∑ t, historyMatrix s r t * ((a.state n).sizes t : ℝ)) = 0 :=
        symmetric_history_balance (a.state n) hsym s r
      have h := abs_sum_coeff_le (historyMatrix s r) (fun t => (abs_historyMatrix s r t).le)
        _ _ hbal _ hclose
      rw [hξN]
      exact h.trans hcard
    · exact himb.trans hdecision
  · rw [hξN]
    exact himb.trans hcard
  · unfold xiScale
    exact mul_pos (by positivity) hx0
  · calc
      xiScale N (p : ℝ) n T = ((Fintype.card (History (n + 1)) : ℝ) * T + 1) * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) := rfl
      _ ≤ 1 := hdT
      _ ≤ T := hT.le

end MajorityDynamics.Idealized.LinearResponse
