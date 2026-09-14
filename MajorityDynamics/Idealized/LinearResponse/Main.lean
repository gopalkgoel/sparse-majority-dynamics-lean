import MajorityDynamics.Idealized.LinearResponse.Bridge
import MajorityDynamics.Idealized.LinearResponse.Core
import MajorityDynamics.Idealized.LinearResponse.Expansion
import MajorityDynamics.Idealized.LinearResponse.Geometry
import MajorityDynamics.Idealized.LinearResponse.Gaussian
import MajorityDynamics.Idealized.LinearResponse.Reference
import MajorityDynamics.Idealized.LinearResponse.Smooth
import MajorityDynamics.Idealized.LinearResponse.Tilt

/-!
# Lemma E.4: the complete small-tilt response

`linear_response_spec` proves every clause of `lem:tilt-vs-linear-map` for every
process with the Theorem 5.2 specification; `linear_response` fixes the actual
selected exponent, and `linear_response_real` is the literal real-density,
integer-size statement with the constructed reference process.

Proof outline (paper §E.4). A.2 (`row_expansions`) expands the mass and the
first moment of the perturbed row law around the reference row law; the
different-trial tilt parameter is exactly `τβ₀σ` (`effectiveTilt_difference`).
Dividing (`Core.lean`) gives the reference conditional mean plus the reference
covariance acting on `τβ₀σ`; the first-order term of the denominator is
controlled through the actual perturbed mass (E.3 at the perturbed sizes,
`row_limits`) rather than through the unconditional binomial mean. The
reference covariance, means and split are identified with the universal
Gaussian quantities by E.3 at the solved tilt (`reference_row_data`) and the
Lipschitz bridge to `γ` (`gaussian_bridge`).
-/

noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators

namespace MajorityDynamics.Idealized.LinearResponse

open MajorityDynamics.Universal
open MajorityDynamics.Binomial (mass eventMass vector)
open MajorityDynamics.Idealized.RowLimits
open MajorityDynamics.Binomial.Approximation (Density scale tiltDifference Sizes)

theorem abs_log_div_le {a b m : ℝ} (ha : 0 < a) (hb : 0 < b) (hm : 0 < m) (hma : m ≤ a)
    (hmb : m ≤ b) : |Real.log (a / b)| ≤ |a - b| / m := by
  have hab : 0 < a / b := div_pos ha hb
  have h1 := Real.log_le_sub_one_of_pos hab
  have h2 := Real.one_sub_inv_le_log_of_pos hab
  have hb0 : b ≠ 0 := hb.ne'
  have ha0 : a ≠ 0 := ha.ne'
  have e1 : a / b - 1 = (a - b) / b := by rw [sub_div, div_self hb0]
  have e2 : 1 - (a / b)⁻¹ = (a - b) / a := by rw [inv_div, sub_div, div_self ha0]
  rw [e1] at h1
  rw [e2] at h2
  have hd1 : (a - b) / b ≤ |a - b| / m :=
    (div_le_div_of_nonneg_right (le_abs_self _) hb.le).trans
      (div_le_div_of_nonneg_left (abs_nonneg _) hm hmb)
  have hd2 : -(|a - b| / m) ≤ (a - b) / a := by
    have h3 : |a - b| / a ≤ |a - b| / m := div_le_div_of_nonneg_left (abs_nonneg _) hm hma
    have h4 : -|a - b| / a ≤ (a - b) / a := div_le_div_of_nonneg_right (neg_abs_le _) ha.le
    rw [neg_div] at h4
    linarith
  rw [abs_le]
  constructor <;> linarith

theorem conditionalCovariance_symm (n : ℕ) (s t u : History (n + 1)) :
    conditionalCovariance n s t u = conditionalCovariance n s u t := by
  rw [conditionalCovariance_entry, conditionalCovariance_entry]
  have h : ∀ x : Row (n + 1), x t * x u = x u * x t := fun x => mul_comm _ _
  simp only [h]
  ring

theorem lipschitz_const_mono {νmin v G : ℝ} (hνmin : 0 < νmin) (hv : νmin ≤ v) (hG : 0 ≤ G) :
    2 * Real.exp (G / v) / v ≤ 2 * Real.exp (G / νmin) / νmin := by
  apply div_le_div₀ (by positivity) _ hνmin hv
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (div_le_div_of_nonneg_left hG hνmin hv)) (by norm_num)

/-- `p / (β₀ √(pN)) ≤ √p`. -/
theorem p_div_beta_le_sqrt {N : ℕ} (hN : 0 < N) (p : ℝ) (hp : 0 < p) (n : ℕ)
    (hs1 : 1 ≤ Real.sqrt (p * N)) :
    p / (betaScale N p n * Real.sqrt (p * N)) ≤ Real.sqrt p := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsqrtN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  have hs : 0 < Real.sqrt (p * N) := lt_of_lt_of_le zero_lt_one hs1
  have hS₀eq : Real.sqrt (p * N) = Real.sqrt p * Real.sqrt N := Real.sqrt_mul hp.le N
  have h1 : Real.sqrt (p * N) / Real.sqrt N ≤ betaScale N p n * Real.sqrt (p * N) := by
    unfold betaScale
    rw [div_mul_eq_mul_div, ← pow_succ]
    exact div_le_div_of_nonneg_right (le_self_pow₀ hs1 (Nat.succ_ne_zero n)) hsqrtN.le
  have h2 : 0 < Real.sqrt (p * N) / Real.sqrt N := div_pos hs hsqrtN
  calc
    p / (betaScale N p n * Real.sqrt (p * N)) ≤ p / (Real.sqrt (p * N) / Real.sqrt N) :=
      div_le_div_of_nonneg_left hp.le h2 h1
    _ = Real.sqrt p := by
      rw [hS₀eq, div_div_eq_mul_div, mul_div_mul_right _ _ hsqrtN.ne', Real.div_sqrt]

/-! Algebraic normalizations with `V = S₀²`. -/

theorem E1_norm {C M S₀ l τ β₀ V : ℝ} (hτ : τ ≠ 0) (hβ : β₀ ≠ 0) (hS : S₀ ≠ 0)
    (hVS : V = S₀ * S₀) : C * M * S₀ * l / (τ * β₀ * V) = C * (M * l / (τ * (β₀ * S₀))) := by
  subst hVS
  field_simp

theorem Em_norm {A S₀ τ β₀ V : ℝ} (hτ : τ ≠ 0) (hβ : β₀ ≠ 0) (hS : S₀ ≠ 0)
    (hVS : V = S₀ * S₀) : A * S₀ / (τ * β₀ * V) = A / (τ * (β₀ * S₀)) := by
  subst hVS
  field_simp

theorem sq_V_eq {T R β₀ S₀ V l : ℝ} (hVS : V = S₀ * S₀) :
    (T * β₀ * R) ^ 2 * V * l ^ 2 = T ^ 2 * R ^ 2 * (β₀ * S₀) ^ 2 * l ^ 2 := by
  subst hVS
  ring

theorem sq_S_eq {A S₀ V : ℝ} (hVS : V = S₀ * S₀) : A * S₀ * (A * S₀) = A ^ 2 * V := by
  subst hVS
  ring

theorem child_norm_eq {A K τ β₀ S₀ V : ℝ} (hVS : V = S₀ * S₀) :
    A * K * (τ * β₀ * V) = K * (τ * (β₀ * S₀)) * (A * S₀) := by
  subst hVS
  ring

set_option maxHeartbeats 12000000 in
theorem linear_response_spec : LinearResponseSpecTheorem := by
  intro θ hθlo hθhi n hk T R hT hR ell hell
  have hT0 : 0 < T := by linarith
  have hDlt := level_succ_lt_horizon hk
  have hκ := responseRate_pos hθlo hθhi hk
  let : Nonempty (History (n + 1)) := ⟨(bits _).symm (fun _ => false)⟩
  obtain ⟨νmin, hνmin, hνle₀⟩ :=
    finite_common_positive (fun t : History (n + 1) => ν n t) (ν_positive n)
  have hνle : ∀ t, νmin ≤ ν n t := fun t => hνle₀ t
  obtain ⟨Bν, hBν, hνB₀⟩ := finite_abs_bound (fun t : History (n + 1) => ν n t)
  have hνB : ∀ t, ν n t ≤ Bν := fun t => (le_abs_self _).trans (hνB₀ t)
  obtain ⟨G₀, hG₀, hgI, hgJ, hcovG⟩ := universal_bounds n
  have hnondeg := universal_nondegeneracy n
  have hφ : 0 < φStar n := hnondeg.probability_pos
  have hφ1 : φStar n ≤ 1 / 4 := hnondeg.probability_le_quarter
  obtain ⟨L, R₀, hR₀, hγR, C₀, hC₀, N₁, hN₁, href⟩ :=
    reference_row_data θ T hθlo hθhi hT n ell hell
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ, G = R₀ + 8 * T + Bν * T * R := ⟨_, rfl⟩
  have hBTR : 0 ≤ Bν * T * R := by positivity
  have hG : 0 < G := by rw [hGdef]; linarith
  have hR₀G : R₀ ≤ G := by rw [hGdef]; linarith
  obtain ⟨K, hK, hbridge⟩ := gaussian_bridge n G hG.le
  obtain ⟨_, hrow⟩ := row_limits n
  obtain ⟨L_a, hrow⟩ := hrow (ell + 1) (by omega)
  obtain ⟨_, hrow⟩ := hrow T G hT hG
  obtain ⟨C_a, hC_a, N_a, hrow⟩ := hrow θ hθlo hθhi
  obtain ⟨Lp₀, hLp₀def⟩ : ∃ x : ℝ, x = 2 * Real.exp (R₀ / νmin) / νmin := ⟨_, rfl⟩
  obtain ⟨LpG, hLpGdef⟩ : ∃ x : ℝ, x = 2 * Real.exp (G / νmin) / νmin := ⟨_, rfl⟩
  have hLp₀ : 0 < Lp₀ := by rw [hLp₀def]; positivity
  have hLpG : 0 < LpG := by rw [hLpGdef]; positivity
  have hinvν : 0 ≤ 2 / νmin := by positivity
  obtain ⟨T₁, hT₁def⟩ : ∃ x : ℝ,
      x = T + 2 + 2 / νmin + 2 * Bν + T * R + Lp₀ * R₀ + LpG * G := ⟨_, rfl⟩
  have hTR : 0 ≤ T * R := by positivity
  have hLpR₀ : 0 ≤ Lp₀ * R₀ := by positivity
  have hLpGG : 0 ≤ LpG * G := by positivity
  have hT₁ : 1 < T₁ := by rw [hT₁def]; linarith
  have hTT₁ : T ≤ T₁ := by rw [hT₁def]; linarith
  obtain ⟨C_A, hC_A, N_A, _, hexp⟩ := row_expansions θ T₁ hθlo hθhi hT₁ n
  obtain ⟨d, hddef⟩ : ∃ x : ℝ, x = (Fintype.card (History (n + 1)) : ℝ) := ⟨_, rfl⟩
  have hd0 : 0 ≤ d := by rw [hddef]; positivity
  have hd1 : 1 ≤ d := by rw [hddef]; exact_mod_cast Fintype.card_pos
  -- derived constants
  obtain ⟨Kr, hKrdef⟩ : ∃ x : ℝ, x = 1 / (φStar n / 2) + 1 / (φStar n / 2) ^ 2 := ⟨_, rfl⟩
  have hKr : 0 ≤ Kr := by rw [hKrdef]; positivity
  obtain ⟨Kec, hKecdef⟩ : ∃ x : ℝ, x = C₀ + K * C₀ := ⟨_, rfl⟩
  have hKec : 0 ≤ Kec := by rw [hKecdef]; positivity
  obtain ⟨Ker, hKerdef⟩ : ∃ x : ℝ, x = C₀ + Kr * (K * C₀) := ⟨_, rfl⟩
  have hKer : 0 ≤ Ker := by rw [hKerdef]; positivity
  obtain ⟨Kg, hKgdef⟩ : ∃ x : ℝ, x = 8 * T + Bν * T * R := ⟨_, rfl⟩
  have hKg : 0 ≤ Kg := by rw [hKgdef]; positivity
  obtain ⟨Ku, hKudef⟩ : ∃ x : ℝ, x = C_a * (d * T + 2) + K * Kg + C₀ := ⟨_, rfl⟩
  have hKu : 0 ≤ Ku := by rw [hKudef]; positivity
  obtain ⟨Kus, hKusdef⟩ : ∃ x : ℝ, x = C_a * (d * T + 2) + Kr * (K * Kg) + C₀ := ⟨_, rfl⟩
  have hKus : 0 ≤ Kus := by rw [hKusdef]; positivity
  obtain ⟨KeP, hKePdef⟩ : ∃ x : ℝ, x = C_A * (1 + T ^ 2 * R ^ 2) := ⟨_, rfl⟩
  have hKeP : 0 ≤ KeP := by rw [hKePdef]; positivity
  obtain ⟨KeM, hKeMdef⟩ : ∃ x : ℝ, x = C_A * T * (1 + T ^ 2 * R ^ 2) := ⟨_, rfl⟩
  have hKeM : 0 ≤ KeM := by rw [hKeMdef]; positivity
  obtain ⟨Q, hQdef⟩ : ∃ x : ℝ, x = 16 * (G₀ + 1) ^ 2 / φStar n ^ 2 := ⟨_, rfl⟩
  have hQ : 0 ≤ Q := by rw [hQdef]; positivity
  obtain ⟨Q₂, hQ₂def⟩ : ∃ x : ℝ, x = (G₀ + 1) ^ 2 := ⟨_, rfl⟩
  have hQ₂ : 0 ≤ Q₂ := by rw [hQ₂def]; positivity
  obtain ⟨Kbig, hKbigdef⟩ : ∃ x : ℝ,
      x = Kec + Ker + Ku + Kus + (Ku + 2 * Kus) + KeP + K * Kg + K * (Kg + C₀) + 1 := ⟨_, rfl⟩
  have hKbig : 0 < Kbig := by rw [hKbigdef]; positivity
  have hKKg : 0 ≤ K * Kg := mul_nonneg hK hKg
  have hKKgC : 0 ≤ K * (Kg + C₀) := mul_nonneg hK (add_nonneg hKg hC₀.le)
  have hKbig_ge : Kec ≤ Kbig ∧ Ker ≤ Kbig ∧ Ku ≤ Kbig ∧ Kus ≤ Kbig ∧ Ku + 2 * Kus ≤ Kbig ∧
      KeP ≤ Kbig ∧ K * Kg ≤ Kbig ∧ K * (Kg + C₀) ≤ Kbig := by
    rw [hKbigdef]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  obtain ⟨Cmean, hCmeandef⟩ : ∃ x : ℝ, x = d * R * Kec + 4 / φStar n *
      (KeM + (Ku + KeP) * (d * R * (G₀ + 1)) + (G₀ + 1) * KeM + KeP * (d * R * (G₀ + 1))) :=
    ⟨_, rfl⟩
  have hCmean : 0 ≤ Cmean := by rw [hCmeandef]; positivity
  obtain ⟨Csplit, hCsplitdef⟩ : ∃ x : ℝ, x = d * (R * (2 * Kec)) + d * (R * (2 * G₀)) * Ker +
      4 / φStar n * (KeM + (Ku + KeP) * (d * (R * (2 * (G₀ + 1)))) + KeM +
        KeP * (d * (R * (2 * (G₀ + 1))))) := ⟨_, rfl⟩
  have hCsplit : 0 ≤ Csplit := by rw [hCsplitdef]; positivity
  obtain ⟨Cchild, hCchilddef⟩ : ∃ x : ℝ, x = d * (R * (Q + Q₂)) +
      8 / φStar n ^ 2 * (KeM + d * (R * (Q + Q₂)) + (G₀ + 1) * KeM + d * (R * (Q + Q₂))) :=
    ⟨_, rfl⟩
  have hCchild : 0 ≤ Cchild := by rw [hCchilddef]; positivity
  obtain ⟨C, hCdef⟩ : ∃ x : ℝ, x = LpG * G + Cmean + Csplit + Cchild + 1 := ⟨_, rfl⟩
  have hCpos : 0 < C := by rw [hCdef]; positivity
  refine ⟨C, hCpos, ?_⟩
  -- the eventual statement
  have hev : ∀ᶠ N : ℕ in atTop, ∀ p : Binomial.Probability, Density θ T N p →
      ∀ a : Process.Data, Process.Specification N p (responseHorizon θ) ell a →
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ sizes : Local.Sizes n,
        (∀ t, |(sizes t : ℝ) - ((a.state n).sizes t : ℝ)| ≤ T * sizeScale N (p : ℝ) n) →
      ∀ s : History (n + 1), ResponseConclusion N p a n sizes s τ R C (responseRate θ n) := by
    filter_upwards [eventually_geometry θ T hθlo hθhi hT n ell (T + 1) (by linarith) hk,
      eventually_basic θ T hθlo hθhi hT,
      eventually_small θ T hθlo hθhi hT n (L + L_a + 5) hk,
      eventually_rpow_neg_le (responseRate θ n) (φStar n ^ 2 / 32 / Kbig) hκ (by positivity),
      eventually_ge_atTop N₁, eventually_ge_atTop N_a, eventually_ge_atTop N_A]
      with N hgeo hbasic hsmall hΘsmall hNN₁ hNN_a hNN_A
    intro p hp a hspec τ hτ₁ hτ₂ sizes hclose s
    obtain ⟨hNpos, hlog2, hbasic⟩ := hbasic
    obtain ⟨hs1, _, hp8⟩ := hbasic p hp
    obtain ⟨hTx, hgeo⟩ := hgeo p hp
    have hfacts := hgeo a (responseHorizon θ) hspec hDlt sizes hclose
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hNpos
    have hp0 : 0 < (p : ℝ) := p.property.1
    have hpN : 0 < (p : ℝ) * N := mul_pos hp0 hN0
    have hS₀ : 0 < Real.sqrt ((p : ℝ) * N) := Real.sqrt_pos.mpr hpN
    have hVS : (p : ℝ) * N = Real.sqrt ((p : ℝ) * N) * Real.sqrt ((p : ℝ) * N) :=
      (Real.mul_self_sqrt hpN.le).symm
    have hβ₀ : 0 < betaScale N (p : ℝ) n :=
      div_pos (pow_pos hS₀ n) (Real.sqrt_pos.mpr hN0)
    have hx : 0 < betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N) := mul_pos hβ₀ hS₀
    have hτ0 : 0 < τ := lt_of_lt_of_le (inv_pos.mpr hT0) hτ₁
    have hb₀ : 0 < τ * betaScale N (p : ℝ) n := mul_pos hτ0 hβ₀
    have hlog1 : 1 ≤ Real.log (N : ℝ) := by linarith [hlog2]
    have hlog0 : 0 ≤ Real.log (N : ℝ) := by linarith
    have hΘ0 : 0 ≤ (N : ℝ) ^ (-responseRate θ n) := Real.rpow_nonneg hN0.le _
    have hΘ1 : (N : ℝ) ^ (-responseRate θ n) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hNpos) (by linarith)
    -- the budget at every exponent `a ≤ L + L_a + 5`
    have hbud := hsmall p hp
    have hbudget : ∀ m : ℕ, m ≤ L + L_a + 5 →
        Real.sqrt (p : ℝ) * Real.log (N : ℝ) ^ m ≤ (N : ℝ) ^ (-responseRate θ n) ∧
        (p : ℝ) * Real.log (N : ℝ) ^ m ≤ (N : ℝ) ^ (-responseRate θ n) ∧
        Real.log (N : ℝ) ^ m / Real.sqrt ((p : ℝ) * N) ≤ (N : ℝ) ^ (-responseRate θ n) ∧
        betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N) * Real.log (N : ℝ) ^ m ≤
          (N : ℝ) ^ (-responseRate θ n) := by
      intro m hm
      have hmono : Real.log (N : ℝ) ^ m ≤ Real.log (N : ℝ) ^ (L + L_a + 5) :=
        pow_le_pow_right₀ hlog1 hm
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact (mul_le_mul_of_nonneg_left hmono (Real.sqrt_nonneg _)).trans hbud.1
      · exact (mul_le_mul_of_nonneg_left hmono hp0.le).trans hbud.2.1
      · exact (div_le_div_of_nonneg_right hmono hS₀.le).trans hbud.2.2.1
      · exact (mul_le_mul_of_nonneg_left hmono hx.le).trans hbud.2.2.2
    have hx1 : betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N) ≤ (N : ℝ) ^ (-responseRate θ n) := by
      have := (hbudget 0 (by omega)).2.2.2
      simpa only [pow_zero, mul_one] using this
    have hxle1 : betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N) ≤ 1 := hx1.trans hΘ1
    have hΘKbig : Kbig * (N : ℝ) ^ (-responseRate θ n) ≤ φStar n ^ 2 / 32 := by
      have h := mul_le_mul_of_nonneg_left hΘsmall hKbig.le
      have h2 : Kbig * (φStar n ^ 2 / 32 / Kbig) = φStar n ^ 2 / 32 := by
        rw [mul_comm]
        exact div_mul_cancel₀ _ hKbig.ne'
      rw [h2] at h
      exact h
    have hφsq : φStar n ^ 2 / 32 ≤ φStar n / 16 := by
      have h := mul_le_mul_of_nonneg_left hφ1 hφ.le
      linarith only [h, hφ]
    have hpiece : ∀ c : ℝ, 0 ≤ c → c ≤ Kbig →
        c * (N : ℝ) ^ (-responseRate θ n) ≤ φStar n ^ 2 / 32 := fun c _ hc =>
      (mul_le_mul_of_nonneg_right hc hΘ0).trans hΘKbig
    -- shorthand facts about sizes
    have hñpos : ∀ t, 0 < (a.state n).sizes t := hfacts.ref_pos
    have hñs : (0 : ℝ) < (a.state n).sizes s := by exact_mod_cast hñpos s
    have hres_ref : ∀ t, 0 < residual (p : ℝ) (a.state n).sizes (a.state n).sizes s t := by
      intro t
      have := hfacts.ref_residual s t
      have := ν_positive n t
      have : (0 : ℝ) < N * ν n t / 8 := by positivity
      linarith
    have hres_new : ∀ t, 0 < residual (p : ℝ) (a.state n).sizes sizes s t := by
      intro t
      have := hfacts.residual s t
      have := ν_positive n t
      have : (0 : ℝ) < N * ν n t / 8 := by positivity
      linarith
    have htr_ref : ∀ t, 0 < Local.trials (a.state n).sizes s t := by
      intro t
      obtain ⟨_, h⟩ := trials_gt_center p (a.state n).sizes (a.state n).sizes s t (hres_ref t)
      have hc : 0 ≤ (p : ℝ) * ((a.state n).sizes t : ℝ) := by positivity
      exact_mod_cast hc.trans_lt h
    have htr_new : ∀ t, 0 < Local.trials sizes s t := by
      intro t
      obtain ⟨_, h⟩ := trials_gt_center p (a.state n).sizes sizes s t (hres_new t)
      have hc : 0 ≤ (p : ℝ) * ((a.state n).sizes t : ℝ) := by positivity
      exact_mod_cast hc.trans_lt h
    have hcenter_pos : ∀ t, 0 < (p : ℝ) * ((a.state n).sizes t : ℝ) := fun t =>
      mul_pos hp0 (by exact_mod_cast hñpos t)
    have hhist_new : (Local.historySupport sizes s).Nonempty :=
      Process.historySupport_nonempty _ hfacts.sizes_support s
    -- reference row data
    obtain ⟨σr, hσrR, hσrγ, htilt, hest⟩ :=
      href N hNN₁ p hp a (responseHorizon θ) hspec hDlt s
    have hσrG : ∀ t, |σr t| ≤ G := fun t => (hσrR t).trans hR₀G
    have hγG : ∀ t, |γ n s t| ≤ G := fun t => (hγR s t).trans hR₀G
    have hρ0 : 0 ≤ Real.log (N : ℝ) ^ L / scale N p := by
      unfold scale
      positivity
    have hρ : Real.log (N : ℝ) ^ L / scale N p ≤ (N : ℝ) ^ (-responseRate θ n) :=
      (hbudget L (by omega)).2.2.1
    have hδ0 : 0 ≤ C₀ * (Real.log (N : ℝ) ^ L / scale N p) := mul_nonneg hC₀.le hρ0
    obtain ⟨hbM, hbm, hbc, hbMJ, hbmJ⟩ := hbridge s σr (γ n s) hσrG hγG _ hδ0 hσrγ
    -- ec bounds every reference-to-universal discrepancy
    have hec : Kec * (N : ℝ) ^ (-responseRate θ n) ≤ φStar n ^ 2 / 32 :=
      hpiece Kec hKec hKbig_ge.1
    have hecΘ : C₀ * (Real.log (N : ℝ) ^ L / scale N p) +
        K * (C₀ * (Real.log (N : ℝ) ^ L / scale N p)) ≤ Kec * (N : ℝ) ^ (-responseRate θ n) := by
      rw [hKecdef]
      have := mul_le_mul_of_nonneg_left hρ (by positivity : 0 ≤ C₀ + K * C₀)
      linarith
    have hecφ : C₀ * (Real.log (N : ℝ) ^ L / scale N p) +
        K * (C₀ * (Real.log (N : ℝ) ^ L / scale N p)) ≤ φStar n / 16 :=
      hecΘ.trans (hec.trans hφsq)
    -- reference masses
    have hD_eq : binomialMass N p (a.state n).sizes s (Local.historySupport (a.state n).sizes s) σr =
        historyMass (a.state n).sizes s (a.tilt n s) := binomialMass_eq _ _ _ _ _ _ htilt _
    have hgMγ : φStar n ≤ gaussianMass (γ n s) (historyEvent s) := hnondeg.history s
    have hgM1 : gaussianMass σr (historyEvent s) ≤ 1 := by
      have := gaussianMass_abs_le_one σr (historyEvent s)
      exact (le_abs_self _).trans this
    have hDlo : φStar n / 2 ≤ historyMass (a.state n).sizes s (a.tilt n s) := by
      have h1 := hest.history_probability
      rw [hD_eq] at h1
      obtain ⟨h1a, h1b⟩ := abs_le.mp h1
      obtain ⟨h2a, h2b⟩ := abs_le.mp hbM
      linarith [h1a, h1b, h2a, h2b]
    have hDpos : 0 < historyMass (a.state n).sizes s (a.tilt n s) := by linarith
    have hDhi : historyMass (a.state n).sizes s (a.tilt n s) ≤ 1 + φStar n / 16 := by
      have h1 := hest.history_probability
      rw [hD_eq] at h1
      obtain ⟨h1a, h1b⟩ := abs_le.mp h1
      have h3 : 0 ≤ K * (C₀ * (Real.log (N : ℝ) ^ L / scale N p)) := mul_nonneg hK hδ0
      linarith [h1a, h1b]
    have hDhi2 : historyMass (a.state n).sizes s (a.tilt n s) ≤ 2 := by linarith
    have hgMσr : φStar n / 2 ≤ gaussianMass σr (historyEvent s) := by
      obtain ⟨h2a, h2b⟩ := abs_le.mp hbM
      linarith [h2a, h2b]
    -- reference split
    have hsplit_ref : ∀ b, |splitProbability (a.state n).sizes s b (a.tilt n s) -
        ν (n + 1) (append s b) / ν n s| ≤ Ker * (N : ℝ) ^ (-responseRate θ n) := by
      intro b
      have h1 := hest.split_probability b
      rw [shiftedChildEvent_zero, binomialSplit_eq _ _ _ _ _ _ htilt] at h1
      have hgMJγ1 : |gaussianMass (γ n s) (childEvent s b)| ≤ 1 := gaussianMass_abs_le_one _ _
      have hratio := ratio_error (by positivity : 0 < φStar n / 2) hgMσr
        (by linarith : φStar n / 2 ≤ gaussianMass (γ n s) (historyEvent s)) hgMJγ1 (hbMJ b) hbM
      rw [universal_split_ratio] at hratio
      have htri := abs_sub_le (splitProbability (a.state n).sizes s b (a.tilt n s))
        (gaussianMass σr (childEvent s b) / gaussianMass σr (historyEvent s))
        (ν (n + 1) (append s b) / ν n s)
      have hKr' : (1 / (φStar n / 2) + 1 / (φStar n / 2) ^ 2) = Kr := hKrdef.symm
      rw [hKr'] at hratio
      rw [hKerdef]
      have := mul_le_mul_of_nonneg_left hρ (by positivity : 0 ≤ C₀ + Kr * (K * C₀))
      linarith only [htri, h1, hratio, this]
    have hr_bounds : ∀ b, φStar n ≤ ν (n + 1) (append s b) / ν n s ∧
        ν (n + 1) (append s b) / ν n s ≤ 1 - φStar n := by
      intro b
      rw [← universal_split_eq]
      exact hnondeg.split s b
    have herφ : Ker * (N : ℝ) ^ (-responseRate θ n) ≤ φStar n / 16 :=
      (hpiece Ker hKer hKbig_ge.2.1).trans hφsq
    have hDJ_eq : ∀ b, childMass (a.state n).sizes s b (a.tilt n s) =
        historyMass (a.state n).sizes s (a.tilt n s) *
          splitProbability (a.state n).sizes s b (a.tilt n s) := by
      intro b
      unfold splitProbability
      exact ((div_mul_cancel₀ _ hDpos.ne').symm.trans (mul_comm _ _))
    have hDJlo : ∀ b, φStar n ^ 2 / 4 ≤ childMass (a.state n).sizes s b (a.tilt n s) := by
      intro b
      rw [hDJ_eq b]
      obtain ⟨h1a, h1b⟩ := abs_le.mp (hsplit_ref b)
      have h2 := (hr_bounds b).1
      have hsp : φStar n / 2 ≤ splitProbability (a.state n).sizes s b (a.tilt n s) := by
        linarith [herφ, h1a, h1b]
      have h3 := mul_le_mul hDlo hsp (by positivity) hDpos.le
      linarith only [h3]
    have hDJpos : ∀ b, 0 < childMass (a.state n).sizes s b (a.tilt n s) := fun b =>
      lt_of_lt_of_le (by positivity) (hDJlo b)
    have hDJle : ∀ b, childMass (a.state n).sizes s b (a.tilt n s) ≤
        historyMass (a.state n).sizes s (a.tilt n s) := fun b =>
      eventMass_mono _ _ (Local.childSupport_subset _ s b)
    -- reference means and covariance
    have hμI : ∀ t, |cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
        (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) t /
          historyMass (a.state n).sizes s (a.tilt n s) / Real.sqrt ((p : ℝ) * N) -
          ∫ x, x t ∂historyLaw n s| ≤ Kec * (N : ℝ) ^ (-responseRate θ n) := by
      intro t
      have h1 := hest.history_mean t
      rw [binomialMean_eq _ _ _ _ _ _ htilt _ (center p (a.state n).sizes) t hDpos.ne'] at h1
      have hc : center p (a.state n).sizes t - (p : ℝ) * (a.state n).sizes t = 0 := by
        unfold center
        ring
      have hrew : cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
          (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) t /
            eventMass (Local.trials (a.state n).sizes s) (a.tilt n s)
              (Local.historySupport (a.state n).sizes s) +
            center p (a.state n).sizes t - (p : ℝ) * (a.state n).sizes t =
          cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
            (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) t /
            historyMass (a.state n).sizes s (a.tilt n s) := by
        unfold historyMass
        linarith
      rw [hrew] at h1
      rw [← gaussianMean_universal_history]
      have htri := abs_sub_le (cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
        (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) t /
          historyMass (a.state n).sizes s (a.tilt n s) / Real.sqrt ((p : ℝ) * N))
        (gaussianMean σr (historyEvent s) t) (gaussianMean (γ n s) (historyEvent s) t)
      linarith [hbm t]
    have hμJ : ∀ b t, |cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
        (Local.childSupport (a.state n).sizes s b) (center p (a.state n).sizes) t /
          childMass (a.state n).sizes s b (a.tilt n s) / Real.sqrt ((p : ℝ) * N) -
          ∫ x, x t ∂childLaw n s b| ≤ Kec * (N : ℝ) ^ (-responseRate θ n) := by
      intro b t
      have h1 := hest.child_mean b t
      rw [shiftedChildEvent_zero,
        binomialMean_eq _ _ _ _ _ _ htilt _ (center p (a.state n).sizes) t (hDJpos b).ne'] at h1
      have hrew : cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
          (Local.childSupport (a.state n).sizes s b) (center p (a.state n).sizes) t /
            eventMass (Local.trials (a.state n).sizes s) (a.tilt n s)
              (Local.childSupport (a.state n).sizes s b) +
            center p (a.state n).sizes t - (p : ℝ) * (a.state n).sizes t =
          cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
            (Local.childSupport (a.state n).sizes s b) (center p (a.state n).sizes) t /
            childMass (a.state n).sizes s b (a.tilt n s) := by
        unfold childMass center
        ring
      rw [hrew] at h1
      rw [← gaussianMean_universal_child]
      have htri := abs_sub_le (cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
        (Local.childSupport (a.state n).sizes s b) (center p (a.state n).sizes) t /
          childMass (a.state n).sizes s b (a.tilt n s) / Real.sqrt ((p : ℝ) * N))
        (gaussianMean σr (childEvent s b) t) (gaussianMean (γ n s) (childEvent s b) t)
      linarith [hbmJ b t]
    have hcov : ∀ i t, |(csecond (Local.trials (a.state n).sizes s) (a.tilt n s)
        (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) i t /
          historyMass (a.state n).sizes s (a.tilt n s) -
        cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
          (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) i /
            historyMass (a.state n).sizes s (a.tilt n s) *
          (cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
            (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) t /
            historyMass (a.state n).sizes s (a.tilt n s))) / ((p : ℝ) * N) -
        conditionalCovariance n s t i| ≤ Kec * (N : ℝ) ^ (-responseRate θ n) := by
      intro i t
      have h1 := hest.covariance i t
      rw [binomialCovariance_eq _ _ _ _ _ _ htilt _ (center p (a.state n).sizes) i t hDpos.ne'] at h1
      have hsym : conditionalCovariance n s t i = gaussianCovariance (γ n s) (historyEvent s) i t := by
        rw [conditionalCovariance_symm, gaussianCovariance_universal]
      rw [hsym]
      have htri := abs_sub_le ((csecond (Local.trials (a.state n).sizes s) (a.tilt n s)
        (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) i t /
          eventMass (Local.trials (a.state n).sizes s) (a.tilt n s)
            (Local.historySupport (a.state n).sizes s) -
        cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
          (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) i /
            eventMass (Local.trials (a.state n).sizes s) (a.tilt n s)
              (Local.historySupport (a.state n).sizes s) *
          (cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
            (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) t /
            eventMass (Local.trials (a.state n).sizes s) (a.tilt n s)
              (Local.historySupport (a.state n).sizes s))) / ((p : ℝ) * N))
        (gaussianCovariance σr (historyEvent s) i t) (gaussianCovariance (γ n s) (historyEvent s) i t)
      have := hbc i t
      unfold historyMass
      linarith
    -- the solved row: `m̃[s,t]/ñ[s]` is the reference conditional mean
    have hsolves : ∀ t, (a.state n).edges s t / ((a.state n).sizes s : ℝ) =
        historyMean (a.state n).sizes s (a.tilt n s) t := by
      intro t
      have h := (hspec.solvable n hDlt).solves s t
      rw [div_eq_iff hñs.ne', historyMean_eq_rowMean, mul_comm]
      exact h.symm
    -- per-σ facts
    have hgtilt : ∀ t, a.tilt n s t = Idealized.logitTilt N p (σr t) (ν n t) := fun t =>
      (congrFun htilt t).symm
    -- residual ratio bound
    have hlogratio : ∀ t, |Real.log (residual (p : ℝ) (a.state n).sizes (a.state n).sizes s t /
        residual (p : ℝ) (a.state n).sizes sizes s t)| ≤
        8 * T * betaScale N (p : ℝ) n / ν n t := by
      intro t
      have hν := ν_positive n t
      have hm : (0 : ℝ) < N * ν n t / 8 := by positivity
      have h := abs_log_div_le (hres_ref t) (hres_new t) hm (hfacts.ref_residual s t)
        (hfacts.residual s t)
      refine h.trans ?_
      rw [residual_sub, div_le_div_iff₀ hm hν]
      have h2 : |((a.state n).sizes t : ℝ) - sizes t| ≤ T * sizeScale N (p : ℝ) n := by
        rw [abs_sub_comm]
        exact hclose t
      rw [sizeScale_eq N hNpos] at h2
      have h3 := mul_le_mul_of_nonneg_right h2 hν.le
      linarith only [h3]
    -- the effective tilt as a bounded logit tilt
    have hgbound : ∀ (σ : Row (n + 1)), (∀ t, |σ t| ≤ R) → ∀ t,
        |ν n t * Real.sqrt ((p : ℝ) * N) *
          (Real.log (residual (p : ℝ) (a.state n).sizes (a.state n).sizes s t /
            residual (p : ℝ) (a.state n).sizes sizes s t) +
            τ * betaScale N (p : ℝ) n * σ t)| ≤
          Kg * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) := by
      intro σ hσ t
      have hν := ν_positive n t
      have hν0 : ν n t ≠ 0 := hν.ne'
      rw [abs_mul, abs_of_pos (mul_pos hν hS₀)]
      have h1 := hlogratio t
      have h2 : |τ * betaScale N (p : ℝ) n * σ t| ≤ T * betaScale N (p : ℝ) n * R := by
        rw [abs_mul, abs_mul, abs_of_pos hτ0, abs_of_pos hβ₀]
        have hτβ : τ * betaScale N (p : ℝ) n ≤ T * betaScale N (p : ℝ) n :=
          mul_le_mul_of_nonneg_right hτ₂ hβ₀.le
        calc
          τ * betaScale N (p : ℝ) n * |σ t| ≤ T * betaScale N (p : ℝ) n * |σ t| :=
            mul_le_mul_of_nonneg_right hτβ (abs_nonneg _)
          _ ≤ T * betaScale N (p : ℝ) n * R :=
            mul_le_mul_of_nonneg_left (hσ t) (by positivity)
      have htri := abs_add_le (Real.log (residual (p : ℝ) (a.state n).sizes (a.state n).sizes s t /
        residual (p : ℝ) (a.state n).sizes sizes s t)) (τ * betaScale N (p : ℝ) n * σ t)
      have hνB' := hνB t
      rw [hKgdef]
      have h3 : ν n t * Real.sqrt ((p : ℝ) * N) * (8 * T * betaScale N (p : ℝ) n / ν n t) =
          8 * T * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) := by
        field_simp
      have h4 : ν n t * Real.sqrt ((p : ℝ) * N) * (T * betaScale N (p : ℝ) n * R) ≤
          Bν * T * R * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) := by
        have := mul_le_mul_of_nonneg_right hνB' (by positivity :
          0 ≤ Real.sqrt ((p : ℝ) * N) * (T * betaScale N (p : ℝ) n * R))
        linarith only [this]
      calc
        ν n t * Real.sqrt ((p : ℝ) * N) *
            |Real.log (residual (p : ℝ) (a.state n).sizes (a.state n).sizes s t /
              residual (p : ℝ) (a.state n).sizes sizes s t) + τ * betaScale N (p : ℝ) n * σ t| ≤
            ν n t * Real.sqrt ((p : ℝ) * N) *
            (8 * T * betaScale N (p : ℝ) n / ν n t + T * betaScale N (p : ℝ) n * R) :=
          mul_le_mul_of_nonneg_left (htri.trans (add_le_add h1 h2)) (by positivity)
        _ = ν n t * Real.sqrt ((p : ℝ) * N) * (8 * T * betaScale N (p : ℝ) n / ν n t) +
            ν n t * Real.sqrt ((p : ℝ) * N) * (T * betaScale N (p : ℝ) n * R) := by ring
        _ ≤ _ := by rw [h3]; linarith
    -- Gaussian parameter of the effective tilt
    have hgrow : ∀ (σ : Row (n + 1)), (∀ t, |σ t| ≤ R) →
        ∃ g : Row (n + 1), rowTilt N p g = processEffectiveTilt N p a n sizes s τ σ ∧
          (∀ t, |g t - σr t| ≤ Kg * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N))) ∧
          (∀ t, |g t| ≤ G) := by
      intro σ hσ
      refine ⟨WithLp.toLp 2 (fun t => σr t + ν n t * Real.sqrt ((p : ℝ) * N) *
        (Real.log (residual (p : ℝ) (a.state n).sizes (a.state n).sizes s t /
          residual (p : ℝ) (a.state n).sizes sizes s t) + τ * betaScale N (p : ℝ) n * σ t)),
        ?_, ?_, ?_⟩
      · funext t
        exact (effectiveTilt_eq_logitTilt N p (a.state n).sizes (a.tilt n s) sizes s τ σ t (σr t)
          (ν_positive n t) hS₀ (hgtilt t)).symm
      · intro t
        show |σr t + ν n t * Real.sqrt ((p : ℝ) * N) * _ - σr t| ≤ _
        rw [add_sub_cancel_left]
        exact hgbound σ hσ t
      · intro t
        show |σr t + ν n t * Real.sqrt ((p : ℝ) * N) * _| ≤ G
        have h := hgbound σ hσ t
        have hKgx : Kg * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) ≤ Kg :=
          mul_le_of_le_one_right hKg hxle1
        have := abs_add_le (σr t) (ν n t * Real.sqrt ((p : ℝ) * N) *
          (Real.log (residual (p : ℝ) (a.state n).sizes (a.state n).sizes s t /
            residual (p : ℝ) (a.state n).sizes sizes s t) + τ * betaScale N (p : ℝ) n * σ t))
        rw [hGdef]
        linarith [hσrR t, hKgdef]
    -- admissibility of the perturbed sizes and E.3 at the actual tilt
    have hadm := hfacts.admissible s
    have hξ : 0 < xiScale N (p : ℝ) n T := hfacts.xi_pos
    have hξT : xiScale N (p : ℝ) n T ≤ T := hfacts.xi_le
    have hE3 := (hrow N hNN_a p hp.1 hp.2 (xiScale N (p : ℝ) n T) hξ hξT s sizes hadm).2
    have hε_a : error L_a N p (xiScale N (p : ℝ) n T) ≤
        (d * T + 2) * (N : ℝ) ^ (-responseRate θ n) := by
      unfold error xiScale
      rw [← hddef]
      have h1 := (hbudget L_a (by omega)).2.2.1
      have h2 := mul_le_mul_of_nonneg_left hx1 (by positivity : 0 ≤ d * T + 1)
      linarith
    -- the A.2 expansions
    have hSizes : Sizes T₁ N (a.state n).sizes := by
      intro t
      have hν := ν_positive n t
      have hl := hfacts.ref_lower t
      have hu := hfacts.ref_upper t
      have hνl := hνle t
      have hνu := hνB t
      constructor
      · have hT₁inv : T₁⁻¹ ≤ νmin / 2 := by
          rw [inv_le_comm₀ (by linarith) (by positivity), hT₁def]
          have : 2 / νmin = (νmin / 2)⁻¹ := by
            rw [inv_div]
          linarith
        have h1 := mul_le_mul_of_nonneg_right hT₁inv hN0.le
        have h2 := mul_le_mul_of_nonneg_left hνl hN0.le
        linarith only [h1, h2, hl]
      · have h1 : 2 * Bν ≤ T₁ := by rw [hT₁def]; linarith
        have h2 := mul_le_mul_of_nonneg_left hνu hN0.le
        have h3 := mul_le_mul_of_nonneg_right h1 hN0.le
        linarith only [h2, h3, hu]
    have hclose_ref : ∀ t, |(Local.trials (a.state n).sizes s t : ℝ) - (a.state n).sizes t| <
        T₁ * N / scale N p := by
      intro t
      rw [trials_cast _ s t (hñpos t)]
      have hd : |((a.state n).sizes t : ℝ) - (if s = t then 1 else 0) - (a.state n).sizes t| ≤ 1 := by
        rw [show ((a.state n).sizes t : ℝ) - (if s = t then 1 else 0) - (a.state n).sizes t =
          -(if s = t then 1 else 0) by ring, abs_neg]
        split_ifs <;> norm_num
      have hNS : 1 ≤ (N : ℝ) / scale N p := by
        unfold scale
        rw [le_div_iff₀ hS₀]
        linarith
      have : T₁ * N / scale N p = T₁ * ((N : ℝ) / scale N p) := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left hNS (by linarith : (0 : ℝ) ≤ T₁)
      linarith
    have hclose_new : ∀ t, |(Local.trials sizes s t : ℝ) - (a.state n).sizes t| <
        T₁ * N / scale N p := by
      intro t
      rw [trials_cast _ s t (hfacts.sizes_pos t)]
      have hd : |(-(if s = t then (1 : ℝ) else 0))| ≤ 1 := by
        rw [abs_neg]
        split_ifs <;> norm_num
      have htri := abs_add_le ((sizes t : ℝ) - (a.state n).sizes t) (-(if s = t then (1 : ℝ) else 0))
      have hrew : (sizes t : ℝ) - (if s = t then 1 else 0) - (a.state n).sizes t =
          ((sizes t : ℝ) - (a.state n).sizes t) + -(if s = t then (1 : ℝ) else 0) := by ring
      rw [hrew]
      have hNS : 1 ≤ (N : ℝ) / scale N p := by
        unfold scale
        rw [le_div_iff₀ hS₀]
        linarith
      have hTS : T * sizeScale N (p : ℝ) n ≤ (N : ℝ) / scale N p := by
        rw [sizeScale_eq N hNpos]
        unfold scale
        rw [le_div_iff₀ hS₀]
        calc
          T * (betaScale N (p : ℝ) n * N) * Real.sqrt ((p : ℝ) * N) =
              (N : ℝ) * (T * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N))) := by ring
          _ ≤ (N : ℝ) * 1 := by
            apply mul_le_mul_of_nonneg_left _ hN0.le
            linarith [hTx, hx.le]
          _ = N := mul_one _
      have : T₁ * N / scale N p = T₁ * ((N : ℝ) / scale N p) := by ring
      rw [this]
      have hT₁2 : 2 < T₁ := by rw [hT₁def]; linarith
      have hNS0 : 0 < (N : ℝ) / scale N p := by linarith
      have := mul_lt_mul_of_pos_right hT₁2 hNS0
      linarith [hclose t]
    have hq₀ : ∀ t, |(a.tilt n s t : ℝ) - p| < T₁ * (p : ℝ) / scale N p := by
      intro t
      rw [hgtilt t]
      have hν := ν_positive n t
      have h := logitTilt_sub_p_le N p (ν n t) (σr t) R₀ hν hR₀.le (by linarith) hs1 (hσrR t)
      have hmono := lipschitz_const_mono hνmin (hνle t) hR₀.le
      rw [← hLp₀def] at hmono
      have hpS : 0 < (p : ℝ) / Real.sqrt ((p : ℝ) * N) := div_pos hp0 hS₀
      have hT₁gt : Lp₀ * R₀ < T₁ := by rw [hT₁def]; linarith
      unfold scale
      calc
        _ ≤ 2 * Real.exp (R₀ / ν n t) / ν n t * ((p : ℝ) / Real.sqrt ((p : ℝ) * N)) * R₀ := h
        _ ≤ Lp₀ * ((p : ℝ) / Real.sqrt ((p : ℝ) * N)) * R₀ := by
          apply mul_le_mul_of_nonneg_right _ hR₀.le
          exact mul_le_mul_of_nonneg_right hmono hpS.le
        _ = Lp₀ * R₀ * ((p : ℝ) / Real.sqrt ((p : ℝ) * N)) := by ring
        _ < T₁ * ((p : ℝ) / Real.sqrt ((p : ℝ) * N)) := mul_lt_mul_of_pos_right hT₁gt hpS
        _ = _ := by ring
    have hq₁ : ∀ (σ : Row (n + 1)), (∀ t, |σ t| ≤ R) → ∀ t,
        |(processEffectiveTilt N p a n sizes s τ σ t : ℝ) - p| ≤
          LpG * G * ((p : ℝ) / Real.sqrt ((p : ℝ) * N)) := by
      intro σ hσ t
      obtain ⟨g, hg, _, hgG⟩ := hgrow σ hσ
      have hν := ν_positive n t
      have hq : processEffectiveTilt N p a n sizes s τ σ t = Idealized.logitTilt N p (g t) (ν n t) :=
        (congrFun hg t).symm
      rw [hq]
      have h := logitTilt_sub_p_le N p (ν n t) (g t) G hν hG.le (by linarith) hs1 (hgG t)
      have hmono := lipschitz_const_mono hνmin (hνle t) hG.le
      rw [← hLpGdef] at hmono
      have hpS : 0 < (p : ℝ) / Real.sqrt ((p : ℝ) * N) := div_pos hp0 hS₀
      calc
        _ ≤ 2 * Real.exp (G / ν n t) / ν n t * ((p : ℝ) / Real.sqrt ((p : ℝ) * N)) * G := h
        _ ≤ LpG * ((p : ℝ) / Real.sqrt ((p : ℝ) * N)) * G := by
          apply mul_le_mul_of_nonneg_right _ hG.le
          exact mul_le_mul_of_nonneg_right hmono hpS.le
        _ = _ := by ring
    -- the norm of the A.2 tilt vector
    have hβfun : ∀ σ : Row (n + 1),
        tiltDifference p (a.state n).sizes (Local.trials (a.state n).sizes s) (Local.trials sizes s)
          (a.tilt n s) (processEffectiveTilt N p a n sizes s τ σ) =
          fun t => τ * betaScale N (p : ℝ) n * σ t := fun σ =>
      effectiveTilt_difference N p (a.state n).sizes (a.tilt n s) sizes s τ σ hres_ref hres_new
    have hβnorm : ∀ (σ : Row (n + 1)), (∀ t, |σ t| ≤ R) →
        ‖tiltDifference p (a.state n).sizes (Local.trials (a.state n).sizes s)
          (Local.trials sizes s) (a.tilt n s) (processEffectiveTilt N p a n sizes s τ σ)‖ ≤
          T * betaScale N (p : ℝ) n * R := by
      intro σ hσ
      rw [hβfun σ]
      have hTβR : 0 ≤ T * betaScale N (p : ℝ) n * R := by positivity
      rw [pi_norm_le_iff_of_nonneg hTβR]
      intro t
      show ‖τ * betaScale N (p : ℝ) n * σ t‖ ≤ T * betaScale N (p : ℝ) n * R
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hτ0, abs_of_pos hβ₀]
      have := hσ t
      have hτβ := mul_le_mul_of_nonneg_right hτ₂ hβ₀.le
      have := mul_le_mul hτβ (hσ t) (abs_nonneg _) (by positivity)
      linarith
    have hnormsmall : ∀ (σ : Row (n + 1)), (∀ t, |σ t| ≤ R) →
        ‖tiltDifference p (a.state n).sizes (Local.trials (a.state n).sizes s)
          (Local.trials sizes s) (a.tilt n s) (processEffectiveTilt N p a n sizes s τ σ)‖ <
          T₁ / (scale N p * Real.log (N : ℝ) ^ 2) := by
      intro σ hσ
      refine (hβnorm σ hσ).trans_lt ?_
      have hl2 : 0 < Real.log (N : ℝ) ^ 2 := by positivity
      have hden : 0 < scale N p * Real.log (N : ℝ) ^ 2 := by
        unfold scale
        positivity
      rw [lt_div_iff₀ hden]
      have hxl2 := (hbudget 2 (by omega)).2.2.2
      have hTR₁ : T * R < T₁ := by rw [hT₁def]; linarith
      unfold scale
      calc
        T * betaScale N (p : ℝ) n * R * (Real.sqrt ((p : ℝ) * N) * Real.log (N : ℝ) ^ 2) =
            T * R * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N) * Real.log (N : ℝ) ^ 2) := by
          ring
        _ ≤ T * R * 1 := mul_le_mul_of_nonneg_left (hxl2.trans hΘ1) hTR
        _ = T * R := mul_one _
        _ < T₁ := hTR₁
    -- the bound `max(p, ‖β‖² pN log²) ≤ p + T²R² x² log²`
    have hEmax : ∀ (σ : Row (n + 1)), (∀ t, |σ t| ≤ R) →
        max (p : ℝ) (‖tiltDifference p (a.state n).sizes (Local.trials (a.state n).sizes s)
          (Local.trials sizes s) (a.tilt n s) (processEffectiveTilt N p a n sizes s τ σ)‖ ^ 2 *
          ((p : ℝ) * N) * Real.log (N : ℝ) ^ 2) ≤
        (p : ℝ) + T ^ 2 * R ^ 2 *
          (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) ^ 2 * Real.log (N : ℝ) ^ 2 := by
      intro σ hσ
      have h := hβnorm σ hσ
      have hn0 := norm_nonneg (tiltDifference p (a.state n).sizes (Local.trials (a.state n).sizes s)
        (Local.trials sizes s) (a.tilt n s) (processEffectiveTilt N p a n sizes s τ σ))
      have hsq : ‖tiltDifference p (a.state n).sizes (Local.trials (a.state n).sizes s)
          (Local.trials sizes s) (a.tilt n s) (processEffectiveTilt N p a n sizes s τ σ)‖ ^ 2 ≤
          (T * betaScale N (p : ℝ) n * R) ^ 2 := pow_le_pow_left₀ hn0 h 2
      have hrew : (T * betaScale N (p : ℝ) n * R) ^ 2 * ((p : ℝ) * N) * Real.log (N : ℝ) ^ 2 =
          T ^ 2 * R ^ 2 * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) ^ 2 *
            Real.log (N : ℝ) ^ 2 := sq_V_eq hVS
      have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq hpN.le)
        (by positivity : 0 ≤ Real.log (N : ℝ) ^ 2)
      rw [hrew] at h2
      exact (max_le_add_of_nonneg hp0.le (by positivity)).trans (by linarith)
    -- the normalized error shapes
    have hEsh : ∀ k : ℕ, k + 2 ≤ L + L_a + 5 →
        ((p : ℝ) + T ^ 2 * R ^ 2 * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) ^ 2 *
          Real.log (N : ℝ) ^ 2) * Real.log (N : ℝ) ^ k ≤
        (1 + T ^ 2 * R ^ 2) * (N : ℝ) ^ (-responseRate θ n) := by
      intro k hk
      have h1 := (hbudget k (by omega)).2.1
      have h2 := (hbudget (k + 2) hk).2.2.2
      have hxsq : (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) ^ 2 ≤
          betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N) := by
        rw [sq]
        exact mul_le_of_le_one_right hx.le hxle1
      have hlk : 0 ≤ Real.log (N : ℝ) ^ k := pow_nonneg hlog0 k
      have h3 : T ^ 2 * R ^ 2 * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) ^ 2 *
          Real.log (N : ℝ) ^ 2 * Real.log (N : ℝ) ^ k ≤
          T ^ 2 * R ^ 2 * (N : ℝ) ^ (-responseRate θ n) := by
        have h4 : (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) ^ 2 * Real.log (N : ℝ) ^ 2 *
            Real.log (N : ℝ) ^ k ≤ (N : ℝ) ^ (-responseRate θ n) := by
          calc
            _ ≤ betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N) * Real.log (N : ℝ) ^ 2 *
                Real.log (N : ℝ) ^ k :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hxsq (by positivity)) hlk
            _ = betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N) * Real.log (N : ℝ) ^ (k + 2) := by
              rw [pow_add]
              ring
            _ ≤ _ := h2
        calc
          _ = T ^ 2 * R ^ 2 * ((betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) ^ 2 *
              Real.log (N : ℝ) ^ 2 * Real.log (N : ℝ) ^ k) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)
      linarith only [h1, h3]
    -- normalized by `τ x`: `Emax log^k / (τ x) ≤ T (1 + T²R²) Θ`
    have hEsh' : ∀ k : ℕ, k + 2 ≤ L + L_a + 5 →
        ((p : ℝ) + T ^ 2 * R ^ 2 * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) ^ 2 *
          Real.log (N : ℝ) ^ 2) * Real.log (N : ℝ) ^ k /
          (τ * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N))) ≤
        T * (1 + T ^ 2 * R ^ 2) * (N : ℝ) ^ (-responseRate θ n) := by
      intro k hk
      have hτx : 0 < τ * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) := mul_pos hτ0 hx
      rw [div_le_iff₀ hτx]
      have h1 := (hbudget k (by omega)).1
      have h2 := (hbudget (k + 2) (by omega)).2.2.2
      have hlk : 0 ≤ Real.log (N : ℝ) ^ k := pow_nonneg hlog0 k
      have hpx := p_div_beta_le_sqrt hNpos (p : ℝ) hp0 n hs1
      -- p log^k ≤ √p log^k · x
      have hpk : (p : ℝ) * Real.log (N : ℝ) ^ k ≤
          Real.sqrt (p : ℝ) * Real.log (N : ℝ) ^ k *
            (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) := by
        rw [div_le_iff₀ hx] at hpx
        have := mul_le_mul_of_nonneg_right hpx hlk
        linarith only [this]
      have hxk : T ^ 2 * R ^ 2 * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) ^ 2 *
          Real.log (N : ℝ) ^ 2 * Real.log (N : ℝ) ^ k ≤
          T ^ 2 * R ^ 2 * (N : ℝ) ^ (-responseRate θ n) *
            (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) := by
        have : (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) ^ 2 * Real.log (N : ℝ) ^ 2 *
            Real.log (N : ℝ) ^ k = (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N) *
              Real.log (N : ℝ) ^ (k + 2)) * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) := by
          rw [pow_add]
          ring
        calc
          _ = T ^ 2 * R ^ 2 * ((betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) ^ 2 *
              Real.log (N : ℝ) ^ 2 * Real.log (N : ℝ) ^ k) := by ring
          _ = T ^ 2 * R ^ 2 * ((betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N) *
              Real.log (N : ℝ) ^ (k + 2)) * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N))) := by
            rw [this]
          _ ≤ _ := by
            rw [mul_assoc (T ^ 2 * R ^ 2)]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_right h2 hx.le
      have hτ1 : 1 ≤ T * τ := by
        have := mul_le_mul_of_nonneg_left hτ₁ hT0.le
        rwa [mul_inv_cancel₀ hT0.ne'] at this
      have hmain : ((p : ℝ) + T ^ 2 * R ^ 2 * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) ^ 2 *
          Real.log (N : ℝ) ^ 2) * Real.log (N : ℝ) ^ k ≤
          (1 + T ^ 2 * R ^ 2) * (N : ℝ) ^ (-responseRate θ n) *
            (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) := by
        have h5 : Real.sqrt (p : ℝ) * Real.log (N : ℝ) ^ k *
            (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) ≤
            (N : ℝ) ^ (-responseRate θ n) * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) :=
          mul_le_mul_of_nonneg_right h1 hx.le
        linarith only [hpk, hxk, h5]
      calc
        _ ≤ (1 + T ^ 2 * R ^ 2) * (N : ℝ) ^ (-responseRate θ n) *
            (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) := hmain
        _ = (1 + T ^ 2 * R ^ 2) * (N : ℝ) ^ (-responseRate θ n) *
            (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) * 1 := (mul_one _).symm
        _ ≤ (1 + T ^ 2 * R ^ 2) * (N : ℝ) ^ (-responseRate θ n) *
            (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) * (T * τ) :=
          mul_le_mul_of_nonneg_left hτ1 (by positivity)
        _ = _ := by ring
    -- per-σ facts shared by the remaining clauses
    have hσblock : ∀ (σ : Row (n + 1)), (∀ t, |σ t| ≤ R) →
        |historyMass sizes s (processEffectiveTilt N p a n sizes s τ σ) -
          historyMass (a.state n).sizes s (a.tilt n s)| ≤ Ku * (N : ℝ) ^ (-responseRate θ n) ∧
        (∀ b, |splitProbability sizes s b (processEffectiveTilt N p a n sizes s τ σ) -
          splitProbability (a.state n).sizes s b (a.tilt n s)| ≤
            Kus * (N : ℝ) ^ (-responseRate θ n)) ∧
        (∀ b, |childMass sizes s b (processEffectiveTilt N p a n sizes s τ σ) -
          childMass (a.state n).sizes s b (a.tilt n s)| ≤
            (Ku + 2 * Kus) * (N : ℝ) ^ (-responseRate θ n)) ∧
        ∃ E₀ E₁ : ℝ, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧
          RowExpansions N p (a.state n).sizes sizes s (a.tilt n s)
            (processEffectiveTilt N p a n sizes s τ σ)
            (tiltDifference p (a.state n).sizes (Local.trials (a.state n).sizes s)
              (Local.trials sizes s) (a.tilt n s) (processEffectiveTilt N p a n sizes s τ σ))
            E₀ E₁ ∧
          E₀ ≤ KeP * (N : ℝ) ^ (-responseRate θ n) ∧
          E₁ / (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)) ≤ KeM * (N : ℝ) ^ (-responseRate θ n) ∧
          E₀ / (τ * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N))) ≤
            KeM * (N : ℝ) ^ (-responseRate θ n) := by
      intro σ hσ
      obtain ⟨g, hg, hgσr, hgG⟩ := hgrow σ hσ
      have hestA := ((hE3 g hgG).2.2.2.2 hfacts.imbalance).2.2.2
      have hδg0 : 0 ≤ Kg * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) := by positivity
      obtain ⟨hgM, _, _, hgMJ, _⟩ := hbridge s g σr hgG hσrG _ hδg0 hgσr
      have hKgx : K * (Kg * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N))) ≤
          K * Kg * (N : ℝ) ^ (-responseRate θ n) := by
        have := mul_le_mul_of_nonneg_left hx1 (by positivity : 0 ≤ K * Kg)
        linarith
      have hKgxφ : K * Kg * (N : ℝ) ^ (-responseRate θ n) ≤ φStar n / 16 :=
        (hpiece (K * Kg) hKKg hKbig_ge.2.2.2.2.2.2.1).trans hφsq
      have hCaε : C_a * error L_a N p (xiScale N (p : ℝ) n T) ≤
          C_a * (d * T + 2) * (N : ℝ) ^ (-responseRate θ n) := by
        have := mul_le_mul_of_nonneg_left hε_a hC_a.le
        linarith
      have hC₀ρ : C₀ * (Real.log (N : ℝ) ^ L / scale N p) ≤ C₀ * (N : ℝ) ^ (-responseRate θ n) :=
        mul_le_mul_of_nonneg_left hρ hC₀.le
      -- (1) the perturbed history mass
      have hPg : |historyMass sizes s (processEffectiveTilt N p a n sizes s τ σ) -
          gaussianMass g (historyEvent s)| ≤ C_a * error L_a N p (xiScale N (p : ℝ) n T) := by
        have h := hestA.history_probability
        rwa [binomialMass_eq _ _ _ _ _ _ hg] at h
      have hσrD : |gaussianMass σr (historyEvent s) - historyMass (a.state n).sizes s (a.tilt n s)| ≤
          C₀ * (Real.log (N : ℝ) ^ L / scale N p) := by
        have h1 := hest.history_probability
        rw [hD_eq, abs_sub_comm] at h1
        exact h1
      have hP'D : |historyMass sizes s (processEffectiveTilt N p a n sizes s τ σ) -
          historyMass (a.state n).sizes s (a.tilt n s)| ≤ Ku * (N : ℝ) ^ (-responseRate θ n) := by
        have h1 := abs_sub_le (historyMass sizes s (processEffectiveTilt N p a n sizes s τ σ))
          (gaussianMass g (historyEvent s)) (historyMass (a.state n).sizes s (a.tilt n s))
        have h2 := abs_sub_le (gaussianMass g (historyEvent s)) (gaussianMass σr (historyEvent s))
          (historyMass (a.state n).sizes s (a.tilt n s))
        rw [hKudef]
        linarith
      -- (2) the perturbed split
      have hgMlo : φStar n / 2 ≤ gaussianMass g (historyEvent s) := by
        obtain ⟨ha, hb⟩ := abs_le.mp hgM
        obtain ⟨ha', hb'⟩ := abs_le.mp hbM
        linarith [ha, hb, ha', hb']
      have hsplit' : ∀ b, |splitProbability sizes s b (processEffectiveTilt N p a n sizes s τ σ) -
          splitProbability (a.state n).sizes s b (a.tilt n s)| ≤
            Kus * (N : ℝ) ^ (-responseRate θ n) := by
        intro b
        have h1 := hestA.split_probability b
        rw [shiftedChildEvent_zero, binomialSplit_eq _ _ _ _ _ _ hg] at h1
        have h2 := hest.split_probability b
        rw [shiftedChildEvent_zero, binomialSplit_eq _ _ _ _ _ _ htilt] at h2
        have hJ1 : |gaussianMass σr (childEvent s b)| ≤ 1 := gaussianMass_abs_le_one _ _
        have hratio := ratio_error (by positivity : 0 < φStar n / 2) hgMlo hgMσr hJ1 (hgMJ b) hgM
        rw [← hKrdef] at hratio
        have htri1 := abs_sub_le (splitProbability sizes s b (processEffectiveTilt N p a n sizes s τ σ))
          (gaussianMass g (childEvent s b) / gaussianMass g (historyEvent s))
          (splitProbability (a.state n).sizes s b (a.tilt n s))
        have htri2 := abs_sub_le (gaussianMass g (childEvent s b) / gaussianMass g (historyEvent s))
          (gaussianMass σr (childEvent s b) / gaussianMass σr (historyEvent s))
          (splitProbability (a.state n).sizes s b (a.tilt n s))
        rw [abs_sub_comm] at h2
        have hKrK : Kr * (K * (Kg * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)))) ≤
            Kr * (K * Kg) * (N : ℝ) ^ (-responseRate θ n) := by
          have := mul_le_mul_of_nonneg_left hKgx hKr
          linarith
        rw [hKusdef]
        linarith
      -- (3) the perturbed child mass
      have hP'pos : 0 < historyMass sizes s (processEffectiveTilt N p a n sizes s τ σ) := by
        obtain ⟨ha, hb⟩ := abs_le.mp hP'D
        have hKuφ : Ku * (N : ℝ) ^ (-responseRate θ n) ≤ φStar n / 16 :=
          (hpiece Ku hKu hKbig_ge.2.2.1).trans hφsq
        linarith [ha, hb]
      have hP'J : ∀ b, |childMass sizes s b (processEffectiveTilt N p a n sizes s τ σ) -
          childMass (a.state n).sizes s b (a.tilt n s)| ≤
            (Ku + 2 * Kus) * (N : ℝ) ^ (-responseRate θ n) := by
        intro b
        have hPJ_eq : childMass sizes s b (processEffectiveTilt N p a n sizes s τ σ) =
            historyMass sizes s (processEffectiveTilt N p a n sizes s τ σ) *
              splitProbability sizes s b (processEffectiveTilt N p a n sizes s τ σ) := by
          unfold splitProbability
          exact ((div_mul_cancel₀ _ hP'pos.ne').symm.trans (mul_comm _ _))
        rw [hPJ_eq, hDJ_eq b]
        have h := abs_mul_sub_mul_le (historyMass sizes s (processEffectiveTilt N p a n sizes s τ σ))
          (historyMass (a.state n).sizes s (a.tilt n s))
          (splitProbability sizes s b (processEffectiveTilt N p a n sizes s τ σ))
          (splitProbability (a.state n).sizes s b (a.tilt n s))
          (historyMass (a.state n).sizes s (a.tilt n s) + Ku * (N : ℝ) ^ (-responseRate θ n)) 1
          (by
            obtain ⟨ha, hb⟩ := abs_le.mp hP'D
            rw [abs_of_pos hP'pos]
            linarith [ha, hb])
          (by
            rw [abs_of_nonneg (by
              unfold splitProbability childMass
              exact div_nonneg (eventMass_nonneg _ _ _) hDpos.le)]
            unfold splitProbability
            rw [div_le_one hDpos]
            exact hDJle b)
        have hKuφ : Ku * (N : ℝ) ^ (-responseRate θ n) ≤ φStar n / 16 :=
          (hpiece Ku hKu hKbig_ge.2.2.1).trans hφsq
        have hsp := hsplit' b
        have hfac : historyMass (a.state n).sizes s (a.tilt n s) + Ku * (N : ℝ) ^ (-responseRate θ n) ≤ 2 := by
          have := hφ1
          linarith
        have := mul_le_mul hfac hsp (abs_nonneg _) (by norm_num)
        linarith
      -- (4) the A.2 expansions
      have hq₁lt : ∀ t, |(processEffectiveTilt N p a n sizes s τ σ t : ℝ) - p| <
          T₁ * (p : ℝ) / scale N p := by
        intro t
        have h := hq₁ σ hσ t
        have hpS : 0 < (p : ℝ) / Real.sqrt ((p : ℝ) * N) := div_pos hp0 hS₀
        have hT₁gt : LpG * G < T₁ := by rw [hT₁def]; linarith
        unfold scale
        calc
          _ ≤ LpG * G * ((p : ℝ) / Real.sqrt ((p : ℝ) * N)) := h
          _ < T₁ * ((p : ℝ) / Real.sqrt ((p : ℝ) * N)) := mul_lt_mul_of_pos_right hT₁gt hpS
          _ = _ := by ring
      have hRexp := hexp N hNN_A p (density_enlarge hT0 hTT₁ hp) (a.state n).sizes sizes hSizes s
        (fun t => ⟨htr_ref t, htr_new t⟩) (fun t => ⟨hclose_ref t, hclose_new t⟩) (a.tilt n s)
        (processEffectiveTilt N p a n sizes s τ σ) (fun t => ⟨hq₀ t, hq₁lt t⟩) (hnormsmall σ hσ)
      have hMAX0 : 0 ≤ max (p : ℝ) (‖tiltDifference p (a.state n).sizes
          (Local.trials (a.state n).sizes s) (Local.trials sizes s) (a.tilt n s)
          (processEffectiveTilt N p a n sizes s τ σ)‖ ^ 2 * ((p : ℝ) * N) * Real.log (N : ℝ) ^ 2) :=
        le_max_of_le_left hp0.le
      have hMAX := hEmax σ hσ
      refine ⟨hP'D, hsplit', hP'J, _, _, mul_nonneg (mul_nonneg hC_A.le hMAX0) (pow_nonneg hlog0 2),
        mul_nonneg (mul_nonneg (mul_nonneg hC_A.le hMAX0) (Real.sqrt_nonneg _)) (pow_nonneg hlog0 3),
        hRexp, ?_, ?_, ?_⟩
      · -- E₀ ≤ KeP Θ
        have h := hEsh 2 (by omega)
        rw [hKePdef]
        have h2 := mul_le_mul_of_nonneg_right hMAX (by positivity : 0 ≤ Real.log (N : ℝ) ^ 2)
        calc
          _ = C_A * (max (p : ℝ) (‖tiltDifference p (a.state n).sizes
              (Local.trials (a.state n).sizes s) (Local.trials sizes s) (a.tilt n s)
              (processEffectiveTilt N p a n sizes s τ σ)‖ ^ 2 * ((p : ℝ) * N) *
                Real.log (N : ℝ) ^ 2) * Real.log (N : ℝ) ^ 2) := by ring
          _ ≤ C_A * ((1 + T ^ 2 * R ^ 2) * (N : ℝ) ^ (-responseRate θ n)) :=
            mul_le_mul_of_nonneg_left (h2.trans h) hC_A.le
          _ = _ := by ring
      · -- E₁ / (b₀ V) ≤ KeM Θ
        have h := hEsh' 3 (by omega)
        rw [hKeMdef]
        have hτx : 0 < τ * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) := mul_pos hτ0 hx
        have hbV : 0 < τ * betaScale N (p : ℝ) n * ((p : ℝ) * N) := by positivity
        have hrew : C_A * max (p : ℝ) (‖tiltDifference p (a.state n).sizes
            (Local.trials (a.state n).sizes s) (Local.trials sizes s) (a.tilt n s)
            (processEffectiveTilt N p a n sizes s τ σ)‖ ^ 2 * ((p : ℝ) * N) *
              Real.log (N : ℝ) ^ 2) * Real.sqrt ((p : ℝ) * N) * Real.log (N : ℝ) ^ 3 /
            (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)) =
            C_A * (max (p : ℝ) (‖tiltDifference p (a.state n).sizes
              (Local.trials (a.state n).sizes s) (Local.trials sizes s) (a.tilt n s)
              (processEffectiveTilt N p a n sizes s τ σ)‖ ^ 2 * ((p : ℝ) * N) *
                Real.log (N : ℝ) ^ 2) * Real.log (N : ℝ) ^ 3 /
              (τ * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)))) :=
          E1_norm hτ0.ne' hβ₀.ne' hS₀.ne' hVS
        rw [hrew]
        have h2 : max (p : ℝ) (‖tiltDifference p (a.state n).sizes
            (Local.trials (a.state n).sizes s) (Local.trials sizes s) (a.tilt n s)
            (processEffectiveTilt N p a n sizes s τ σ)‖ ^ 2 * ((p : ℝ) * N) *
              Real.log (N : ℝ) ^ 2) * Real.log (N : ℝ) ^ 3 /
            (τ * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N))) ≤
            T * (1 + T ^ 2 * R ^ 2) * (N : ℝ) ^ (-responseRate θ n) := by
          refine le_trans ?_ h
          apply div_le_div_of_nonneg_right _ hτx.le
          exact mul_le_mul_of_nonneg_right hMAX (by positivity)
        calc
          _ ≤ C_A * (T * (1 + T ^ 2 * R ^ 2) * (N : ℝ) ^ (-responseRate θ n)) :=
            mul_le_mul_of_nonneg_left h2 hC_A.le
          _ = _ := by ring
      · -- E₀ / (τ x) ≤ KeM Θ
        have h := hEsh' 2 (by omega)
        rw [hKeMdef]
        have hτx : 0 < τ * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) := mul_pos hτ0 hx
        have hrew : C_A * max (p : ℝ) (‖tiltDifference p (a.state n).sizes
            (Local.trials (a.state n).sizes s) (Local.trials sizes s) (a.tilt n s)
            (processEffectiveTilt N p a n sizes s τ σ)‖ ^ 2 * ((p : ℝ) * N) *
              Real.log (N : ℝ) ^ 2) * Real.log (N : ℝ) ^ 2 /
            (τ * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N))) =
            C_A * (max (p : ℝ) (‖tiltDifference p (a.state n).sizes
              (Local.trials (a.state n).sizes s) (Local.trials sizes s) (a.tilt n s)
              (processEffectiveTilt N p a n sizes s τ σ)‖ ^ 2 * ((p : ℝ) * N) *
                Real.log (N : ℝ) ^ 2) * Real.log (N : ℝ) ^ 2 /
              (τ * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)))) := by ring
        rw [hrew]
        have h2 : max (p : ℝ) (‖tiltDifference p (a.state n).sizes
            (Local.trials (a.state n).sizes s) (Local.trials sizes s) (a.tilt n s)
            (processEffectiveTilt N p a n sizes s τ σ)‖ ^ 2 * ((p : ℝ) * N) *
              Real.log (N : ℝ) ^ 2) * Real.log (N : ℝ) ^ 2 /
            (τ * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N))) ≤
            T * (1 + T ^ 2 * R ^ 2) * (N : ℝ) ^ (-responseRate θ n) := by
          refine le_trans ?_ h
          apply div_le_div_of_nonneg_right _ hτx.le
          exact mul_le_mul_of_nonneg_right hMAX (by positivity)
        calc
          _ ≤ C_A * (T * (1 + T ^ 2 * R ^ 2) * (N : ℝ) ^ (-responseRate θ n)) :=
            mul_le_mul_of_nonneg_left h2 hC_A.le
          _ = _ := by ring
    -- common smallness facts
    have hKuφ : Ku * (N : ℝ) ^ (-responseRate θ n) ≤ φStar n ^ 2 / 32 :=
      hpiece Ku hKu hKbig_ge.2.2.1
    have hKusφ : Kus * (N : ℝ) ^ (-responseRate θ n) ≤ φStar n ^ 2 / 32 :=
      hpiece Kus hKus hKbig_ge.2.2.2.1
    have hKuJφ : (Ku + 2 * Kus) * (N : ℝ) ^ (-responseRate θ n) ≤ φStar n ^ 2 / 32 :=
      hpiece (Ku + 2 * Kus) (by positivity) hKbig_ge.2.2.2.2.1
    have hKePφ : KeP * (N : ℝ) ^ (-responseRate θ n) ≤ φStar n ^ 2 / 32 :=
      hpiece KeP hKeP hKbig_ge.2.2.2.2.2.1
    have hφφ := mul_le_mul_of_nonneg_left hφ1 hφ.le
    have hφsq1 : φStar n ^ 2 / 32 ≤ 1 := by linarith only [hφφ, hφ1, hφ]
    have hφsq2 : φStar n ^ 2 / 16 ≤ 1 := by linarith only [hφφ, hφ1, hφ]
    have hKec1 : Kec * (N : ℝ) ^ (-responseRate θ n) ≤ 1 := hec.trans hφsq1
    have hEmI : ∀ t, |cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
        (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) t /
          historyMass (a.state n).sizes s (a.tilt n s)| ≤ (G₀ + 1) * Real.sqrt ((p : ℝ) * N) := by
      intro t
      have h1 := hμI t
      have h2 : |cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
          (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) t /
            historyMass (a.state n).sizes s (a.tilt n s) / Real.sqrt ((p : ℝ) * N)| ≤ G₀ + 1 := by
        have := abs_sub_abs_le_abs_sub (cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
          (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) t /
            historyMass (a.state n).sizes s (a.tilt n s) / Real.sqrt ((p : ℝ) * N))
          (∫ x, x t ∂historyLaw n s)
        linarith [hgI s t]
      rwa [abs_div, abs_of_pos hS₀, div_le_iff₀ hS₀] at h2
    have hEmJ : ∀ b t, |cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
        (Local.childSupport (a.state n).sizes s b) (center p (a.state n).sizes) t /
          childMass (a.state n).sizes s b (a.tilt n s)| ≤ (G₀ + 1) * Real.sqrt ((p : ℝ) * N) := by
      intro b t
      have h1 := hμJ b t
      have h2 : |cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
          (Local.childSupport (a.state n).sizes s b) (center p (a.state n).sizes) t /
            childMass (a.state n).sizes s b (a.tilt n s) / Real.sqrt ((p : ℝ) * N)| ≤ G₀ + 1 := by
        have := abs_sub_abs_le_abs_sub (cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
          (Local.childSupport (a.state n).sizes s b) (center p (a.state n).sizes) t /
            childMass (a.state n).sizes s b (a.tilt n s) / Real.sqrt ((p : ℝ) * N))
          (∫ x, x t ∂childLaw n s b)
        linarith [hgJ s b t]
      rwa [abs_div, abs_of_pos hS₀, div_le_iff₀ hS₀] at h2
    have hCmeanC : Cmean ≤ C := by rw [hCdef]; linarith [mul_nonneg hLpG.le hG.le]
    have hCsplitC : Csplit ≤ C := by rw [hCdef]; linarith [mul_nonneg hLpG.le hG.le]
    have hCchildC : Cchild ≤ C := by rw [hCdef]; linarith [mul_nonneg hLpG.le hG.le]
    have h2D : 2 / historyMass (a.state n).sizes s (a.tilt n s) ≤ 4 / φStar n := by
      rw [div_le_div_iff₀ hDpos hφ]
      linarith
    have h2DJ : ∀ b, 2 / childMass (a.state n).sizes s b (a.tilt n s) ≤ 8 / φStar n ^ 2 := by
      intro b
      rw [div_le_div_iff₀ (hDJpos b) (by positivity)]
      linarith [hDJlo b]
    -- assemble the clauses
    refine
      { reference_residual_pos := hres_ref
        residual_pos := hres_new
        tilt_in_unit := fun σ t => effectiveTilt_in_unit N p _ _ sizes s τ σ t
        tilt_bound := ?_
        tilt_equation := fun σ t => effectiveTilt_equation N p _ _ sizes s τ σ t (hres_ref t)
          (hres_new t) (hcenter_pos t)
        smooth := smooth_response_quantities N p _ _ sizes s τ hhist_new
        mean_response := ?_
        split_response := ?_
        child_mean_response := ?_
        history_nondegenerate := ?_
        split_nondegenerate := ?_ }
    · -- tilt bound
      intro σ hσ t
      have h := hq₁ σ hσ t
      have hCge : LpG * G ≤ C := by rw [hCdef]; linarith
      calc
        _ ≤ LpG * G * ((p : ℝ) / Real.sqrt ((p : ℝ) * N)) := h
        _ ≤ C * ((p : ℝ) / Real.sqrt ((p : ℝ) * N)) :=
          mul_le_mul_of_nonneg_right hCge (by positivity)
        _ = _ := by ring
    · -- (i) mean response
      intro σ hσ t
      obtain ⟨hP'D, _, _, E₀, E₁, hE₀0, hE₁0, hR, hE₀, hE₁, hE₀τ⟩ := hσblock σ hσ
      have hmass := hR.mass none
      have hfirst := hR.first none t
      rw [← Finset.sum_mul] at hmass hfirst
      have hβ : ∀ i, tiltDifference p (a.state n).sizes (Local.trials (a.state n).sizes s)
          (Local.trials sizes s) (a.tilt n s) (processEffectiveTilt N p a n sizes s τ σ) i =
          τ * betaScale N (p : ℝ) n * σ i := fun i => congrFun (hβfun σ) i
      have hsmall : Ku * (N : ℝ) ^ (-responseRate θ n) + E₀ ≤
          historyMass (a.state n).sizes s (a.tilt n s) / 4 := by
        linarith [hE₀.trans hKePφ, hKuφ, hφsq]
      obtain ⟨hDen, hbound⟩ := mean_clause (historyMass (a.state n).sizes s (a.tilt n s))
        (historyMass sizes s (processEffectiveTilt N p a n sizes s τ σ))
        (cfirst (Local.trials sizes s) (processEffectiveTilt N p a n sizes s τ σ)
          (Local.historySupport sizes s) (center p (a.state n).sizes) t)
        (fun i => cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
          (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) i)
        (fun i => csecond (Local.trials (a.state n).sizes s) (a.tilt n s)
          (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) i t)
        (fun i => σ i)
        (tiltDifference p (a.state n).sizes (Local.trials (a.state n).sizes s)
          (Local.trials sizes s) (a.tilt n s) (processEffectiveTilt N p a n sizes s τ σ))
        (fun i => ∫ x, Binomial.Approximation.centered p (a.state n).sizes x i
          ∂Binomial.law (Local.trials (a.state n).sizes s) (a.tilt n s))
        (fun i => conditionalCovariance n s t i) t
        (τ * betaScale N (p : ℝ) n) ((p : ℝ) * N) R G₀ (Kec * (N : ℝ) ^ (-responseRate θ n))
        (Ku * (N : ℝ) ^ (-responseRate θ n)) E₀ E₁ ((G₀ + 1) * Real.sqrt ((p : ℝ) * N))
        hDpos hpN hb₀ hβ hσ hmass hfirst hP'D hsmall (fun i => hcov i t) (fun i => hcovG s t i)
        (hEmI t)
      have hP'ne : historyMass sizes s (processEffectiveTilt N p a n sizes s τ σ) ≠ 0 := by
        have : 0 < historyMass (a.state n).sizes s (a.tilt n s) / 2 := by positivity
        exact (lt_of_lt_of_le this hDen).ne'
      have hlhs : historyMean sizes s (processEffectiveTilt N p a n sizes s τ σ) t -
          (a.state n).edges s t / ((a.state n).sizes s : ℝ) =
          cfirst (Local.trials sizes s) (processEffectiveTilt N p a n sizes s τ σ)
            (Local.historySupport sizes s) (center p (a.state n).sizes) t /
            historyMass sizes s (processEffectiveTilt N p a n sizes s τ σ) -
          cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
            (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) t /
            historyMass (a.state n).sizes s (a.tilt n s) := by
        rw [hsolves t, historyMean_eq_cfirst _ _ _ (center p (a.state n).sizes) t hP'ne,
          historyMean_eq_cfirst _ _ _ (center p (a.state n).sizes) t hDpos.ne']
        ring
      rw [hlhs]
      refine hbound.trans ?_
      -- bound the remainder by `Cmean Θ`
      have hbV : 0 < τ * betaScale N (p : ℝ) n * ((p : ℝ) * N) := by positivity
      have hKS : d * ((τ * betaScale N (p : ℝ) n * R) * ((G₀ + Kec * (N : ℝ) ^ (-responseRate θ n)) *
          ((p : ℝ) * N))) / (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)) ≤ d * R * (G₀ + 1) := by
        rw [div_le_iff₀ hbV]
        have : G₀ + Kec * (N : ℝ) ^ (-responseRate θ n) ≤ G₀ + 1 := by linarith
        have h2 := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ d * R * (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)))
        linarith only [h2]
      have hEm : (G₀ + 1) * Real.sqrt ((p : ℝ) * N) / (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)) =
          (G₀ + 1) / (τ * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N))) :=
        Em_norm hτ0.ne' hβ₀.ne' hS₀.ne' hVS
      have hEPEm : E₀ * ((G₀ + 1) * Real.sqrt ((p : ℝ) * N)) /
          (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)) ≤
          (G₀ + 1) * (KeM * (N : ℝ) ^ (-responseRate θ n)) := by
        rw [mul_div_assoc, hEm]
        have : E₀ * ((G₀ + 1) / (τ * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)))) =
            (G₀ + 1) * (E₀ / (τ * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)))) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left hE₀τ (by positivity)
      have hdecomp : 2 / historyMass (a.state n).sizes s (a.tilt n s) *
          (E₁ + (Ku * (N : ℝ) ^ (-responseRate θ n) + E₀) *
            (d * ((τ * betaScale N (p : ℝ) n * R) * ((G₀ + Kec * (N : ℝ) ^ (-responseRate θ n)) *
              ((p : ℝ) * N)))) +
            E₀ * ((G₀ + 1) * Real.sqrt ((p : ℝ) * N) +
              d * ((τ * betaScale N (p : ℝ) n * R) * ((G₀ + Kec * (N : ℝ) ^ (-responseRate θ n)) *
                ((p : ℝ) * N))))) / (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)) =
          2 / historyMass (a.state n).sizes s (a.tilt n s) *
          (E₁ / (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)) +
            (Ku * (N : ℝ) ^ (-responseRate θ n) + E₀) *
              (d * ((τ * betaScale N (p : ℝ) n * R) * ((G₀ + Kec * (N : ℝ) ^ (-responseRate θ n)) *
                ((p : ℝ) * N))) / (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N))) +
            E₀ * ((G₀ + 1) * Real.sqrt ((p : ℝ) * N)) / (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)) +
            E₀ * (d * ((τ * betaScale N (p : ℝ) n * R) * ((G₀ + Kec * (N : ℝ) ^ (-responseRate θ n)) *
              ((p : ℝ) * N))) / (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)))) := by
        ring
      rw [hddef] at hKS hdecomp
      rw [hdecomp]
      have hKS0 : 0 ≤ (Fintype.card (History (n + 1)) : ℝ) *
          ((τ * betaScale N (p : ℝ) n * R) * ((G₀ + Kec * (N : ℝ) ^ (-responseRate θ n)) *
            ((p : ℝ) * N))) / (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)) := by positivity
      have hue0 : 0 ≤ Ku * (N : ℝ) ^ (-responseRate θ n) + E₀ := by positivity
      have hue : Ku * (N : ℝ) ^ (-responseRate θ n) + E₀ ≤
          (Ku + KeP) * (N : ℝ) ^ (-responseRate θ n) := by linarith
      have hA := mul_le_mul hue hKS hKS0 (by positivity)
      have hB := mul_le_mul hE₀ hKS hKS0 (by positivity)
      have hC4 : 0 ≤ 4 / φStar n := by positivity
      have hinner : E₁ / (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)) +
          (Ku * (N : ℝ) ^ (-responseRate θ n) + E₀) *
            ((Fintype.card (History (n + 1)) : ℝ) * ((τ * betaScale N (p : ℝ) n * R) *
              ((G₀ + Kec * (N : ℝ) ^ (-responseRate θ n)) * ((p : ℝ) * N))) /
              (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N))) +
          E₀ * ((G₀ + 1) * Real.sqrt ((p : ℝ) * N)) / (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)) +
          E₀ * ((Fintype.card (History (n + 1)) : ℝ) * ((τ * betaScale N (p : ℝ) n * R) *
            ((G₀ + Kec * (N : ℝ) ^ (-responseRate θ n)) * ((p : ℝ) * N))) /
            (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N))) ≤
          (KeM + (Ku + KeP) * (d * R * (G₀ + 1)) + (G₀ + 1) * KeM + KeP * (d * R * (G₀ + 1))) *
            (N : ℝ) ^ (-responseRate θ n) := by
        rw [hddef]
        linarith only [hE₁, hA, hB, hEPEm]
      have hinner0 : 0 ≤ E₁ / (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)) +
          (Ku * (N : ℝ) ^ (-responseRate θ n) + E₀) *
            ((Fintype.card (History (n + 1)) : ℝ) * ((τ * betaScale N (p : ℝ) n * R) *
              ((G₀ + Kec * (N : ℝ) ^ (-responseRate θ n)) * ((p : ℝ) * N))) /
              (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N))) +
          E₀ * ((G₀ + 1) * Real.sqrt ((p : ℝ) * N)) / (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)) +
          E₀ * ((Fintype.card (History (n + 1)) : ℝ) * ((τ * betaScale N (p : ℝ) n * R) *
            ((G₀ + Kec * (N : ℝ) ^ (-responseRate θ n)) * ((p : ℝ) * N))) /
            (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N))) := by positivity
      have hmul := mul_le_mul h2D hinner hinner0 hC4
      have hfirstterm : (Fintype.card (History (n + 1)) : ℝ) *
          (R * (Kec * (N : ℝ) ^ (-responseRate θ n))) =
          d * R * Kec * (N : ℝ) ^ (-responseRate θ n) := by rw [hddef]; ring
      rw [hfirstterm]
      calc
        _ ≤ d * R * Kec * (N : ℝ) ^ (-responseRate θ n) + 4 / φStar n *
            ((KeM + (Ku + KeP) * (d * R * (G₀ + 1)) + (G₀ + 1) * KeM + KeP * (d * R * (G₀ + 1))) *
              (N : ℝ) ^ (-responseRate θ n)) := by linarith
        _ = Cmean * (N : ℝ) ^ (-responseRate θ n) := by rw [hCmeandef]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hCmeanC hΘ0
    · -- (ii) split response
      intro σ hσ b
      obtain ⟨hP'D, _, _, E₀, E₁, hE₀0, hE₁0, hR, hE₀, _, hE₀τ⟩ := hσblock σ hσ
      have hmass := hR.mass none
      have hmassJ := hR.mass (some b)
      rw [← Finset.sum_mul] at hmass hmassJ
      have hβ : ∀ i, tiltDifference p (a.state n).sizes (Local.trials (a.state n).sizes s)
          (Local.trials sizes s) (a.tilt n s) (processEffectiveTilt N p a n sizes s τ σ) i =
          τ * betaScale N (p : ℝ) n * σ i := fun i => congrFun (hβfun σ) i
      have hsmall : Ku * (N : ℝ) ^ (-responseRate θ n) + E₀ ≤
          historyMass (a.state n).sizes s (a.tilt n s) / 4 := by
        linarith [hE₀.trans hKePφ, hKuφ, hφsq]
      have hbound := split_clause (historyMass (a.state n).sizes s (a.tilt n s))
        (childMass (a.state n).sizes s b (a.tilt n s))
        (historyMass sizes s (processEffectiveTilt N p a n sizes s τ σ))
        (childMass sizes s b (processEffectiveTilt N p a n sizes s τ σ))
        (fun i => cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
          (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) i)
        (fun i => cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
          (Local.childSupport (a.state n).sizes s b) (center p (a.state n).sizes) i)
        (fun i => σ i)
        (tiltDifference p (a.state n).sizes (Local.trials (a.state n).sizes s)
          (Local.trials sizes s) (a.tilt n s) (processEffectiveTilt N p a n sizes s τ σ))
        (fun i => ∫ x, Binomial.Approximation.centered p (a.state n).sizes x i
          ∂Binomial.law (Local.trials (a.state n).sizes s) (a.tilt n s))
        (fun i => ∫ x, x i ∂childLaw n s b) (fun i => ∫ x, x i ∂historyLaw n s)
        (ν (n + 1) (append s b) / ν n s) (τ * betaScale N (p : ℝ) n) (Real.sqrt ((p : ℝ) * N)) R G₀
        (Kec * (N : ℝ) ^ (-responseRate θ n)) (Ker * (N : ℝ) ^ (-responseRate θ n))
        (Ku * (N : ℝ) ^ (-responseRate θ n)) E₀ E₀
        hDpos (hDJpos b) (hDJle b) hS₀ hb₀ hβ hσ hmass hmassJ hP'D hsmall (hsplit_ref b)
        (fun i => hμJ b i) hμI (fun i => ⟨hgJ s b i, hgI s i⟩)
      refine hbound.trans ?_
      have hbS : 0 < τ * betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N) := by positivity
      have hKS : d * ((τ * betaScale N (p : ℝ) n * R) *
          (2 * (G₀ + Kec * (N : ℝ) ^ (-responseRate θ n)) * Real.sqrt ((p : ℝ) * N))) /
          (τ * betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) ≤ d * (R * (2 * (G₀ + 1))) := by
        rw [div_le_iff₀ hbS]
        have : G₀ + Kec * (N : ℝ) ^ (-responseRate θ n) ≤ G₀ + 1 := by linarith
        have h2 := mul_le_mul_of_nonneg_left this (by positivity :
          0 ≤ 2 * d * R * (τ * betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)))
        linarith only [h2]
      have hE₀S : E₀ / (τ * betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) ≤
          KeM * (N : ℝ) ^ (-responseRate θ n) := by
        rw [mul_assoc]
        exact hE₀τ
      have hdecomp : 2 / historyMass (a.state n).sizes s (a.tilt n s) *
          (E₀ + (Ku * (N : ℝ) ^ (-responseRate θ n) + E₀) *
            (d * ((τ * betaScale N (p : ℝ) n * R) *
              (2 * (G₀ + Kec * (N : ℝ) ^ (-responseRate θ n)) * Real.sqrt ((p : ℝ) * N)))) +
            E₀ * (1 + d * ((τ * betaScale N (p : ℝ) n * R) *
              (2 * (G₀ + Kec * (N : ℝ) ^ (-responseRate θ n)) * Real.sqrt ((p : ℝ) * N))))) /
          (τ * betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) =
          2 / historyMass (a.state n).sizes s (a.tilt n s) *
          (E₀ / (τ * betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) +
            (Ku * (N : ℝ) ^ (-responseRate θ n) + E₀) *
              (d * ((τ * betaScale N (p : ℝ) n * R) *
                (2 * (G₀ + Kec * (N : ℝ) ^ (-responseRate θ n)) * Real.sqrt ((p : ℝ) * N))) /
                (τ * betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N))) +
            E₀ / (τ * betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) +
            E₀ * (d * ((τ * betaScale N (p : ℝ) n * R) *
              (2 * (G₀ + Kec * (N : ℝ) ^ (-responseRate θ n)) * Real.sqrt ((p : ℝ) * N))) /
              (τ * betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)))) := by
        ring
      rw [hddef] at hKS hdecomp
      rw [hdecomp]
      have hKS0 : 0 ≤ (Fintype.card (History (n + 1)) : ℝ) * ((τ * betaScale N (p : ℝ) n * R) *
          (2 * (G₀ + Kec * (N : ℝ) ^ (-responseRate θ n)) * Real.sqrt ((p : ℝ) * N))) /
          (τ * betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) := by positivity
      have hue0 : 0 ≤ Ku * (N : ℝ) ^ (-responseRate θ n) + E₀ := by positivity
      have hue : Ku * (N : ℝ) ^ (-responseRate θ n) + E₀ ≤
          (Ku + KeP) * (N : ℝ) ^ (-responseRate θ n) := by linarith
      have hA := mul_le_mul hue hKS hKS0 (by positivity)
      have hB := mul_le_mul hE₀ hKS hKS0 (by positivity)
      have hC4 : 0 ≤ 4 / φStar n := by positivity
      have hinner : E₀ / (τ * betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) +
          (Ku * (N : ℝ) ^ (-responseRate θ n) + E₀) *
            ((Fintype.card (History (n + 1)) : ℝ) * ((τ * betaScale N (p : ℝ) n * R) *
              (2 * (G₀ + Kec * (N : ℝ) ^ (-responseRate θ n)) * Real.sqrt ((p : ℝ) * N))) /
              (τ * betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N))) +
          E₀ / (τ * betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) +
          E₀ * ((Fintype.card (History (n + 1)) : ℝ) * ((τ * betaScale N (p : ℝ) n * R) *
            (2 * (G₀ + Kec * (N : ℝ) ^ (-responseRate θ n)) * Real.sqrt ((p : ℝ) * N))) /
            (τ * betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N))) ≤
          (KeM + (Ku + KeP) * (d * (R * (2 * (G₀ + 1)))) + KeM + KeP * (d * (R * (2 * (G₀ + 1))))) *
            (N : ℝ) ^ (-responseRate θ n) := by
        rw [hddef]
        linarith only [hE₀S, hA, hB]
      have hinner0 : 0 ≤ E₀ / (τ * betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) +
          (Ku * (N : ℝ) ^ (-responseRate θ n) + E₀) *
            ((Fintype.card (History (n + 1)) : ℝ) * ((τ * betaScale N (p : ℝ) n * R) *
              (2 * (G₀ + Kec * (N : ℝ) ^ (-responseRate θ n)) * Real.sqrt ((p : ℝ) * N))) /
              (τ * betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N))) +
          E₀ / (τ * betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) +
          E₀ * ((Fintype.card (History (n + 1)) : ℝ) * ((τ * betaScale N (p : ℝ) n * R) *
            (2 * (G₀ + Kec * (N : ℝ) ^ (-responseRate θ n)) * Real.sqrt ((p : ℝ) * N))) /
            (τ * betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N))) := by positivity
      have hmul := mul_le_mul h2D hinner hinner0 hC4
      have hfirst2 : (Fintype.card (History (n + 1)) : ℝ) *
          (R * (2 * (Kec * (N : ℝ) ^ (-responseRate θ n)))) +
          (Fintype.card (History (n + 1)) : ℝ) * (R * (2 * G₀)) *
            (Ker * (N : ℝ) ^ (-responseRate θ n)) =
          (d * (R * (2 * Kec)) + d * (R * (2 * G₀)) * Ker) * (N : ℝ) ^ (-responseRate θ n) := by
        rw [hddef]
        ring
      rw [hfirst2]
      calc
        _ ≤ (d * (R * (2 * Kec)) + d * (R * (2 * G₀)) * Ker) * (N : ℝ) ^ (-responseRate θ n) +
            4 / φStar n * ((KeM + (Ku + KeP) * (d * (R * (2 * (G₀ + 1)))) + KeM +
              KeP * (d * (R * (2 * (G₀ + 1))))) * (N : ℝ) ^ (-responseRate θ n)) := by linarith
        _ = Csplit * (N : ℝ) ^ (-responseRate θ n) := by rw [hCsplitdef]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hCsplitC hΘ0
    · -- (iii) child conditional mean
      intro σ hσ b t
      obtain ⟨_, _, hP'J, E₀, E₁, hE₀0, hE₁0, hR, hE₀, hE₁, hE₀τ⟩ := hσblock σ hσ
      have hmassJ := hR.mass (some b)
      have hfirstJ := hR.first (some b) t
      rw [← Finset.sum_mul] at hmassJ hfirstJ
      have hβ : ∀ i, tiltDifference p (a.state n).sizes (Local.trials (a.state n).sizes s)
          (Local.trials sizes s) (a.tilt n s) (processEffectiveTilt N p a n sizes s τ σ) i =
          τ * betaScale N (p : ℝ) n * σ i := fun i => congrFun (hβfun σ) i
      have hsmall : (Ku + 2 * Kus) * (N : ℝ) ^ (-responseRate θ n) + E₀ ≤
          childMass (a.state n).sizes s b (a.tilt n s) / 4 := by
        linarith [hE₀.trans hKePφ, hKuJφ, hDJlo b]
      -- second moments over the child support
      have hD0 : historyMass (a.state n).sizes s (a.tilt n s) ≠ 0 := hDpos.ne'
      have hφ0 : φStar n ≠ 0 := hφ.ne'
      have hM2 : ∀ i, |csecond (Local.trials (a.state n).sizes s) (a.tilt n s)
          (Local.childSupport (a.state n).sizes s b) (center p (a.state n).sizes) i t /
            childMass (a.state n).sizes s b (a.tilt n s)| ≤ Q * ((p : ℝ) * N) := by
        intro i
        have hsub := abs_csecond_subset_le (Local.trials (a.state n).sizes s) (a.tilt n s)
          (Local.childSupport_subset (a.state n).sizes s b) (center p (a.state n).sizes) i t
        have hdiag : ∀ j, csecond (Local.trials (a.state n).sizes s) (a.tilt n s)
            (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) j j ≤
            4 * (G₀ + 1) ^ 2 * ((p : ℝ) * N) := by
          intro j
          have hc := hcov j j
          have hEmj := hEmI j
          have hSig := hcovG s j j
          have hcov1 : |(csecond (Local.trials (a.state n).sizes s) (a.tilt n s)
              (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) j j /
                historyMass (a.state n).sizes s (a.tilt n s) -
              cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
                (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) j /
                  historyMass (a.state n).sizes s (a.tilt n s) *
                (cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
                  (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) j /
                  historyMass (a.state n).sizes s (a.tilt n s))) / ((p : ℝ) * N)| ≤ G₀ + 1 := by
            have := abs_sub_abs_le_abs_sub ((csecond (Local.trials (a.state n).sizes s) (a.tilt n s)
              (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) j j /
                historyMass (a.state n).sizes s (a.tilt n s) -
              cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
                (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) j /
                  historyMass (a.state n).sizes s (a.tilt n s) *
                (cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
                  (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) j /
                  historyMass (a.state n).sizes s (a.tilt n s))) / ((p : ℝ) * N))
              (conditionalCovariance n s j j)
            linarith
          rw [abs_div, abs_of_pos hpN, div_le_iff₀ hpN] at hcov1
          have hcov2 := (abs_le.mp hcov1).2
          have hsq := mul_le_mul hEmj hEmj (abs_nonneg _) (by positivity)
          rw [← abs_mul] at hsq
          have hsq2 := (abs_le.mp hsq).2
          have hcs : csecond (Local.trials (a.state n).sizes s) (a.tilt n s)
              (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) j j =
              historyMass (a.state n).sizes s (a.tilt n s) *
                (csecond (Local.trials (a.state n).sizes s) (a.tilt n s)
                  (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) j j /
                    historyMass (a.state n).sizes s (a.tilt n s) -
                  cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
                    (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) j /
                      historyMass (a.state n).sizes s (a.tilt n s) *
                    (cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
                      (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) j /
                      historyMass (a.state n).sizes s (a.tilt n s)) +
                  cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
                    (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) j /
                      historyMass (a.state n).sizes s (a.tilt n s) *
                    (cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
                      (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) j /
                      historyMass (a.state n).sizes s (a.tilt n s))) := by
            field_simp
            ring
          have hVS' : (G₀ + 1) * Real.sqrt ((p : ℝ) * N) * ((G₀ + 1) * Real.sqrt ((p : ℝ) * N)) =
              (G₀ + 1) ^ 2 * ((p : ℝ) * N) := sq_S_eq hVS
          rw [hVS'] at hsq2
          have hGV : (G₀ + 1) * ((p : ℝ) * N) ≤ (G₀ + 1) ^ 2 * ((p : ℝ) * N) := by
            apply mul_le_mul_of_nonneg_right _ hpN.le
            have h := mul_nonneg hG₀ (by linarith : (0 : ℝ) ≤ G₀ + 1)
            linarith only [h]
          have hsum : csecond (Local.trials (a.state n).sizes s) (a.tilt n s)
              (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) j j /
                historyMass (a.state n).sizes s (a.tilt n s) -
              cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
                (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) j /
                  historyMass (a.state n).sizes s (a.tilt n s) *
                (cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
                  (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) j /
                  historyMass (a.state n).sizes s (a.tilt n s)) +
              cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
                (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) j /
                  historyMass (a.state n).sizes s (a.tilt n s) *
                (cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
                  (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) j /
                  historyMass (a.state n).sizes s (a.tilt n s)) ≤
              2 * (G₀ + 1) ^ 2 * ((p : ℝ) * N) := by
            linarith [hcov2, hsq2, hGV]
          calc
            _ = _ := hcs
            _ ≤ historyMass (a.state n).sizes s (a.tilt n s) * (2 * (G₀ + 1) ^ 2 * ((p : ℝ) * N)) :=
              mul_le_mul_of_nonneg_left hsum hDpos.le
            _ ≤ 2 * (2 * (G₀ + 1) ^ 2 * ((p : ℝ) * N)) :=
              mul_le_mul_of_nonneg_right hDhi2 (by positivity)
            _ = _ := by ring
        have hboth : (csecond (Local.trials (a.state n).sizes s) (a.tilt n s)
            (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) i i +
            csecond (Local.trials (a.state n).sizes s) (a.tilt n s)
              (Local.historySupport (a.state n).sizes s) (center p (a.state n).sizes) t t) / 2 ≤
            4 * (G₀ + 1) ^ 2 * ((p : ℝ) * N) := by
          linarith [hdiag i, hdiag t]
        have hnum := hsub.trans hboth
        rw [abs_div, abs_of_pos (hDJpos b), div_le_iff₀ (hDJpos b)]
        have hDJ := hDJlo b
        rw [hQdef]
        have : 16 * (G₀ + 1) ^ 2 / φStar n ^ 2 * ((p : ℝ) * N) *
            childMass (a.state n).sizes s b (a.tilt n s) ≥
            16 * (G₀ + 1) ^ 2 / φStar n ^ 2 * ((p : ℝ) * N) * (φStar n ^ 2 / 4) :=
          mul_le_mul_of_nonneg_left hDJ (by positivity)
        have heq : 16 * (G₀ + 1) ^ 2 / φStar n ^ 2 * ((p : ℝ) * N) * (φStar n ^ 2 / 4) =
            4 * (G₀ + 1) ^ 2 * ((p : ℝ) * N) := by
          field_simp
          ring
        linarith [hnum, this, heq]
      have hEm2 : (G₀ + 1) * Real.sqrt ((p : ℝ) * N) * ((G₀ + 1) * Real.sqrt ((p : ℝ) * N)) ≤
          Q₂ * ((p : ℝ) * N) := by
        rw [hQ₂def]
        exact le_of_eq (sq_S_eq hVS)
      obtain ⟨hDen, hbound⟩ := child_clause (childMass (a.state n).sizes s b (a.tilt n s))
        (childMass sizes s b (processEffectiveTilt N p a n sizes s τ σ))
        (cfirst (Local.trials sizes s) (processEffectiveTilt N p a n sizes s τ σ)
          (Local.childSupport sizes s b) (center p (a.state n).sizes) t)
        (fun i => cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
          (Local.childSupport (a.state n).sizes s b) (center p (a.state n).sizes) i)
        (fun i => csecond (Local.trials (a.state n).sizes s) (a.tilt n s)
          (Local.childSupport (a.state n).sizes s b) (center p (a.state n).sizes) i t)
        (fun i => σ i)
        (tiltDifference p (a.state n).sizes (Local.trials (a.state n).sizes s)
          (Local.trials sizes s) (a.tilt n s) (processEffectiveTilt N p a n sizes s τ σ))
        (fun i => ∫ x, Binomial.Approximation.centered p (a.state n).sizes x i
          ∂Binomial.law (Local.trials (a.state n).sizes s) (a.tilt n s)) t
        (τ * betaScale N (p : ℝ) n) ((p : ℝ) * N) R Q Q₂
        ((Ku + 2 * Kus) * (N : ℝ) ^ (-responseRate θ n)) E₀ E₁ ((G₀ + 1) * Real.sqrt ((p : ℝ) * N))
        (hDJpos b) hb₀ hβ hσ hmassJ hfirstJ (hP'J b) hsmall hM2 (fun i => hEmJ b i) hEm2
      have hP'Jne : childMass sizes s b (processEffectiveTilt N p a n sizes s τ σ) ≠ 0 :=
        (lt_of_lt_of_le (half_pos (hDJpos b)) hDen).ne'
      have hlhs : childMean sizes s b (processEffectiveTilt N p a n sizes s τ σ) t -
          childMean (a.state n).sizes s b (a.tilt n s) t =
          cfirst (Local.trials sizes s) (processEffectiveTilt N p a n sizes s τ σ)
            (Local.childSupport sizes s b) (center p (a.state n).sizes) t /
            childMass sizes s b (processEffectiveTilt N p a n sizes s τ σ) -
          cfirst (Local.trials (a.state n).sizes s) (a.tilt n s)
            (Local.childSupport (a.state n).sizes s b) (center p (a.state n).sizes) t /
            childMass (a.state n).sizes s b (a.tilt n s) := by
        rw [childMean_eq_cfirst _ _ _ _ (center p (a.state n).sizes) t hP'Jne,
          childMean_eq_cfirst _ _ _ _ (center p (a.state n).sizes) t (hDJpos b).ne']
        ring
      rw [hlhs]
      refine hbound.trans ?_
      -- bound by `Cchild τβ₀pN`
      have hbV : 0 < τ * betaScale N (p : ℝ) n * ((p : ℝ) * N) := by positivity
      have hKSJ : (Fintype.card (History (n + 1)) : ℝ) *
          ((τ * betaScale N (p : ℝ) n * R) * ((Q + Q₂) * ((p : ℝ) * N))) =
          d * (R * (Q + Q₂)) * (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)) := by
        rw [hddef]
        ring
      have hE₁b : E₁ ≤ KeM * (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)) := by
        rw [div_le_iff₀ hbV] at hE₁
        have h2 : KeM * (N : ℝ) ^ (-responseRate θ n) * (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)) ≤
            KeM * 1 * (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΘ1 hKeM) hbV.le
        linarith
      have hue1 : (Ku + 2 * Kus) * (N : ℝ) ^ (-responseRate θ n) + E₀ ≤ 1 := by
        linarith [hE₀.trans hKePφ, hKuJφ, hφsq2]
      have hE₀1 : E₀ ≤ 1 := by linarith [hE₀.trans hKePφ, hφsq1]
      have hEPEm : E₀ * ((G₀ + 1) * Real.sqrt ((p : ℝ) * N)) ≤
          (G₀ + 1) * KeM * (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)) := by
        have hτx : 0 < τ * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N)) := mul_pos hτ0 hx
        rw [div_le_iff₀ hτx] at hE₀τ
        have hE₀τ' : E₀ ≤ KeM * (τ * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N))) := by
          have h2 : KeM * (N : ℝ) ^ (-responseRate θ n) *
              (τ * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N))) ≤
              KeM * 1 * (τ * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N))) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΘ1 hKeM) hτx.le
          linarith
        have hrew : (G₀ + 1) * KeM * (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)) =
            KeM * (τ * (betaScale N (p : ℝ) n * Real.sqrt ((p : ℝ) * N))) *
              ((G₀ + 1) * Real.sqrt ((p : ℝ) * N)) := child_norm_eq hVS
        rw [hrew]
        exact mul_le_mul_of_nonneg_right hE₀τ' (by positivity)
      have hKSJ0 : 0 ≤ d * (R * (Q + Q₂)) * (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)) := by
        positivity
      rw [hKSJ]
      have hA := mul_le_mul_of_nonneg_right hue1 hKSJ0
      have hB := mul_le_mul_of_nonneg_right hE₀1 hKSJ0
      have hinner : E₁ + ((Ku + 2 * Kus) * (N : ℝ) ^ (-responseRate θ n) + E₀) *
          (d * (R * (Q + Q₂)) * (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N))) +
          E₀ * ((G₀ + 1) * Real.sqrt ((p : ℝ) * N) +
            d * (R * (Q + Q₂)) * (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N))) ≤
          (KeM + d * (R * (Q + Q₂)) + (G₀ + 1) * KeM + d * (R * (Q + Q₂))) *
            (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)) := by
        linarith only [hE₁b, hA, hB, hEPEm]
      have hinner0 : 0 ≤ E₁ + ((Ku + 2 * Kus) * (N : ℝ) ^ (-responseRate θ n) + E₀) *
          (d * (R * (Q + Q₂)) * (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N))) +
          E₀ * ((G₀ + 1) * Real.sqrt ((p : ℝ) * N) +
            d * (R * (Q + Q₂)) * (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N))) := by positivity
      have hC8 : 0 ≤ 8 / φStar n ^ 2 := by positivity
      have hmul := mul_le_mul (h2DJ b) hinner hinner0 hC8
      calc
        _ ≤ d * (R * (Q + Q₂)) * (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)) +
            8 / φStar n ^ 2 * ((KeM + d * (R * (Q + Q₂)) + (G₀ + 1) * KeM + d * (R * (Q + Q₂))) *
              (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N))) := by linarith
        _ = Cchild * (τ * betaScale N (p : ℝ) n * ((p : ℝ) * N)) := by rw [hCchilddef]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hCchildC hbV.le
    · -- (iv) history nondegeneracy
      intro σ hσ
      obtain ⟨hP'D, _, _, _⟩ := hσblock σ hσ
      obtain ⟨ha, hb⟩ := abs_le.mp hP'D
      linarith [hKuφ, hφsq, ha, hb]
    · -- (iv) split nondegeneracy
      intro σ hσ b
      obtain ⟨_, hsplit', _, _⟩ := hσblock σ hσ
      obtain ⟨h1a, h1b⟩ := abs_le.mp (hsplit' b)
      obtain ⟨h2a, h2b⟩ := abs_le.mp (hsplit_ref b)
      obtain ⟨h3a, h3b⟩ := hr_bounds b
      have h4 := hKusφ
      have h5 := herφ
      constructor <;> linarith [h1a, h1b, h2a, h2b, h3a, h3b, h4, h5]
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (hev.and (eventually_ge_atTop 1))
  exact ⟨N₀, (hN₀ N₀ le_rfl).2, fun N hN => (hN₀ N hN).1⟩

/-- Lemma E.4 with the actual selected process exponent. -/
theorem linear_response : LinearResponseTheorem := by
  intro θ hθlo hθhi n hk T R hT hR
  exact linear_response_spec θ hθlo hθhi n hk T R hT hR (processExponent θ T)
    (processSelection_spec hθlo hθhi hT).1

/-- The literal real-density, integer-size statement for the constructed process. -/
theorem linear_response_real : LinearResponseRealTheorem := by
  intro θ hθlo hθhi n hk
  refine ⟨responseRate θ n, rfl, responseRate_pos hθlo hθhi hk, ?_⟩
  intro T R hT hR
  have hT0 : 0 < T := by linarith
  have hDlt := level_succ_lt_horizon hk
  obtain ⟨C, hC, N₀, hN₀, h⟩ := linear_response θ hθlo hθhi n hk T R hT hR
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    (eventually_geometry θ T hθlo hθhi hT n (processExponent θ T) 0 le_rfl hk)
  refine ⟨C, hC, max N₀ (max N₁ (processThreshold θ T)), hN₀.trans (le_max_left _ _), ?_⟩
  intro N hN p hp₀ hp₁
  have hNN₀ : N₀ ≤ N := (le_max_left _ _).trans hN
  have hNN₁ : N₁ ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hNth : processThreshold θ T ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  obtain ⟨hp, hspec, huniq⟩ := referenceData_agree hθlo hθhi hT hNth hp₀ hp₁
  have heq := referenceDataReal_eq (θ := θ) (T := T) (N := N) hp
  refine ⟨hp, heq, ?_, ?_, ?_⟩
  · rw [heq]
    exact hspec
  · rw [heq]
    exact huniq
  · intro τ hτ₁ hτ₂ η hη
    rw [heq] at hη ⊢
    have hden : Density θ T N ⟨p, hp⟩ := ⟨hp₀, hp₁⟩
    have hgeo := (hN₁ N hNN₁ ⟨p, hp⟩ hden).2 (referenceData θ T N ⟨p, hp⟩) (responseHorizon θ)
      hspec hDlt ((referenceData θ T N ⟨p, hp⟩).state n).sizes
      (fun t => by
        rw [sub_self, abs_zero]
        exact mul_nonneg hT0.le (sizeScale_nonneg _ _ _))
    have hpos : ∀ t, 0 < η t := by
      intro t
      obtain ⟨h1a, h1b⟩ := abs_le.mp (hη t)
      have h2 := hgeo.ref_lower t
      have h3 := hgeo.perturbation t
      have h4 : 0 ≤ (N : ℝ) * ν n t := mul_nonneg (Nat.cast_nonneg _) (ν_positive n t).le
      have : (0 : ℝ) < η t := by linarith [h1a, h1b, h2, h3, h4]
      exact_mod_cast this
    have hcast : ∀ t, (((η t).toNat : ℕ) : ℝ) = (η t : ℝ) := by
      intro t
      exact_mod_cast Int.toNat_of_nonneg (hpos t).le
    refine ⟨hpos, hcast, ?_⟩
    intro s
    apply h N hNN₀ ⟨p, hp⟩ hden _ hspec τ hτ₁ hτ₂ (fun t => (η t).toNat) _ s
    intro t
    show |(((η t).toNat : ℕ) : ℝ) - _| ≤ _
    rw [hcast t]
    exact hη t

end MajorityDynamics.Idealized.LinearResponse
