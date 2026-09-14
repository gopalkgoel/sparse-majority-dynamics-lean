import MajorityDynamics.Idealized.CriticalDay.Target
import MajorityDynamics.Idealized.PerturbedEvolution.TemplateRates

/-! Faithful centering with an explicit error budget, independent of any
critical exponent or density window. This preserves the response multiplier
instead of bounding it by a constant. -/
noncomputable section
open scoped BigOperators
namespace MajorityDynamics.Idealized.CriticalDay
open Universal LinearResponse PerturbedTilt
open Binomial.Approximation (scale)

structure FaithfulBudgetData (N : ℕ) (p τ E : ℝ) (a : Process.Data) (n : ℕ)
    (η : History (n + 1) → ℤ) (e : History (n + 1) → History (n + 1) → ℤ) : Prop where
  sizes : ∀ s, |(η s : ℝ) - ((a.state n).sizes s : ℝ) -
      τ * sizeScale N p n * ε n s| ≤ τ * sizeScale N p n * E
  edges : ∀ s t, |(e s t : ℝ) - (a.state n).edges s t *
      (1 + τ * betaScale N p n * (ε n s / ν n s + ε n t / ν n t))| ≤
        τ * betaScale N p n * E * (N : ℝ) ^ 2 * p

theorem faithful_target_budget (n : ℕ) :
    ∃ radius : ℝ, 0 < radius ∧ ∃ K : ℝ, 0 < K ∧
    ∀ (N : ℕ) (p τ E : ℝ), 0 < N → 0 < p → 0 < τ → 0 ≤ E → E < radius →
    ∀ a : Process.Data,
    (∀ s, 0 < (a.state n).sizes s) →
    (∀ s, |((a.state n).sizes s : ℝ) / N - ν n s| ≤ E) →
    (∀ s t, |(a.state n).edges s t / (p * (N : ℝ) ^ 2) - ν n s * ν n t| ≤ E) →
    τ * betaScale N p n ≤ E →
    ∀ (η : History (n + 1) → ℤ) (e : History (n + 1) → History (n + 1) → ℤ),
    (∀ s, 0 < η s) → FaithfulBudgetData N p τ E a n η e →
    ∀ s t, |edgeTarget N p a τ η e s t - ε n t| ≤ K * E := by
  classical
  have hsingle (z : History (n + 1) × History (n + 1)) :=
    target_scalar_control (ν_positive n z.1) (ν_positive n z.2) (ε n z.1) (ε n z.2)
  choose radius hr K hK hctl using hsingle
  obtain ⟨r, hr, hrlower⟩ := RowLimits.finite_common_positive radius hr
  let K₀ := 1 + ∑ z, |K z|
  have hK₀ : 0 < K₀ := by dsimp [K₀]; positivity
  have hKbound (z) : K z ≤ K₀ := by
    have hh := Finset.single_le_sum (fun z => fun _ => abs_nonneg (K z)) (Finset.mem_univ z)
    dsimp [K₀]
    linarith [le_abs_self (K z)]
  refine ⟨r, hr, K₀, hK₀, ?_⟩
  intro N p τ E hN hp hτ hE hEr a hsz hrefsz hrefedge hb η e hη hf s t
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hβ : 0 < betaScale N p n := by unfold betaScale; positivity
  have hS : 0 < sizeScale N p n := by unfold sizeScale; positivity
  have hns : (0 : ℝ) < (a.state n).sizes s := by exact_mod_cast hsz s
  have hηs : (0 : ℝ) < η s := by exact_mod_cast hη s
  have hscale : sizeScale N p n = betaScale N p n * N := sizeScale_eq N hN p n
  have hnum : |((η s : ℝ) - ((a.state n).sizes s : ℝ)) /
      (τ * betaScale N p n * N) - ε n s| ≤ E := by
    have heq : ((η s : ℝ) - ((a.state n).sizes s : ℝ)) /
        (τ * betaScale N p n * N) - ε n s =
      ((η s : ℝ) - ((a.state n).sizes s : ℝ) - τ * sizeScale N p n * ε n s) /
        (τ * sizeScale N p n) := by
      rw [hscale]
      field_simp
    rw [heq, abs_div, abs_of_pos (mul_pos hτ hS)]
    exact (div_le_iff₀ (mul_pos hτ hS)).mpr (by simpa [mul_comm] using hf.sizes s)
  have hedge : |((e s t : ℝ) - (a.state n).edges s t *
      (1 + τ * betaScale N p n * (ε n s / ν n s + ε n t / ν n t))) /
        (τ * betaScale N p n * p * (N : ℝ) ^ 2)| ≤ E := by
    rw [abs_div, abs_of_pos (by positivity : 0 < τ * betaScale N p n * p * (N : ℝ) ^ 2)]
    apply (div_le_iff₀ (by positivity : 0 < τ * betaScale N p n * p * (N : ℝ) ^ 2)).mpr
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hf.edges s t
  let x : Fin 5 → ℝ := ![((a.state n).sizes s : ℝ) / N,
    (a.state n).edges s t / (p * (N : ℝ) ^ 2), τ * betaScale N p n,
    ((η s : ℝ) - ((a.state n).sizes s : ℝ)) / (τ * betaScale N p n * N) - ε n s,
    ((e s t : ℝ) - (a.state n).edges s t *
      (1 + τ * betaScale N p n * (ε n s / ν n s + ε n t / ν n t))) /
        (τ * betaScale N p n * p * (N : ℝ) ^ 2)]
  have hx : ∀ i, |x i - targetPoint (ν n s) (ν n t) i| ≤ E := by
    intro i
    fin_cases i
    · exact hrefsz s
    · exact hrefedge s t
    · simpa [x, targetPoint, abs_of_pos (mul_pos hτ hβ)] using hb
    · simpa [x, targetPoint] using hnum
    · simpa [x, targetPoint] using hedge
  have hc := hctl (s, t) E hE (hEr.trans_le (hrlower (s, t))) x hx
  have heq : targetFunction (ν n s) (ν n t) (ε n s) (ε n t) x =
      edgeTarget N p a τ η e s t :=
    target_rescale hn.ne' hp.ne' (mul_pos hτ hβ).ne' hns.ne' hηs.ne' _ _ _ _
  rw [heq] at hc
  exact hc.trans (mul_le_mul_of_nonneg_right (hKbound (s, t)) hE)

/-- Exact centering cancellation and its explicit amplified error. -/
theorem centered_target_budget {n N : ℕ} (hN : 0 < N) (p : Binomial.Probability)
    (a : Process.Data) {τ E R K : ℝ} (hτ : 0 < τ) (hE : 0 ≤ E)
    (η : History (n + 1) → ℤ) (e : History (n + 1) → History (n + 1) → ℤ)
    (hf : FaithfulBudgetData N p τ E a n η e)
    (href : ∀ s t, |((a.state n).edges s t / (a.state n).sizes s -
      (p : ℝ) * (a.state n).sizes t) / scale N p - ν n t * μ n s t| ≤ R)
    (htarget : ∀ s t, |edgeTarget N p a τ η e s t - ε n t| ≤ K * E) :
    ∀ s t, |((e s t : ℝ) / (η s : ℝ) - (p : ℝ) * (η t : ℝ)) / scale N p -
      ν n t * μ n s t| ≤ R + τ * (betaScale N p n * scale N p) * (K + 1) * E := by
  intro s t
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hp0 := p.property.1
  have hs : 0 < scale N p := Real.sqrt_pos.mpr (mul_pos p.property.1 hn)
  have hβ : 0 < betaScale N p n := by unfold betaScale; positivity
  have hsq : scale N p ^ 2 = (p : ℝ) * N := Real.sq_sqrt (by positivity)
  have hsc : sizeScale N p n = betaScale N p n * N := sizeScale_eq N hN p n
  have htarget' : |τ * betaScale N p n * scale N p *
      (edgeTarget N p a τ η e s t - ε n t)| ≤
        τ * (betaScale N p n * scale N p) * K * E := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < τ * betaScale N p n * scale N p)]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (htarget s t)
      (show 0 ≤ τ * betaScale N p n * scale N p by positivity)
  have hfaith : |(p : ℝ) / scale N p *
      ((η t : ℝ) - (a.state n).sizes t - τ * sizeScale N p n * ε n t)| ≤
        τ * (betaScale N p n * scale N p) * E := by
    rw [abs_mul, abs_of_pos (div_pos p.property.1 hs)]
    have hh := mul_le_mul_of_nonneg_left (hf.sizes t) (div_pos p.property.1 hs).le
    have hid : (p : ℝ) / scale N p * (τ * sizeScale N p n * E) =
        τ * (betaScale N p n * scale N p) * E := by
      rw [hsc]
      field_simp
      nlinarith [hsq]
    rwa [hid] at hh
  have hid : ((e s t : ℝ) / (η s : ℝ) - (p : ℝ) * (η t : ℝ)) / scale N p - ν n t * μ n s t =
      (((a.state n).edges s t / (a.state n).sizes s - (p : ℝ) * (a.state n).sizes t) /
        scale N p - ν n t * μ n s t) +
      τ * betaScale N p n * scale N p * (edgeTarget N p a τ η e s t - ε n t) -
      (p : ℝ) / scale N p * ((η t : ℝ) - (a.state n).sizes t -
        τ * sizeScale N p n * ε n t) := by
    dsimp [edgeTarget]
    rw [hsc, ← hsq]
    field_simp
    rw [hsq]
    ring
  rw [hid]
  have hh := (abs_sub _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add (href s t) htarget')) hfaith)
  exact hh.trans_eq (by ring)

end MajorityDynamics.Idealized.CriticalDay
