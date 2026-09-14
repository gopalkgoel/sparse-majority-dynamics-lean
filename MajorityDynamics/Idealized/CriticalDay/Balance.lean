import MajorityDynamics.Idealized.CriticalDay.Geometry
import MajorityDynamics.Idealized.PerturbedEvolution.AdmissibilitySizes
import MajorityDynamics.Universal.Section4

noncomputable section
open Filter Topology
open scoped BigOperators
namespace MajorityDynamics.Idealized.CriticalDay
open Universal LinearResponse PerturbedTilt
open Binomial.Approximation (Density scale)

def lead (n : ℕ) : ℝ := ∑ t, character (Fin.last n) t * ε n t

theorem lead_pos (n : ℕ) : 0 < lead n := ε_lead_positive n

theorem faithful_lead_error {n N : ℕ} {p T δ τ : ℝ} {a : Process.Data}
    {η : History (n + 1) → ℤ} {e : History (n + 1) → History (n + 1) → ℤ}
    (hsym : Process.StateSymmetric (a.state n))
    (hf : FaithfulNumericalData N p T δ τ a n η e) :
    |(∑ t, character (Fin.last n) t * (η t : ℝ)) - τ * sizeScale N p n * lead n| ≤
      (Fintype.card (History (n + 1)) : ℝ) * (T * sizeScale N p n * (N : ℝ) ^ (-δ)) := by
  have href : (∑ t, character (Fin.last n) t * ((a.state n).sizes t : ℝ)) = 0 :=
    Process.symmetric_imbalance_eq_zero (a.state n) hsym (Fin.last n)
  have hid : (∑ t, character (Fin.last n) t *
      ((η t : ℝ) - (a.state n).sizes t - τ * sizeScale N p n * ε n t)) =
      (∑ t, character (Fin.last n) t * (η t : ℝ)) - τ * sizeScale N p n * lead n := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [href, sub_zero]
    congr 1
    unfold lead
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [← hid]
  simpa only [one_mul] using abs_sum_mul_le' (character (Fin.last n))
    (fun t => (η t : ℝ) - (a.state n).sizes t - τ * sizeScale N p n * ε n t)
    1 (T * sizeScale N p n * (N : ℝ) ^ (-δ))
    (fun t => (abs_character (Fin.last n) t).le) hf.sizes

theorem faithful_shift_error {n N : ℕ} {p : Binomial.Probability} {T δ τ : ℝ}
    {a : Process.Data} {η : History (n + 1) → ℤ}
    {e : History (n + 1) → History (n + 1) → ℤ}
    (hN : 0 < N) (hsym : Process.StateSymmetric (a.state n))
    (hcast : ∀ t, ((naturalSizes η t : ℕ) : ℝ) = (η t : ℝ))
    (hf : FaithfulNumericalData N (p : ℝ) T δ τ a n η e) :
    |RowLimits.shift N p (naturalSizes η) -
      τ * betaScale N (p : ℝ) n * scale N p * lead n| ≤
      (Fintype.card (History (n + 1)) : ℝ) * T *
        (betaScale N (p : ℝ) n * scale N p) * (N : ℝ) ^ (-δ) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hp0 := p.property.1
  have hS : 0 < scale N p := Real.sqrt_pos.mpr (by positivity)
  have hsq : scale N p ^ 2 = (p : ℝ) * N := Real.sq_sqrt (by positivity)
  have hsc := sizeScale_eq N hN (p : ℝ) n
  have he := mul_le_mul_of_nonneg_left (faithful_lead_error hsym hf) (div_pos hp0 hS).le
  have hi : (p : ℝ) / scale N p * sizeScale N (p : ℝ) n =
      betaScale N (p : ℝ) n * scale N p := by
    rw [hsc]
    field_simp
    linear_combination -(betaScale N (p : ℝ) n) * hsq
  have hs : RowLimits.shift N p (naturalSizes η) =
      (p : ℝ) / scale N p * ∑ t, character (Fin.last n) t * (η t : ℝ) := by
    unfold RowLimits.shift RowLimits.nextImbalance RowLimits.sizeVector imbalance
    simp only [hcast]
    unfold scale
    ring
  rw [hs]
  have hleft : (p : ℝ) / scale N p * ∑ t, character (Fin.last n) t * (η t : ℝ) -
      τ * betaScale N (p : ℝ) n * scale N p * lead n =
      (p : ℝ) / scale N p * ((∑ t, character (Fin.last n) t * (η t : ℝ)) -
        τ * sizeScale N (p : ℝ) n * lead n) := by
    rw [mul_sub]
    linear_combination (τ * lead n) * hi
  rw [hleft, abs_mul, abs_of_pos (div_pos hp0 hS)]
  have hright : (p : ℝ) / scale N p *
      ((Fintype.card (History (n + 1)) : ℝ) * (T * sizeScale N (p : ℝ) n * (N : ℝ) ^ (-δ))) =
      (Fintype.card (History (n + 1)) : ℝ) * T *
        (betaScale N (p : ℝ) n * scale N p) * (N : ℝ) ^ (-δ) := by
    linear_combination (Fintype.card (History (n + 1)) : ℝ) * T * (N : ℝ) ^ (-δ) * hi
  rw [hright] at he
  exact he

/-- Positive shift constants are selected before delta. -/
theorem faithful_shift_window (θ T : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (n ell : ℕ) (hk : (n : ℝ) + 1 = 1 / (1 - θ)) :
    ∃ lo hi : ℝ, 0 < lo ∧ lo ≤ hi ∧
    ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop,
    ∀ p : Binomial.Probability, Density θ T N p →
    ∀ a : Process.Data, Process.Specification N p (responseHorizon θ) ell a →
    ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
    ∀ η : History (n + 1) → ℤ, ∀ e : History (n + 1) → History (n + 1) → ℤ,
    FaithfulNumericalData N (p : ℝ) T δ τ a n η e →
    lo ≤ RowLimits.shift N p (naturalSizes η) ∧
      RowLimits.shift N p (naturalSizes η) ≤ hi := by
  let B := Real.sqrt T ^ (n + 1)
  let L := (Real.sqrt T)⁻¹ ^ (n + 1)
  let lo := T⁻¹ * L * lead n / 2
  let hi := T * B * lead n + lo
  let C := (Fintype.card (History (n + 1)) : ℝ) * T * B
  have hT0 : 0 < T := by linarith
  have hB : 0 < B := by dsimp [B]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hl : 0 < lead n := lead_pos n
  have hlo : 0 < lo := by dsimp [lo]; positivity
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (mul_pos (Nat.cast_pos.mpr Fintype.card_pos) hT0) hB
  refine ⟨lo, hi, hlo, by dsimp [hi]; linarith [mul_pos (mul_pos hT0 hB) hl], ?_⟩
  intro δ hδ
  filter_upwards [faithful_geometry θ T δ hθlo hθhi hT hδ n ell hk,
    eventually_gt_atTop (0 : ℕ),
    eventually_rpow_neg_le δ (lo / C) hδ (div_pos hlo hC)] with N hgeo hN hsmall
  intro p hp a ha τ hτ hτT η e hf
  obtain ⟨_, hcast, _, _⟩ := hgeo p hp a ha τ hτ hτT η e hf
  have hτ0 : 0 < τ := (inv_pos.mpr hT0).trans_le hτ
  obtain ⟨hbL, hbU⟩ := critical_scale_bounds hN hT0 hp hk hθhi
  change L ≤ betaScale N (p : ℝ) n * scale N p at hbL
  change betaScale N (p : ℝ) n * scale N p ≤ B at hbU
  have hb0 : 0 < betaScale N (p : ℝ) n * scale N p := hL.trans_le hbL
  have herr := faithful_shift_error hN
    (ha.symmetry n (Nat.lt_of_succ_lt (critical_level_lt_horizon hk))) hcast hf
  have herror : |RowLimits.shift N p (naturalSizes η) -
      τ * betaScale N (p : ℝ) n * scale N p * lead n| ≤ lo := by
    have h1 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hbU (show 0 ≤ (Fintype.card (History (n + 1)) : ℝ) * T by positivity))
      (Real.rpow_nonneg (Nat.cast_nonneg N) (-δ))
    have h2 := mul_le_mul_of_nonneg_left hsmall hC.le
    have heq : C * (lo / C) = lo := by field_simp
    rw [heq] at h2
    exact herr.trans (h1.trans h2)
  have hloMain : 2 * lo ≤ τ * betaScale N (p : ℝ) n * scale N p * lead n := by
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul hτ hbL hL.le hτ0.le) hl.le
    dsimp [lo]
    nlinarith [hh]
  have hhiMain : τ * betaScale N (p : ℝ) n * scale N p * lead n ≤ T * B * lead n := by
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul hτT hbU hb0.le hT0.le) hl.le
    nlinarith [hh]
  obtain ⟨heL, heU⟩ := abs_le.mp herror
  dsimp [hi]
  constructor <;> linarith

end MajorityDynamics.Idealized.CriticalDay
