import MajorityDynamics.Idealized.CriticalDay.TerminalFaithfulBudget
import MajorityDynamics.Idealized.CriticalDay.FlexibleScales

noncomputable section
open Filter Topology
namespace MajorityDynamics.Idealized.CriticalDay
open Binomial.Approximation

/-- One common eventual threshold controls the gain-relative terminal error
and the absolute smallness needed by the finite faithful-target expansion. -/
theorem terminal_error_small_uniform (θ T r δ C K ε radius : ℝ) (k : ℕ)
    (hθ : θ < 1) (hT : 0 < T) (hr : 0 < r) (hr3 : r ≤ 1/3)
    (hgap : r/4 < δ) (hC : 0 < C) (hK : 0 < K)
    (hε : 0 < ε) (hradius : 0 < radius) :
    ∀ᶠ N : ℕ in atTop, 0 < N ∧ 1 ≤ Real.log (N:ℝ) ∧
      ∀ p : Binomial.Probability, SparseRange θ T N p →
      ∀ a : ℝ, 0 < a → scale N p^r ≤ a*scale N p → a ≤ scale N p^r →
      0 < terminalError (scale N p) a (Real.log N^k) ((N:ℝ)^(-δ)) ∧
      C*terminalError (scale N p) a (Real.log N^k) ((N:ℝ)^(-δ)) ≤ ε*min a 1 ∧
      K*(Real.log N^k/scale N p+a/scale N p+(N:ℝ)^(-δ)) < radius := by
  let η := min (ε/C) (radius/(8*K))
  have hη : 0 < η := by dsimp [η]; positivity
  have hδ : 0 < δ := lt_trans (by positivity : 0 < r/4) hgap
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [eventually_gt_atTop (0:ℕ),hlog,
    uniform_flexible_terminal_budget θ T r δ 1 η k hθ hT hr hr3 hgap zero_le_one hη,
    LinearResponse.eventually_rpow_neg_le δ (radius/(4*K)) hδ (by positivity)]
    with N hN hlog hbudget hqsmall
  refine ⟨hN,hlog,?_⟩
  intro p hp a ha halo hahi
  have hs : 0 < scale N p := Real.sqrt_pos.mpr
    (mul_pos p.property.1 (Nat.cast_pos.mpr hN))
  have hl : 1 ≤ Real.log N^k := one_le_pow₀ hlog
  have hq : 0 ≤ (N:ℝ)^(-δ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hW := terminalError_controls hs ha.le hl hq
  have hW0 : 0 < terminalError (scale N p) a (Real.log N^k) ((N:ℝ)^(-δ)) :=
    (div_pos (zero_lt_one.trans_le hl) hs).trans_le hW.2.1
  have hmin : 0 < min a 1 := lt_min ha zero_lt_one
  have hh := hbudget p hp a ((N:ℝ)^(-δ)) ha halo hahi hq (by simp)
  change terminalError (scale N p) a (Real.log N^k) ((N:ℝ)^(-δ))/min a 1 ≤ η at hh
  have hwη := (div_le_iff₀ hmin).mp hh
  have hwabs : terminalError (scale N p) a (Real.log N^k) ((N:ℝ)^(-δ)) ≤ η :=
    hwη.trans (by nlinarith only [min_le_right a 1,hη])
  refine ⟨hW0,?_,?_⟩
  · have hb := hwη.trans (mul_le_mul_of_nonneg_right
      (show η ≤ ε/C from min_le_left _ _) hmin.le)
    have hc := mul_le_mul_of_nonneg_left hb hC.le
    have hid : C*(ε/C*min a 1) = ε*min a 1 := by field_simp
    rwa [hid] at hc
  · have hw := hwabs.trans (show η ≤ radius/(8*K) from min_le_right _ _)
    have hKraw := mul_le_mul_of_nonneg_left (hW.2.1.trans hw) hK.le
    have hKbeta := mul_le_mul_of_nonneg_left (hW.2.2.1.trans hw) hK.le
    have hKq := mul_le_mul_of_nonneg_left hqsmall hK.le
    have hid8 : K*(radius/(8*K)) = radius/8 := by field_simp
    have hid4 : K*(radius/(4*K)) = radius/4 := by field_simp
    rw [hid8] at hKraw hKbeta
    rw [hid4] at hKq
    nlinarith only [hKraw,hKbeta,hKq,hradius]

end MajorityDynamics.Idealized.CriticalDay

