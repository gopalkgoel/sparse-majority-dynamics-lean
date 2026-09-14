import MajorityDynamics.GraphProcess.RowConcentration.Main
import MajorityDynamics.Local.Admissibility

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace MajorityDynamics.GraphProcess.RowExactTotals
open Universal
universe u

/-- The actual R1 tolerance eventually fits inside the original kappa tolerance,
uniformly throughout the original density window. -/
theorem eventually_regular_tolerance {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      Real.sqrt (p*N)*(Real.log (N : ℝ))^((2:ℝ)/3) ≤ (p*N)^((4:ℝ)/7) := by
  have hT0 : 0 < T := by linarith
  have hc : 0 < (T⁻¹)^((1:ℝ)/14) := Real.rpow_pos_of_pos (inv_pos.mpr hT0) _
  have ht : Tendsto (fun N : ℕ => (Real.log (N : ℝ))^((2:ℝ)/3) /
      (N : ℝ)^((1-θ)/14)) atTop (𝓝 0) := by
    exact (isLittleO_log_rpow_rpow_atTop ((2:ℝ)/3)
      (by linarith : 0 < (1-θ)/14)).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₁,h₁⟩ := eventually_atTop.mp (ht.eventually (eventually_lt_nhds hc))
  obtain ⟨N₂,h₂⟩ := EnumerationBounds.eventually_window hθlo hθhi hT
    (L := 1) zero_lt_one (U := 1) zero_lt_one (M := 1) zero_lt_one
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN p hlo hhi
  have hw := h₂ N (by omega) p hlo hhi
  have hNp := hw.1
  have hp := hw.2.1
  have hlog := (div_lt_iff₀ (Real.rpow_pos_of_pos hNp ((1-θ)/14))).mp (h₁ N (by omega))
  have hlow : T⁻¹*(N : ℝ)^(1-θ) ≤ p*N := by
    have hh := mul_le_mul_of_nonneg_right hlo.le hNp.le
    have hid : (N : ℝ)^(-θ) * N = (N : ℝ)^(1-θ) := by
      calc
        _ = (N : ℝ)^(-θ) * (N : ℝ)^(1:ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hNp]; congr 1; ring
    simpa only [mul_assoc, hid] using hh
  have hpow : (T⁻¹)^((1:ℝ)/14) * (N : ℝ)^((1-θ)/14) ≤ (p*N)^((1:ℝ)/14) := by
    have hh := Real.rpow_le_rpow (by positivity : 0 ≤ T⁻¹*(N : ℝ)^(1-θ)) hlow
      (by norm_num : (0:ℝ) ≤ 1/14)
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hNp.le] at hh
    simpa only [mul_one_div] using hh
  calc
    _ ≤ Real.sqrt (p*N) * (p*N)^((1:ℝ)/14) :=
      mul_le_mul_of_nonneg_left (hlog.le.trans hpow) (Real.sqrt_nonneg _)
    _ = (p*N)^((4:ℝ)/7) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add (mul_pos hp hNp)]
      norm_num

theorem R1_regular {V : Type*} [Fintype V] {n : ℕ}
    (y : Local.CoarseData V n) (p : ℝ)
    (hscale : Real.sqrt (p*Fintype.card V)*(Real.log (Fintype.card V))^((2:ℝ)/3) ≤
      (p*Fintype.card V)^((4:ℝ)/7))
    (d : RowArray.Ambient y.part) (hd : RowConcentration.R1 y p d) :
    RowArray.Regular p d := by
  intro v t
  exact (hd v t).trans hscale

/-- The first B.6 conclusion, with the original full local-admissibility inputs. -/
theorem uniform_history_regularity {θ T φ A : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      Local.CoreAdmissible y q T φ p →
      (RowConcentration.conditionedLaw y q).real {d | ¬ RowArray.Regular p d} ≤
        (N : ℝ)^(-A) := by
  obtain ⟨N₁,h₁⟩ := eventually_regular_tolerance hθlo hθhi hT
  obtain ⟨N₂,h₂⟩ := RowConcentration.uniform_concentration (A := A) n hθlo hθhi hT hφ
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN V inst hcard p hlo hhi y q ha
  have hc := h₂ N (by omega) V hcard p hlo hhi y q
    (fun s => by simpa only [← hcard, div_eq_mul_inv, mul_comm] using ha.sizes s)
    (fun s t => by simpa only [← hcard] using ha.tilt s t) ha.conditioning
  have hs : Real.sqrt (p*Fintype.card V)*(Real.log (Fintype.card V))^((2:ℝ)/3) ≤
      (p*Fintype.card V)^((4:ℝ)/7) := by
    rw [hcard]
    exact h₁ N (by omega) p hlo hhi
  let := RowConcentration.conditioned_probability y q hφ ha.conditioning
  apply le_trans (measureReal_mono (show {d | ¬ RowArray.Regular p d} ⊆
      {d | ¬ RowConcentration.Good y p q d} from ?_)) hc
  intro d hd hg
  exact hd (R1_regular y p hs d hg.1)

end MajorityDynamics.GraphProcess.RowExactTotals

/-- info: 'MajorityDynamics.GraphProcess.RowExactTotals.eventually_regular_tolerance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowExactTotals.eventually_regular_tolerance

/-- info: 'MajorityDynamics.GraphProcess.RowExactTotals.R1_regular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowExactTotals.R1_regular

/-- info: 'MajorityDynamics.GraphProcess.RowExactTotals.uniform_history_regularity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.RowExactTotals.uniform_history_regularity
