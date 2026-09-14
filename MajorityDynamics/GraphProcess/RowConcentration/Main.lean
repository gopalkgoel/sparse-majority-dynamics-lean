import MajorityDynamics.GraphProcess.RowConcentration.Assembly
import MajorityDynamics.GraphProcess.RowConcentration.Degree
import MajorityDynamics.GraphProcess.RowConcentration.Size
import MajorityDynamics.GraphProcess.RowConcentration.Mass

/-! The closed row-model stage of Proposition 3.9: all three errors have the
literal paper scale, uniformly to every polynomial decay power. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.RowConcentration
open Universal
universe u

/-- The original history-conditioned row law satisfies R1, R2 and R3 jointly
with superpolynomial probability. The threshold is uniform in the graph carrier,
density, coarse data and tilts. No exact-count conditioning or transfer premise
is assumed. In fact this holds for every real decay power and positive history
mass lower bound, a slightly stronger parameter range than the paper uses. -/
theorem uniform_concentration {θ T φ A : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hφ : 0 < φ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(q s t : ℝ)-p| ≤ T*p/Real.sqrt (p*N)) →
      Conditioning y q φ →
      (conditionedLaw y q).real {d | ¬ Good y p q d} ≤ (N : ℝ)^(-A) := by
  let h : ℝ := Fintype.card (History (n + 1))
  have hh : 0 < h := by
    dsimp [h]
    rw [history_card]
    positivity
  obtain ⟨N₁, h₁⟩ := uniform_degree_tail (A := (4 : ℝ)) n hθlo hθhi hT hφ
  obtain ⟨N₂, h₂⟩ := uniform_degree_tail (A := A + 1) n hθlo hθhi hT hφ
  obtain ⟨N₃, h₃⟩ := eventually_tolerance_le hθlo hθhi hT
  obtain ⟨N₄, h₄⟩ := eventually_mass_bias hθlo hθhi hT
  obtain ⟨N₅, h₅⟩ := eventually_log_tail
    (C := 4*h) (c := 2) (r := 2) (b := 0) (A := A+1)
    (by positivity) (by norm_num) (by norm_num)
  obtain ⟨N₆, h₆⟩ := eventually_log_tail
    (C := 4*h^2) (c := 1/8) (r := 2) (b := 0) (A := A+1)
    (by positivity) (by norm_num) (by norm_num)
  obtain ⟨N₇, h₇⟩ := exists_nat_gt (3 + 2*h^2)
  refine ⟨max N₁ (max N₂ (max N₃ (max N₄ (max N₅ (max N₆ N₇))))), ?_⟩
  intro N hN V inst hcard p hlo hhi y q hsizes htilt hc
  have hd₄ := h₁ N (by omega) V hcard p hlo hhi y q hsizes htilt hc
  have hd := h₂ N (by omega) V hcard p hlo hhi y q hsizes htilt hc
  have hr := h₃ N (by omega) p hlo hhi
  have hb := h₄ N (by omega) p hlo hhi
  have ht₂ := h₅ N (by omega)
  have ht₃ := h₆ N (by omega)
  simp only [Real.rpow_zero, mul_one, Real.rpow_two] at ht₂ ht₃
  have hC : 3 + 2*h^2 ≤ (N : ℝ) :=
    h₇.le.trans (by exact_mod_cast (show N₇ ≤ N by omega))
  have hNr := hr.2.1
  have hNN : 0 < Fintype.card V := by rw [hcard]; exact_mod_cast hNr
  have hlog : 0 ≤ Real.log (Fintype.card V) := by rw [hcard]; linarith [hr.2.2.1]
  have htol : Real.sqrt (p * Fintype.card V) *
      (Real.log (Fintype.card V)) ^ (2 / 3 : ℝ) ≤ p * Fintype.card V := by
    simpa only [hcard] using hr.2.2.2
  have hbias : (Fintype.card V : ℝ)^2 * (conditionedLaw y q).real {d | ¬ R1 y p d} ≤
      ((Fintype.card V : ℝ)^2 * p / Real.sqrt (Fintype.card V) *
        Real.log (Fintype.card V)) / 2 := by
    rw [hcard]
    exact (mul_le_mul_of_nonneg_left hd₄ (sq_nonneg _)).trans hb
  have hs := R2_failure y q hφ hc hNN hlog
  have hm := R3_failure y hr.1 q hφ hc hNN hlog htol hbias
  have hj := failure_union_le y p q hφ hc
  rw [hcard] at hs hm
  change (conditionedLaw y q).real {d | ¬ R2 y q d} ≤
    (h*2)*(2*Real.exp (-2*(Real.log (N : ℝ))^2)) at hs
  change (conditionedLaw y q).real {d | ¬ R3 y p q d} ≤
    (h^2*2)*((conditionedLaw y q).real {d | ¬ R1 y p d} +
      2*Real.exp (-(Real.log (N : ℝ))^2/8)) at hm
  have he₃ : -(1/8 : ℝ)*(Real.log (N : ℝ))^2 =
      -(Real.log (N : ℝ))^2/8 := by ring
  rw [he₃] at ht₃
  have hs' : (conditionedLaw y q).real {d | ¬ R2 y q d} ≤ (N : ℝ)^(-(A+1)) := by
    nlinarith
  have hmd := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ h^2*2)
  have hout : (conditionedLaw y q).real {d | ¬ Good y p q d} ≤
      (3+2*h^2)*(N : ℝ)^(-(A+1)) := by nlinarith
  exact hout.trans (polynomial_absorption hNr hC)

end MajorityDynamics.GraphProcess.RowConcentration
