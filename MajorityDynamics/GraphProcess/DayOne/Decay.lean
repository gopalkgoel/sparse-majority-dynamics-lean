import MajorityDynamics.GraphProcess.RowConcentration.Asymptotics

noncomputable section
open Filter
namespace MajorityDynamics.GraphProcess.DayOne

/-- The day-one union-bound envelope has polynomially vanishing failure. -/
theorem eventually_failure_decay :
    ∀ᶠ N : ℕ in atTop,
      (4*(N : ℝ)+8) * Real.exp (-(3/80:ℝ) * Real.log (N : ℝ)^2) ≤
        (N : ℝ)^(-1:ℝ) := by
  obtain ⟨N₀,h₀⟩ := RowConcentration.eventually_log_tail
    (C := 12) (c := 3/80) (r := 2) (b := 1) (A := 1)
    (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop (1:ℕ)] with N hN hN1
  have hreal : (1:ℝ) ≤ N := by exact_mod_cast hN1
  calc
    _ ≤ 12*(N : ℝ) * Real.exp (-(3/80:ℝ) * Real.log (N : ℝ)^2) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _)
    _ ≤ _ := by simpa only [Real.rpow_one, Real.rpow_two] using h₀ N hN
end MajorityDynamics.GraphProcess.DayOne
