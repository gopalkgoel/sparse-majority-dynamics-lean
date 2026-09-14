import MajorityDynamics.GraphProcess.NonLumpability.Graphs

noncomputable section
open scoped BigOperators
namespace MajorityDynamics.GraphProcess.NonLumpability
open Universal FineState History CoarseKernel

/-- The existing regularity threshold is at least two at N=8,p=1/2. -/
theorem threshold_lower : (2 : ℝ) ≤ (4 : ℝ) ^ (4 / 7 : ℝ) := by
  have h : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [← Real.sqrt_eq_rpow]
    norm_num
  rw [← h]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)

theorem state_regular (variant : Bool) :
    Regular (1 / 2) (state variant).part (state variant).deg := by
  intro v t
  rw [← label_exhaust t, state_part, partition_size, state_degree]
  have hb := rawDegree_bounds variant v (bits 1 t 0)
  have h0 : (0 : ℝ) ≤ rawDegree variant v (bits 1 t 0) := by exact_mod_cast hb.1
  have h3 : (rawDegree variant v (bits 1 t 0) : ℝ) ≤ 3 := by exact_mod_cast hb.2
  have ha : |(rawDegree variant v (bits 1 t 0) : ℝ) - 2| ≤ 2 := by
    rw [abs_le]; constructor <;> linarith
  norm_num only [Fintype.card_fin, Nat.cast_ofNat]
  exact ha.trans threshold_lower

theorem state_reg (variant : Bool) : (rho (1 / 2) (state variant)).reg = true :=
  (flag_true _ _ _).mpr (state_regular variant)

/-- Equality of all fields of the existing coarse carrier, including κ. -/
theorem same_coarse : rho (1 / 2) (state false) = rho (1 / 2) (state true) := by
  apply coarse_ext
  · simp only [rho_part, state_part]
  · funext s t
    rw [rho_edge, rho_edge, ← label_exhaust s, ← label_exhaust t, state_edges, state_edges]
  · rw [state_reg, state_reg]

set_option maxHeartbeats 1000000 in
/-- Only vertex zero changes color in the second graph. -/
theorem next_color (variant : Bool) (v : Fin 8) :
    Probability.RandomOpinionsReduction.nextColoringV (graph variant) coloring v =
      if variant = true ∧ v = 0 then true else coloring v := by
  simp only [Probability.RandomOpinionsReduction.nextColoringV,
    Fin.sum_univ_succ, Fin.sum_univ_zero]
  cases variant <;> fin_cases v <;>
    norm_num [coloring, graph, edges, Paper.opinion]
  all_goals norm_num [Fin.ext_iff]

theorem state_refinement (variant : Bool) (v : Fin 8) :
    refinement (state variant) v =
      append (label (coloring v)) (if variant = true ∧ v = 0 then true else coloring v) := by
  change refinement (actualState (graph variant) coloring 0) v = _
  rw [refinement_actualState, actualHistory_succ]
  have hp : actualHistory (graph variant) coloring 1 v = label (coloring v) :=
    congrFun (state_part variant) v
  rw [hp]
  congr 1
  simpa [Probability.RandomOpinionsReduction.coloringOnDayV,
    Function.iterate_succ_apply'] using next_color variant v

/-- The actual next false-false block, stated without any next degree information. -/
theorem refinement_size (variant : Bool) :
    Local.partSizes (refinement (state variant)) (append (label false) false) =
      if variant then 3 else 4 := by
  classical
  rw [← block_card_partSizes]
  have hblock : block (refinement (state variant)) (append (label false) false) =
      Finset.univ.filter (fun v : Fin 8 => coloring v = false ∧
        (if variant = true ∧ v = 0 then true else coloring v) = false) := by
    ext v
    simp only [mem_block, state_refinement, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      have hp := congrArg parent h
      have hl := congrArg last h
      exact ⟨label_injective (by simpa using hp), by simpa using hl⟩
    · rintro ⟨hp, hl⟩
      rw [hl, hp]
  rw [hblock]
  rw [Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero]
  cases variant <;> norm_num [coloring]
  all_goals norm_num [Fin.ext_iff]

end MajorityDynamics.GraphProcess.NonLumpability
