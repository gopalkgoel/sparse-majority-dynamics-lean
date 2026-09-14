import MajorityDynamics.Analysis.GaussianRegularity.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Convex

noncomputable section

open Set

namespace MajorityDynamics.Analysis.GaussianRegularity

/-- Positive diagonal variances form an open parameter domain. -/
theorem isOpen_positiveVariance (d r : ℕ) :
    IsOpen {p : Parameters d r | positiveVariance p} := by
  simpa only [positiveVariance, ofPred_forall] using
    (isOpen_iInter_of_finite fun i : Fin d =>
      isOpen_lt (continuous_const : Continuous (fun _ : Parameters d r => (0 : ℝ)))
        (show Continuous (fun p : Parameters d r => p.1.2 i) by fun_prop))

/-- The full parameter domain is convex; compact sets need not themselves be convex. -/
theorem convex_positiveVariance (d r : ℕ) :
    Convex ℝ {p : Parameters d r | positiveVariance p} := by
  intro p hp q hq a b ha hb hab i
  change 0 < a * p.1.2 i + b * q.1.2 i
  have hp' := hp i
  have hq' := hq i
  by_cases hapos : 0 < a
  · exact add_pos_of_pos_of_nonneg (mul_pos hapos hp') (mul_nonneg hb hq'.le)
  · have hbpos : 0 < b := by linarith
    exact add_pos_of_nonneg_of_pos (mul_nonneg ha hp'.le) (mul_pos hbpos hq')

/-- Compact positive-variance families stay uniformly away from zero variance. -/
theorem compact_variance_lower_bound {d r : ℕ} {P : Set (Parameters d r)}
    (hP : IsCompact P) (hv : ∀ p ∈ P, positiveVariance p) :
    ∃ a : ℝ, 0 < a ∧ ∀ p ∈ P, ∀ i, a ≤ p.1.2 i := by
  rcases P.eq_empty_or_nonempty with hPe | hPn
  · subst P
    exact ⟨1, zero_lt_one, by simp⟩
  rcases isEmpty_or_nonempty (Fin d) with hi | hi
  · exact ⟨1, zero_lt_one, fun _ _ i => isEmptyElim i⟩
  let Q := P ×ˢ (Set.univ : Set (Fin d))
  have hQ : IsCompact Q := hP.prod isCompact_univ
  have hQn : Q.Nonempty := hPn.prod Set.univ_nonempty
  have hc : Continuous (fun q : Parameters d r × Fin d => q.1.1.2 q.2) := by
    rw [continuous_iff_continuousAt]
    intro q
    rw [continuousAt_prod_of_discrete_right]
    change ContinuousAt (fun p : Parameters d r => p.1.2 q.2) q.1
    fun_prop
  obtain ⟨q, hq, hmin⟩ := hQ.exists_isMinOn hQn hc.continuousOn
  exact ⟨q.1.1.2 q.2, hv q.1 hq.1 q.2,
    fun p hp i => hmin (show (p, i) ∈ Q from ⟨hp, Set.mem_univ i⟩)⟩

/-- A compact family fits in a bounded parameter region with positive variances. -/
theorem compact_parameter_bounds {d r : ℕ} {P : Set (Parameters d r)}
    (hP : IsCompact P) (hv : ∀ p ∈ P, positiveVariance p) :
    ∃ a R : ℝ, 0 < a ∧ 0 < R ∧
      ∀ p ∈ P, ‖p‖ ≤ R ∧ ∀ i, a ≤ p.1.2 i := by
  obtain ⟨a, ha, hvar⟩ := compact_variance_lower_bound hP hv
  obtain ⟨R, hR⟩ := hP.isBounded.exists_norm_le
  refine ⟨a, max R 1, ha, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro p hp
  exact ⟨(hR p hp).trans (le_max_left _ _), hvar p hp⟩

/-- A bounded convex region on which all variances have a common lower bound. -/
def parameterBox {d r : ℕ} (a R : ℝ) : Set (Parameters d r) :=
  {p | ‖p‖ ≤ R ∧ ∀ i, a ≤ p.1.2 i}

theorem convex_parameterBox {d r : ℕ} (a R : ℝ) :
    Convex ℝ (parameterBox (d := d) (r := r) a R) := by
  intro p hp q hq b c hb hc hbc
  constructor
  · have hp' : p ∈ Metric.closedBall 0 R := by simpa using hp.1
    have hq' : q ∈ Metric.closedBall 0 R := by simpa using hq.1
    simpa using convex_closedBall (0 : Parameters d r) R hp' hq' hb hc hbc
  · intro i
    change a ≤ b * p.1.2 i + c * q.1.2 i
    have h1 := mul_le_mul_of_nonneg_left (hp.2 i) hb
    have h2 := mul_le_mul_of_nonneg_left (hq.2 i) hc
    calc
      a = b * a + c * a := by rw [← add_mul, hbc, one_mul]
      _ ≤ b * p.1.2 i + c * q.1.2 i := add_le_add h1 h2

theorem parameterBox_subset_positiveVariance {d r : ℕ} {a R : ℝ} (ha : 0 < a) :
    parameterBox (d := d) (r := r) a R ⊆ {p | positiveVariance p} :=
  fun _ hp i => ha.trans_le (hp.2 i)

/-- Every positive-variance point has a neighborhood inside one convex parameter box. -/
theorem exists_parameterBox_mem_nhds {d r : ℕ} {p : Parameters d r}
    (hp : positiveVariance p) :
    ∃ a R : ℝ, 0 < a ∧ 0 < R ∧ parameterBox a R ∈ nhds p := by
  obtain ⟨c, hc, hv⟩ := compact_variance_lower_bound
    (P := {p}) isCompact_singleton (by simpa using hp)
  let a := c / 2
  let R := ‖p‖ + 1
  have hopen : IsOpen {q : Parameters d r | ‖q‖ < R ∧ ∀ i, a < q.1.2 i} := by
    apply (isOpen_lt continuous_norm continuous_const).inter
    change IsOpen {q : Parameters d r | ∀ i, a < q.1.2 i}
    simpa only [ofPred_forall] using
      (isOpen_iInter_of_finite fun i : Fin d =>
        isOpen_lt (continuous_const : Continuous (fun _ : Parameters d r => a))
          (show Continuous (fun q : Parameters d r => q.1.2 i) by fun_prop))
  have hmem : p ∈ {q : Parameters d r | ‖q‖ < R ∧ ∀ i, a < q.1.2 i} := by
    refine ⟨by dsimp [R]; linarith, ?_⟩
    intro i
    have h := hv p (Set.mem_singleton p) i
    dsimp [a]
    linarith
  refine ⟨a, R, by dsimp [a]; positivity, by dsimp [R]; positivity, ?_⟩
  exact Filter.mem_of_superset (hopen.mem_nhds hmem)
    (fun q hq => ⟨hq.1.le, fun i => (hq.2 i).le⟩)

end MajorityDynamics.Analysis.GaussianRegularity
