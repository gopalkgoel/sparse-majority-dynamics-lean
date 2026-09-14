import MajorityDynamics.Idealized.RowLimits.Events
import MajorityDynamics.Idealized.RowLimits.GeometryLocal

/-! Exact deletion of the diagonal trial and its normalized threshold error. -/
noncomputable section
open scoped BigOperators
open MajorityDynamics.Universal
namespace MajorityDynamics.Idealized.RowLimits
variable {n r : ℕ}

theorem matrix_trials_eq (sizes : Local.Sizes n) (s : History (n + 1))
    (hs : ∀ t, 0 < sizes t) (M : Matrix (Fin r) (History (n + 1)) ℝ) (j : Fin r) :
    (∑ t, M j t * (Local.trials sizes s t : ℝ)) =
      (∑ t, M j t * (sizes t : ℝ)) - M j s := by
  classical
  simp_rw [trials_cast sizes s _ (hs _), mul_sub]
  rw [Finset.sum_sub_distrib]
  simp

theorem abs_historyMatrix (s : History (n + 1)) (j : Fin n) (t : History (n + 1)) :
    |historyMatrix s j t| = 1 := by
  have h (b : Bool) : |sign b| = 1 := by cases b <;> norm_num
  simp [historyMatrix, character, abs_mul, h]

theorem abs_childMatrix (s : History (n + 1)) (b : Bool)
    (j : Fin (n + 1)) (t : History (n + 1)) : |childMatrix s b j t| = 1 := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · have h (b : Bool) : |sign b| = 1 := by cases b <;> norm_num
    simp [character, abs_mul, h]
  · simpa using abs_historyMatrix s i t

def normalizedThreshold (N : ℕ) (p : Binomial.Probability) (sizes : Local.Sizes n)
    (s : History (n + 1)) (M : Matrix (Fin r) (History (n + 1)) ℝ) :
    Analysis.ConditionalGaussian.Space r :=
  WithLp.toLp 2 (fun j => (p : ℝ) * (∑ t, M j t * (Local.trials sizes s t : ℝ)) /
    Real.sqrt ((p : ℝ) * N))

theorem normalizedThreshold_deletion (N : ℕ) (p : Binomial.Probability)
    (sizes : Local.Sizes n) (s : History (n + 1)) (hs : ∀ t, 0 < sizes t)
    (M : Matrix (Fin r) (History (n + 1)) ℝ) (j : Fin r) (hM : |M j s| ≤ 1) :
    |normalizedThreshold N p sizes s M j -
      (p : ℝ) * (∑ t, M j t * (sizes t : ℝ)) / Real.sqrt ((p : ℝ) * N)| ≤
        (p : ℝ) / Real.sqrt ((p : ℝ) * N) := by
  change |(p : ℝ) * (∑ t, M j t * (Local.trials sizes s t : ℝ)) / _ - _| ≤ _
  rw [matrix_trials_eq sizes s hs M j]
  have he : (p : ℝ) * ((∑ t, M j t * (sizes t : ℝ)) - M j s) /
      Real.sqrt ((p : ℝ) * N) - (p : ℝ) * (∑ t, M j t * (sizes t : ℝ)) /
      Real.sqrt ((p : ℝ) * N) = -((p : ℝ) / Real.sqrt ((p : ℝ) * N)) * M j s := by ring
  rw [he, abs_mul, abs_neg, abs_of_nonneg (div_nonneg p.property.1.le (Real.sqrt_nonneg _))]
  exact (mul_le_mul_of_nonneg_left hM (div_nonneg p.property.1.le (Real.sqrt_nonneg _))).trans_eq
    (mul_one _)

theorem normalized_balance {N : ℕ} (hN : 0 < N) (p : Binomial.Probability)
    {z ξ : ℝ} (hz : |z| ≤ ξ * (N : ℝ) / Real.sqrt ((p : ℝ) * N)) :
    |(p : ℝ) * z / Real.sqrt ((p : ℝ) * N)| ≤ ξ := by
  have h : 0 < (p : ℝ) * N := mul_pos p.property.1 (Nat.cast_pos.mpr hN)
  have hr : Real.sqrt ((p : ℝ) * N) ≠ 0 := (Real.sqrt_pos.mpr h).ne'
  rw [abs_div, abs_mul, abs_of_pos p.property.1, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ (p : ℝ) * (ξ * (N : ℝ) / Real.sqrt ((p : ℝ) * N)) /
        Real.sqrt ((p : ℝ) * N) := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hz p.property.1.le) (Real.sqrt_nonneg _)
    _ = ξ := by
      field_simp
      rw [Real.sq_sqrt h.le]
      ring

theorem normalizedThreshold_history_bound {N ell : ℕ} (hN : 0 < N)
    {p : Binomial.Probability} {T ξ : ℝ} {s : History (n + 1)} {sizes : Local.Sizes n}
    (ha : AdmissibleSizes N p ell T ξ s sizes) (hs : ∀ t, 0 < sizes t) (j : Fin n) :
    |normalizedThreshold N p sizes s (historyMatrix s) j| ≤
      ξ + (p : ℝ) / Real.sqrt ((p : ℝ) * N) := by
  have hd := normalizedThreshold_deletion N p sizes s hs (historyMatrix s) j
    (abs_historyMatrix s j s).le
  have hb := normalized_balance hN p (ha.history_balance j)
  have he := abs_add_le (normalizedThreshold N p sizes s (historyMatrix s) j -
    (p : ℝ) * (∑ t, historyMatrix s j t * (sizes t : ℝ)) / Real.sqrt ((p : ℝ) * N))
    ((p : ℝ) * (∑ t, historyMatrix s j t * (sizes t : ℝ)) / Real.sqrt ((p : ℝ) * N))
  rw [sub_add_cancel] at he
  exact he.trans ((add_le_add hd hb).trans_eq (add_comm _ _))

theorem normalizedThreshold_child_last {N : ℕ} (p : Binomial.Probability)
    (sizes : Local.Sizes n) (s : History (n + 1)) (hs : ∀ t, 0 < sizes t) (b : Bool) :
    |normalizedThreshold N p sizes s (childMatrix s b) (Fin.last n) -
      childThreshold (n := n) b (shift N p sizes) (Fin.last n)| ≤
        (p : ℝ) / Real.sqrt ((p : ℝ) * N) := by
  have hd := normalizedThreshold_deletion N p sizes s hs (childMatrix s b) (Fin.last n)
    (abs_childMatrix s b (Fin.last n) s).le
  have he : (p : ℝ) * (∑ t, childMatrix s b (Fin.last n) t * (sizes t : ℝ)) /
      Real.sqrt ((p : ℝ) * N) = sign b * shift N p sizes := by
    simp only [childMatrix_last, shift, nextImbalance, imbalance, sizeVector,
      mul_assoc, ← Finset.mul_sum]
    ring
  rw [he] at hd
  simpa only [childThreshold_last] using hd

theorem normalizedThreshold_child_castSucc (N : ℕ) (p : Binomial.Probability)
    (sizes : Local.Sizes n) (s : History (n + 1)) (b : Bool) (j : Fin n) :
    normalizedThreshold N p sizes s (childMatrix s b) j.castSucc =
      normalizedThreshold N p sizes s (historyMatrix s) j := by
  simp [normalizedThreshold]

theorem normalizedThreshold_child_error {N ell : ℕ} (hN : 0 < N)
    {p : Binomial.Probability} {T ξ : ℝ} {s : History (n + 1)} {sizes : Local.Sizes n}
    (ha : AdmissibleSizes N p ell T ξ s sizes) (hs : ∀ t, 0 < sizes t) (hξ : 0 ≤ ξ)
    (b : Bool) (j : Fin (n + 1)) :
    |normalizedThreshold N p sizes s (childMatrix s b) j -
      childThreshold b (shift N p sizes) j| ≤
        ξ + (p : ℝ) / Real.sqrt ((p : ℝ) * N) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · exact (normalizedThreshold_child_last p sizes s hs b).trans (le_add_of_nonneg_left hξ)
  · simpa only [normalizedThreshold_child_castSucc, childThreshold_castSucc, sub_zero] using
      normalizedThreshold_history_bound hN ha hs i

theorem shift_abs_le {N ell : ℕ} (hN : 0 < N)
    {p : Binomial.Probability} {T ξ : ℝ} {s : History (n + 1)} {sizes : Local.Sizes n}
    (ha : AdmissibleSizes N p ell T ξ s sizes) : |shift N p sizes| ≤ T :=
  normalized_balance hN p ha.decision_balance

theorem shift_abs_le_of_small_balance {N : ℕ} (hN : 0 < N)
    {p : Binomial.Probability} {ξ : ℝ} {sizes : Local.Sizes n}
    (hb : |nextImbalance sizes| ≤ ξ * (N : ℝ) / Real.sqrt ((p : ℝ) * N)) :
    |shift N p sizes| ≤ ξ := normalized_balance hN p hb

theorem matrix_trials_bound (sizes : Local.Sizes n) (s : History (n + 1))
    (hs : ∀ t, 0 < sizes t) (M : Matrix (Fin r) (History (n + 1)) ℝ)
    (j : Fin r) (hM : |M j s| ≤ 1) {B : ℝ}
    (hb : |∑ t, M j t * (sizes t : ℝ)| ≤ B) :
    |∑ t, M j t * (Local.trials sizes s t : ℝ)| ≤ B + 1 := by
  rw [matrix_trials_eq sizes s hs M j]
  exact (abs_sub _ _).trans (add_le_add hb hM)

theorem childMatrix_size_bound {N ell : ℕ}
    {p : Binomial.Probability} {T ξ : ℝ} {s : History (n + 1)} {sizes : Local.Sizes n}
    (ha : AdmissibleSizes N p ell T ξ s sizes) (hξ : ξ ≤ T) (b : Bool)
    (j : Fin (n + 1)) :
    |∑ t, childMatrix s b j t * (sizes t : ℝ)| ≤ T * (N : ℝ) / Real.sqrt ((p : ℝ) * N) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · have he : (∑ t, childMatrix s b (Fin.last n) t * (sizes t : ℝ)) =
        sign b * nextImbalance sizes := by
      simp only [childMatrix_last, nextImbalance, imbalance, sizeVector, mul_assoc,
        ← Finset.mul_sum]
    rw [he, abs_mul]
    have hb : |sign b| = 1 := by cases b <;> norm_num
    simpa only [hb, one_mul] using ha.decision_balance
  · simp only [childMatrix_castSucc]
    exact (ha.history_balance i).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hξ (Nat.cast_nonneg _)) (Real.sqrt_nonneg _))

theorem matrix_trial_balance {N : ℕ} (hN : 0 < N) (p : Binomial.Probability)
    {T K : ℝ} (hT : 1 < T) (hK : 2 * T < K)
    (hscale : Real.sqrt ((p : ℝ) * N) ≤ N)
    (sizes : Local.Sizes n) (s : History (n + 1)) (hs : ∀ t, 0 < sizes t)
    (M : Matrix (Fin r) (History (n + 1)) ℝ) (j : Fin r) (hM : |M j s| ≤ 1)
    (hb : |∑ t, M j t * (sizes t : ℝ)| ≤ T * (N : ℝ) / Real.sqrt ((p : ℝ) * N)) :
    |∑ t, M j t * (Local.trials sizes s t : ℝ)| < K * (N : ℝ) / Real.sqrt ((p : ℝ) * N) := by
  have hr : 0 < Real.sqrt ((p : ℝ) * N) := Real.sqrt_pos.mpr
    (mul_pos p.property.1 (Nat.cast_pos.mpr hN))
  have hq : 1 ≤ (N : ℝ) / Real.sqrt ((p : ℝ) * N) := (le_div_iff₀ hr).mpr (by simpa using hscale)
  have hd := matrix_trials_bound sizes s hs M j hM hb
  have htk : T + 1 < K := by linarith
  have hprod := mul_lt_mul_of_pos_right htk (lt_of_lt_of_le zero_lt_one hq)
  rw [mul_div_assoc] at hd ⊢
  nlinarith

theorem matrix_trial_history_balance {N ell : ℕ} (hN : 0 < N)
    {p : Binomial.Probability} {T ξ K : ℝ} {s : History (n + 1)} {sizes : Local.Sizes n}
    (ha : AdmissibleSizes N p ell T ξ s sizes) (hs : ∀ t, 0 < sizes t)
    (hT : 1 < T) (hK : 2 * T < K) (hξ : ξ ≤ T)
    (hscale : Real.sqrt ((p : ℝ) * N) ≤ N) (j : Fin n) :
    |∑ t, historyMatrix s j t * (Local.trials sizes s t : ℝ)| <
      K * (N : ℝ) / Real.sqrt ((p : ℝ) * N) := by
  apply matrix_trial_balance hN p hT hK hscale sizes s hs _ j (abs_historyMatrix s j s).le
  exact (ha.history_balance j).trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hξ (Nat.cast_nonneg _)) (Real.sqrt_nonneg _))

theorem matrix_trial_child_balance {N ell : ℕ} (hN : 0 < N)
    {p : Binomial.Probability} {T ξ K : ℝ} {s : History (n + 1)} {sizes : Local.Sizes n}
    (ha : AdmissibleSizes N p ell T ξ s sizes) (hs : ∀ t, 0 < sizes t)
    (hT : 1 < T) (hK : 2 * T < K) (hξ : ξ ≤ T)
    (hscale : Real.sqrt ((p : ℝ) * N) ≤ N) (b : Bool) (j : Fin (n + 1)) :
    |∑ t, childMatrix s b j t * (Local.trials sizes s t : ℝ)| <
      K * (N : ℝ) / Real.sqrt ((p : ℝ) * N) :=
  matrix_trial_balance hN p hT hK hscale sizes s hs _ j (abs_childMatrix s b j s).le
    (childMatrix_size_bound ha hξ b j)

theorem normalizedThreshold_bound {N : ℕ} (hN : 0 < N) (p : Binomial.Probability)
    (sizes : Local.Sizes n) (s : History (n + 1)) (hs : ∀ t, 0 < sizes t)
    (M : Matrix (Fin r) (History (n + 1)) ℝ) (j : Fin r) (hM : |M j s| ≤ 1)
    {T : ℝ} (hb : |∑ t, M j t * (sizes t : ℝ)| ≤ T * (N : ℝ) / Real.sqrt ((p : ℝ) * N)) :
    |normalizedThreshold N p sizes s M j| ≤ T + (p : ℝ) / Real.sqrt ((p : ℝ) * N) := by
  have hd := normalizedThreshold_deletion N p sizes s hs M j hM
  have ht := normalized_balance hN p hb
  have he := abs_add_le (normalizedThreshold N p sizes s M j -
    (p : ℝ) * (∑ t, M j t * (sizes t : ℝ)) / Real.sqrt ((p : ℝ) * N))
    ((p : ℝ) * (∑ t, M j t * (sizes t : ℝ)) / Real.sqrt ((p : ℝ) * N))
  rw [sub_add_cancel] at he
  exact he.trans ((add_le_add hd ht).trans_eq (add_comm _ _))

theorem normalizedThreshold_child_bound {N ell : ℕ} (hN : 0 < N)
    {p : Binomial.Probability} {T ξ : ℝ} {s : History (n + 1)} {sizes : Local.Sizes n}
    (ha : AdmissibleSizes N p ell T ξ s sizes) (hs : ∀ t, 0 < sizes t)
    (hξ : ξ ≤ T) (b : Bool) (j : Fin (n + 1)) :
    |normalizedThreshold N p sizes s (childMatrix s b) j| ≤
      T + (p : ℝ) / Real.sqrt ((p : ℝ) * N) :=
  normalizedThreshold_bound hN p sizes s hs _ j (abs_childMatrix s b j s).le
    (childMatrix_size_bound ha hξ b j)

end MajorityDynamics.Idealized.RowLimits
