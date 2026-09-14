import MajorityDynamics.Universal.ResponseBasic

/-!
# Linear-response solvability, covariance identities, and sibling cancellation

All statements concern the constructed arrays of Section 4. The only analytic
input is the already proved conditional covariance and the law of total
expectation for the two actual branches.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open MajorityDynamics.Analysis

namespace MajorityDynamics.Universal

theorem betaFor_spec (n : ℕ) (s : History (n + 1)) (e : History (n + 1) → ℝ) :
    Matrix.vecMul (betaFor n s e) (conditionalCovariance n s) = e := by
  rw [betaFor, Matrix.vecMul_vecMul,
    Matrix.nonsing_inv_mul _
      ((conditionalCovariance n s).isUnit_iff_isUnit_det.mp
        (universal_conditional_covariance_posDef n s).isUnit), Matrix.vecMul_one]

theorem betaFor_unique (n : ℕ) (s : History (n + 1)) (e b : History (n + 1) → ℝ)
    (hb : Matrix.vecMul b (conditionalCovariance n s) = e) : b = betaFor n s e := by
  apply Matrix.vecMul_injective_of_isUnit (universal_conditional_covariance_posDef n s).isUnit
  exact hb.trans (betaFor_spec n s e).symm

theorem β_spec (n : ℕ) (s t : History (n + 1)) :
    ∑ u, β n s u * conditionalCovariance n s u t = ε n t :=
  congrFun (betaFor_spec n s (ε n)) t

theorem β_unique (n : ℕ) (s : History (n + 1)) (b : History (n + 1) → ℝ)
    (hb : ∀ t, ∑ u, b u * conditionalCovariance n s u t = ε n t) : b = β n s :=
  betaFor_unique n s (ε n) b (funext hb)

/-- Existence and uniqueness in the paper's displayed coordinate orientation. -/
theorem β_existsUnique (n : ℕ) (s : History (n + 1)) :
    ∃! b : History (n + 1) → ℝ,
      ∀ t, ∑ u, b u * conditionalCovariance n s u t = ε n t :=
  ⟨β n s, β_spec n s, fun b hb => β_unique n s b hb⟩

@[simp] theorem responseLinear_add {k : ℕ} (b : History k → ℝ) (x y : Row k) :
    responseLinear b (x + y) = responseLinear b x + responseLinear b y := by
  simp [responseLinear, mul_add, Finset.sum_add_distrib]

@[simp] theorem responseLinear_smul {k : ℕ} (b : History k → ℝ) (c : ℝ) (x : Row k) :
    responseLinear b (c • x) = c * responseLinear b x := by
  simp only [responseLinear, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem responseLinear_memLp {k : ℕ} (ρ : Measure (Row k)) (hlp : MemLp id 2 ρ)
    (b : History k → ℝ) : MemLp (responseLinear b) 2 ρ :=
  memLp_finsetSum _ (fun t _ => (hlp.eval_piLp t).const_mul (b t))

theorem integral_responseLinear {k : ℕ} (ρ : Measure (Row k)) [IsFiniteMeasure ρ]
    (hlp : MemLp id 2 ρ) (b : History k → ℝ) :
    (∫ x, responseLinear b x ∂ρ) = ∑ t, b t * ∫ x, x t ∂ρ := by
  unfold responseLinear
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
  · intro t _
    exact ((hlp.eval_piLp t).integrable (by norm_num)).const_mul (b t)

theorem integral_responseLinear_eq_mean {k : ℕ} (ρ : Measure (Row k)) [IsFiniteMeasure ρ]
    (hlp : MemLp id 2 ρ) (b : History k → ℝ) :
    (∫ x, responseLinear b x ∂ρ) = responseLinear b (ConditionalGaussian.mean ρ) := by
  rw [integral_responseLinear ρ hlp b, responseLinear]
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  exact (eval_integral_piLp (f := fun x : Row k => x)
    (fun j => (hlp.eval_piLp j).integrable (by norm_num)) t).symm

theorem responseLinear_covariance_coordinate {k : ℕ} (ρ : Measure (Row k))
    [IsFiniteMeasure ρ] (hlp : MemLp id 2 ρ) (b : History k → ℝ) (t : History k) :
    ProbabilityTheory.covariance (responseLinear b) (fun x => x t) ρ =
      ∑ u, b u * ConditionalGaussian.covMatrix ρ u t := by
  change ProbabilityTheory.covariance (fun x => ∑ u, b u * x u) (fun x => x t) ρ = _
  simpa only [id_eq, covariance_const_mul_left,
    ConditionalGaussian.covMatrix] using
    covariance_fun_sum_left (fun u => (hlp.eval_piLp u).const_mul (b u)) (hlp.eval_piLp t)

/-- The centered covariance characterization displayed in Definition `def:universal-epsilon`. -/
theorem B_covariance_coordinate (n : ℕ) (s t : History (n + 1)) :
    ProbabilityTheory.covariance (B n s) (fun x => x t) (historyLaw n s) = ε n t := by
  have hreg := historyLaw_regular n s
  let := hreg.probability
  change ProbabilityTheory.covariance (responseLinear (β n s)) _ _ = _
  rw [responseLinear_covariance_coordinate _ hreg.memLp_two]
  exact β_spec n s t

theorem B_memLp_history (n : ℕ) (s : History (n + 1)) :
    MemLp (B n s) 2 (historyLaw n s) :=
  responseLinear_memLp _ (historyLaw_regular n s).memLp_two (β n s)

theorem B_memLp_child (n : ℕ) (s : History (n + 1)) (b : Bool) :
    MemLp (B n s) 2 (childLaw n s b) :=
  responseLinear_memLp _ (childLaw_regular n s b).memLp_two (β n s)

theorem B_covariance_responseLinear (n : ℕ) (s : History (n + 1))
    (a : History (n + 1) → ℝ) :
    ProbabilityTheory.covariance (B n s) (responseLinear a) (historyLaw n s) =
      ∑ t, a t * ε n t := by
  have hreg := historyLaw_regular n s
  let := hreg.probability
  change ProbabilityTheory.covariance (B n s) (fun x => ∑ t, a t * x t) _ = _
  have h := covariance_fun_sum_right
    (fun t => (hreg.memLp_two.eval_piLp t).const_mul (a t)) (B_memLp_history n s)
  simpa only [id_eq, covariance_const_mul_right, B_covariance_coordinate] using h

theorem responseLinear_branch_total (n : ℕ) (s : History (n + 1))
    (a : History (n + 1) → ℝ) :
    branchProbability s (ν n) (γ n s) false *
        (∫ x, responseLinear a x ∂childLaw n s false) +
      branchProbability s (ν n) (γ n s) true *
        (∫ x, responseLinear a x ∂childLaw n s true) =
      ∫ x, responseLinear a x ∂historyLaw n s := by
  have hreg := historyLaw_regular n s
  have hf := childLaw_regular n s false
  have ht := childLaw_regular n s true
  let := hreg.probability
  let := hf.probability
  let := ht.probability
  rw [integral_responseLinear_eq_mean _ hf.memLp_two,
    integral_responseLinear_eq_mean _ ht.memLp_two,
    integral_responseLinear_eq_mean _ hreg.memLp_two]
  have h := congrArg (responseLinear a) (branchMean_total s (ν n) (ν_positive n) (γ n s))
  simp only [responseLinear_add, responseLinear_smul] at h
  simp only [childLaw, historyLaw, dayLaw]
  rw [child_condition_eq s false (ν n) (ν_positive n),
    child_condition_eq s true (ν n) (ν_positive n),
    history_condition_eq s (ν n) (ν_positive n)]
  exact h

/-- Cancellation holds for every input response, before any coherence argument. -/
theorem responseStep_siblings (n : ℕ) (e : History (n + 1) → ℝ)
    (s : History (n + 1)) :
    responseStep n e (append s false) + responseStep n e (append s true) = 0 := by
  simp only [responseStep, parent_append, last_append, ν_recursion]
  have htotal := responseLinear_branch_total n s (betaFor n s e)
  have hprob := branchProbability_add s (ν n) (ν_positive n) (γ n s)
  calc
    _ = ν n s *
        ((branchProbability s (ν n) (γ n s) false *
            (∫ x, responseLinear (betaFor n s e) x ∂childLaw n s false) +
          branchProbability s (ν n) (γ n s) true *
            (∫ x, responseLinear (betaFor n s e) x ∂childLaw n s true)) -
          (branchProbability s (ν n) (γ n s) false +
            branchProbability s (ν n) (γ n s) true) *
            (∫ x, responseLinear (betaFor n s e) x ∂historyLaw n s)) := by ring
    _ = 0 := by rw [htotal, hprob]; ring

theorem ε_siblings (n : ℕ) (s : History (n + 1)) :
    ε (n + 1) (append s false) + ε (n + 1) (append s true) = 0 :=
  responseStep_siblings n (ε n) s

theorem ε_sibling_neg (n : ℕ) (s : History (n + 1)) :
    ε (n + 1) (append s true) = -ε (n + 1) (append s false) := by
  linarith [ε_siblings n s]

/-- The sibling identity also includes the initial response on one-bit histories. -/
theorem ε_siblings_at_level (n : ℕ) (s : History n) :
    ε n (append s false) + ε n (append s true) = 0 := by
  cases n with
  | zero => simp
  | succ n => exact ε_siblings n s

theorem ε_sum_zero (n : ℕ) : ∑ t, ε n t = 0 := by
  rw [sum_children]
  simp only [ε_siblings_at_level, Finset.sum_const_zero]

/-- Every response signed by a coordinate earlier than the final one cancels. -/
theorem ε_earlier_signed_sum (n : ℕ) (r : Fin n) :
    ∑ t, character r.castSucc t * ε n t = 0 := by
  rw [sum_children]
  simp only [character_append_castSucc, ← mul_add, ε_siblings_at_level,
    mul_zero, Finset.sum_const_zero]

/-- The last-coordinate signed sum is twice the sum of the zero children. -/
theorem ε_lead_sum (n : ℕ) :
    ∑ t, character (Fin.last n) t * ε n t =
      2 * ∑ s : History n, ε n (append s false) := by
  rw [sum_children, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp only [character, bits_append_last, sign_false, sign_true, one_mul, neg_one_mul]
  linarith [ε_siblings_at_level n s]

theorem ε_initial_lead : ∑ t, character (Fin.last 0) t * ε 0 t = 2 := by
  simp [character, ε_zero, last, sign_sq]

theorem ε_lead_pos_of_children (n : ℕ)
    (h : ∀ s : History n, 0 < ε n (append s false)) :
    0 < ∑ t, character (Fin.last n) t * ε n t := by
  rw [ε_lead_sum]
  apply mul_pos (by norm_num)
  exact Finset.sum_pos (fun s _ => h s) Finset.univ_nonempty

end MajorityDynamics.Universal
