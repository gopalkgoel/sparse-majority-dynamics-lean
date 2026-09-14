import MajorityDynamics.Idealized.RowLimits.Basic
import MajorityDynamics.Universal.Events
import MajorityDynamics.Binomial.ApproximationStatements
import MajorityDynamics.Analysis.GaussianRegularity.Basic

/-! Literal history inequalities and their orthogonal integer normals for E.3. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators Matrix
open MajorityDynamics.Universal

namespace MajorityDynamics.Idealized.RowLimits

variable {n k : ℕ}

def integerSign (b : Bool) : ℤ := if b then -1 else 1

@[simp] theorem integerSign_cast (b : Bool) : (integerSign b : ℝ) = sign b := by
  cases b <;> simp [integerSign, sign]

def historyIntegerMatrix (s : History (n + 1)) : Fin n → History (n + 1) → ℤ :=
  fun r t => integerSign (bits (n + 1) s r.succ) *
    integerSign (bits (n + 1) t r.castSucc)

def childIntegerMatrix (s : History (n + 1)) (b : Bool) :
    Fin (n + 1) → History (n + 1) → ℤ :=
  Fin.snoc (historyIntegerMatrix s)
    (fun t => integerSign b * integerSign (bits (n + 1) t (Fin.last n)))

def historyStrict (s : History (n + 1)) : Fin n → Bool :=
  fun r => decide (bits (n + 1) s r.succ ≠ bits (n + 1) s r.castSucc)

def childStrict (s : History (n + 1)) (b : Bool) : Fin (n + 1) → Bool :=
  Fin.snoc (historyStrict s) (decide (b ≠ last s))

@[simp] theorem historyIntegerMatrix_cast (s : History (n + 1)) (r : Fin n)
    (t : History (n + 1)) : (historyIntegerMatrix s r t : ℝ) = historyMatrix s r t := by
  simp [historyIntegerMatrix, historyMatrix, character]

def childMatrix (s : History (n + 1)) (b : Bool) :
    Matrix (Fin (n + 1)) (History (n + 1)) ℝ :=
  fun r t => (childIntegerMatrix s b r t : ℝ)

@[simp] theorem childMatrix_castSucc (s : History (n + 1)) (b : Bool)
    (r : Fin n) (t : History (n + 1)) : childMatrix s b r.castSucc t = historyMatrix s r t := by
  simp [childMatrix, childIntegerMatrix]

@[simp] theorem childMatrix_last (s : History (n + 1)) (b : Bool)
    (t : History (n + 1)) : childMatrix s b (Fin.last n) t = sign b * character (Fin.last n) t := by
  simp [childMatrix, childIntegerMatrix, character]

theorem decision_iff_mixed (a b : Bool) (z : ℝ) : decision a b z ↔
    if decide (b ≠ a) then 0 < sign b * z else 0 ≤ sign b * z := by
  cases a <;> cases b <;> simp [decision] <;> constructor <;> intro h <;> first | rcases h with h | h <;> linarith | rcases lt_or_eq_of_le h with h | h <;> simp_all

theorem history_inequalityEvent (s : History (n + 1)) (a : History (n + 1) → ℕ) :
    a ∈ Binomial.inequalityEvent (fun r t => (historyIntegerMatrix s r t : ℝ))
      (historyStrict s) ↔ WithLp.toLp 2 (fun t => (a t : ℝ)) ∈ historyEvent s := by
  simp only [Binomial.inequalityEvent, mem_ofPred_eq, historyEvent]
  apply forall_congr'
  intro r
  rw [decision_iff_mixed]
  simp [historyStrict, historyMatrix, imbalance, Finset.mul_sum, mul_assoc]

theorem child_inequalityEvent (s : History (n + 1)) (b : Bool)
    (a : History (n + 1) → ℕ) :
    a ∈ Binomial.inequalityEvent (childMatrix s b) (childStrict s b) ↔
      WithLp.toLp 2 (fun t => (a t : ℝ)) ∈ childEvent s b := by
  rw [childEvent, mem_inter_iff, ← history_inequalityEvent]
  simp only [Binomial.inequalityEvent, mem_ofPred_eq]
  rw [Fin.forall_iff_castSucc, decision_iff_mixed]
  simp [childStrict, historyStrict, historyMatrix, imbalance, Finset.mul_sum, mul_assoc, and_comm]

theorem signed_character_orthogonal {r k : ℕ} (f : Fin r → Fin k)
    (hf : Function.Injective f) (b : Fin r → Bool) :
    Binomial.Approximation.OrthogonalRows (fun j (t : History k) => integerSign (b j) *
      integerSign (bits k t (f j))) := by
  constructor
  · intro j
    refine ⟨⟨0, Fintype.card_pos⟩, ?_⟩
    have hz (c : Bool) : integerSign c ≠ 0 := by cases c <;> norm_num [integerSign]
    exact mul_ne_zero (hz _) (hz _)
  · intro j l hjl
    have h : (∑ t : History k,
        (sign (b j) * character (f j) t) * (sign (b l) * character (f l) t)) = 0 := by
      calc
        _ = (sign (b j) * sign (b l)) *
            ∑ t : History k, character (f j) t * character (f l) t := by
          rw [Finset.mul_sum]
          congr 1
          ext t
          ring
        _ = 0 := by rw [character_orthogonal, if_neg (fun h => hjl (hf h)), mul_zero]
    exact_mod_cast (by simpa [character] using h :
      (∑ t : History k, ((integerSign (b j) * integerSign (bits k t (f j)) : ℤ) : ℝ) *
        ((integerSign (b l) * integerSign (bits k t (f l)) : ℤ) : ℝ)) = 0)

theorem historyIntegerMatrix_orthogonal (s : History (n + 1)) :
    Binomial.Approximation.OrthogonalRows (historyIntegerMatrix s) :=
  signed_character_orthogonal Fin.castSucc (Fin.castSucc_injective _)
    (fun r => bits (n + 1) s r.succ)

theorem childIntegerMatrix_eq (s : History (n + 1)) (b : Bool) :
    childIntegerMatrix s b = fun r t =>
      integerSign ((Fin.snoc (fun i : Fin n => bits (n + 1) s i.succ) b : Fin (n+1) → Bool) r) *
        integerSign (bits (n + 1) t r) := by
  funext r t
  refine Fin.lastCases ?_ (fun i => ?_) r <;>
    simp [childIntegerMatrix, historyIntegerMatrix]

theorem childIntegerMatrix_orthogonal (s : History (n + 1)) (b : Bool) :
    Binomial.Approximation.OrthogonalRows (childIntegerMatrix s b) := by
  rw [childIntegerMatrix_eq]
  exact signed_character_orthogonal id Function.injective_id _


theorem signed_character_rank {r k : ℕ} (f : Fin r → Fin k)
    (hf : Function.Injective f) (b : Fin r → Bool) :
    Matrix.rank (fun j (t : History k) => sign (b j) * character (f j) t) = r := by
  have hind : LinearIndependent ℝ
      (fun j (t : History k) => sign (b j) * character (f j) t) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hz := congrArg (fun v : History k → ℝ =>
      ∑ t, character (f j) t * v t) hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      mul_zero, Finset.sum_const_zero] at hz
    simp_rw [Finset.mul_sum] at hz
    rw [Finset.sum_comm] at hz
    have he (l : Fin r) :
        (∑ t : History k, character (f j) t * (c l * (sign (b l) * character (f l) t))) =
          c l * sign (b l) * ∑ t : History k, character (f j) t * character (f l) t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring
    simp_rw [he, character_orthogonal, hf.eq_iff] at hz
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hz
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (history_card_pos k).ne')).resolve_right
      (sign_ne_zero _)
  simpa using hind.rank_matrix

theorem historyMatrix_rank (s : History (n + 1)) : (historyMatrix s).rank = n :=
  signed_character_rank Fin.castSucc (Fin.castSucc_injective _) _

theorem childMatrix_rank (s : History (n + 1)) (b : Bool) : (childMatrix s b).rank = n + 1 := by
  have he : childMatrix s b = fun r t =>
      sign ((Fin.snoc (fun i : Fin n => bits (n + 1) s i.succ) b : Fin (n+1) → Bool) r) *
        character r t := by
    funext r t
    refine Fin.lastCases ?_ (fun i => ?_) r <;> simp [historyMatrix]
  rw [he]
  exact signed_character_rank id Function.injective_id _


/-- Threshold vector in the paper's convention `Mx ≥ -u`. -/
def childThreshold (b : Bool) (u : ℝ) : Analysis.ConditionalGaussian.Space (n + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun _ : Fin n => (0 : ℝ)) (sign b * u))

@[simp] theorem childThreshold_castSucc (b : Bool) (u : ℝ) (r : Fin n) :
    childThreshold (n := n) b u r.castSucc = 0 := by simp [childThreshold]

@[simp] theorem childThreshold_last (b : Bool) (u : ℝ) :
    childThreshold (n := n) b u (Fin.last n) = sign b * u := by simp [childThreshold]

theorem imbalance_ne_level_ae (ν : History (n + 1) → ℝ) (hν : ∀ t, 0 < ν t)
    (γ : Row (n + 1)) (r : Fin (n + 1)) (c : ℝ) :
    ∀ᵐ x ∂rowLaw ν γ, imbalance r x ≠ c := by
  have hnull : rowLaw ν γ {x | imbalance r x = c} = 0 := by
    apply Analysis.ConditionalGaussian.gaussianLaw_absolutelyContinuous _ (covariance_posDef ν hν) γ
    simp_rw [imbalance_eq_inner]
    exact Analysis.ConditionalGaussian.volume_inner_level_eq_zero _ (characterVector_ne_zero r) c
  simpa only [ae_iff, not_not] using hnull

theorem decision_iff_weak (a b : Bool) {z : ℝ} (hz : z ≠ 0) :
    decision a b z ↔ 0 ≤ sign b * z := by
  rw [decision_iff_strict _ _ hz]
  exact lt_iff_le_and_ne.trans (and_iff_left (mul_ne_zero (sign_ne_zero b) hz).symm)

theorem historyEvent_ae_eq_weak (s : History (n + 1))
    (ν : History (n + 1) → ℝ) (hν : ∀ t, 0 < ν t) (γ : Row (n + 1)) :
    historyEvent s =ᵐ[rowLaw ν γ]
      Analysis.GaussianRegularity.event (historyMatrix s) 0 := by
  have hall : ∀ᵐ x ∂rowLaw ν γ, ∀ r : Fin (n + 1), imbalance r x ≠ 0 :=
    ae_all_iff.mpr (imbalance_ne_zero_ae ν hν γ)
  filter_upwards [hall] with x hx
  apply propext
  change (∀ r : Fin n, decision _ _ (imbalance r.castSucc x)) ↔ _
  simp only [Analysis.GaussianRegularity.event, PiLp.zero_apply, neg_zero]
  apply forall_congr'
  intro r
  rw [decision_iff_weak _ _ (hx r.castSucc)]
  simp [historyMatrix, imbalance, Finset.mul_sum, mul_assoc]

theorem shiftedChildEvent_ae_eq_weak (s : History (n + 1)) (b : Bool) (u : ℝ)
    (ν : History (n + 1) → ℝ) (hν : ∀ t, 0 < ν t) (γ : Row (n + 1)) :
    shiftedChildEvent s b u =ᵐ[rowLaw ν γ]
      Analysis.GaussianRegularity.event (childMatrix s b) (childThreshold b u) := by
  filter_upwards [historyEvent_ae_eq_weak s ν hν γ,
    imbalance_ne_level_ae ν hν γ (Fin.last n) (-u)] with x hx hz
  apply propext
  change (x ∈ historyEvent s ∧ decision _ _ _) ↔ _
  have hne : imbalance (Fin.last n) x + u ≠ 0 := by intro h; apply hz; linarith
  change (x ∈ historyEvent s) = (x ∈ Analysis.GaussianRegularity.event (historyMatrix s) 0) at hx
  rw [hx, decision_iff_weak _ _ hne]
  simp only [Analysis.GaussianRegularity.event, mem_ofPred_eq, Fin.forall_iff_castSucc,
    childThreshold_last, childThreshold_castSucc, childMatrix_last, childMatrix_castSucc,
    neg_zero, PiLp.zero_apply]
  simp only [imbalance, mul_assoc, ← Finset.mul_sum]
  constructor
  · rintro ⟨hh, hb⟩
    exact ⟨by nlinarith, hh⟩
  · rintro ⟨hb, hh⟩
    exact ⟨hh, by nlinarith⟩

end MajorityDynamics.Idealized.RowLimits
