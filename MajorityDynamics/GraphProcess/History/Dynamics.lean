import MajorityDynamics.GraphProcess.History.Counting
import MajorityDynamics.Universal.Histories
import MajorityDynamics.Probability.RandomOpinionsReduction.Transport

/-! Actual histories retain the paper's day-1 initial coloring and discrete ties. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace MajorityDynamics.GraphProcess.History
open Universal
open Probability.RandomOpinionsReduction (nextColoringV coloringOnDayV)
variable {V : Type*} [Fintype V]

def actualHistory (G : SimpleGraph V) (c : V → Bool) (k : ℕ) (v : V) : Universal.History k :=
  (bits k).symm (fun r => coloringOnDayV G c (r.val + 1) v)

@[simp] theorem bits_actualHistory (G : SimpleGraph V) (c : V → Bool) (k : ℕ)
    (v : V) (r : Fin k) :
    bits k (actualHistory G c k v) r = coloringOnDayV G c (r.val + 1) v := by
  simp [actualHistory]

theorem actualHistory_eq_iff (G : SimpleGraph V) (c : V → Bool) (k : ℕ)
    (v : V) (s : Universal.History k) :
    actualHistory G c k v = s ↔ ∀ r : Fin k,
      coloringOnDayV G c (r.val + 1) v = bits k s r := by
  rw [← (bits k).injective.eq_iff]
  simp [actualHistory, funext_iff]

theorem mem_actualBlock (G : SimpleGraph V) (c : V → Bool) (k : ℕ)
    (v : V) (s : Universal.History k) :
    v ∈ block (actualHistory G c k) s ↔ ∀ r : Fin k,
      coloringOnDayV G c (r.val + 1) v = bits k s r := by
  rw [mem_block, actualHistory_eq_iff]

@[simp] theorem actualHistory_succ (G : SimpleGraph V) (c : V → Bool) (k : ℕ) (v : V) :
    actualHistory G c (k + 1) v = append (actualHistory G c k v)
      (coloringOnDayV G c (k + 1) v) := by
  apply (bits (k + 1)).injective
  funext r
  refine Fin.lastCases ?_ (fun i => ?_) r <;> simp

@[simp] theorem parent_actualHistory (G : SimpleGraph V) (c : V → Bool) (k : ℕ) (v : V) :
    parent (actualHistory G c (k + 1) v) = actualHistory G c k v := by simp

@[simp] theorem last_actualHistory (G : SimpleGraph V) (c : V → Bool) (k : ℕ) (v : V) :
    last (actualHistory G c (k + 1) v) = coloringOnDayV G c (k + 1) v := by simp

theorem actualHistory_child_iff (G : SimpleGraph V) (c : V → Bool) (k : ℕ) (v : V)
    (s : Universal.History k) (b : Bool) :
    actualHistory G c (k + 1) v = append s b ↔
      actualHistory G c k v = s ∧ coloringOnDayV G c (k + 1) v = b := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg parent h, by simpa using congrArg last h⟩
  · rintro ⟨hs, hb⟩
    simp [hs, hb]

theorem child_blocks_union (G : SimpleGraph V) (c : V → Bool) (k : ℕ)
    (s : Universal.History k) :
    block (actualHistory G c (k + 1)) (append s false) ∪
      block (actualHistory G c (k + 1)) (append s true) = block (actualHistory G c k) s := by
  classical
  ext v
  simp only [Finset.mem_union, mem_block, actualHistory_child_iff]
  cases coloringOnDayV G c (k + 1) v <;> simp

theorem child_blocks_disjoint (G : SimpleGraph V) (c : V → Bool) (k : ℕ)
    (s : Universal.History k) :
    Disjoint (block (actualHistory G c (k + 1)) (append s false))
      (block (actualHistory G c (k + 1)) (append s true)) := by
  apply block_disjoint
  intro h
  have := congrArg last h
  simp at this

def neighborSum (G : SimpleGraph V) (c : V → Bool) (v : V) : ℤ := by
  classical
  exact ∑ w, if G.Adj v w then Paper.opinion (c w) else 0

theorem coloringOnDay_succ (G : SimpleGraph V) (c : V → Bool) (r : ℕ) :
    coloringOnDayV G c (r + 2) = nextColoringV G (coloringOnDayV G c (r + 1)) := by
  simp [coloringOnDayV, Function.iterate_succ_apply']

theorem nextColoring_decision (G : SimpleGraph V) (c : V → Bool) (v : V) (b : Bool) :
    nextColoringV G c v = b ↔ decision (c v) b (neighborSum G c v : ℝ) := by
  classical
  unfold nextColoringV
  change (if 0 < neighborSum G c v then false else
    if neighborSum G c v < 0 then true else c v) = b ↔ _
  rcases lt_trichotomy 0 (neighborSum G c v) with hp | hz | hn
  · have hpR : (0 : ℝ) < neighborSum G c v := by exact_mod_cast hp
    cases b <;> simp [hp, decision, sign, hpR, ne_of_gt hpR, not_lt.mpr hpR.le]
  · have hz' : neighborSum G c v = 0 := hz.symm
    simp [hz', decision, eq_comm]
  · have hnR : (neighborSum G c v : ℝ) < 0 := by exact_mod_cast hn
    cases b <;> simp [hn, not_lt.mpr hn.le, decision, sign, hnR, ne_of_lt hnR, not_lt.mpr hnR.le]

/-- Fiber-constant colorings let any prescribed partition reconstruct a neighbor sum. -/
theorem neighborSum_of_fiber_coloring {L : Type*} [Fintype L]
    (π : V → L) (G : SimpleGraph V) (c : V → Bool) (b : L → Bool)
    (hc : ∀ w, c w = b (π w)) (v : V) :
    neighborSum G c v = ∑ t, Paper.opinion (b t) * degreeArray π G v t := by
  classical
  unfold neighborSum degreeArray
  simp_rw [Finset.mul_sum]
  rw [← sum_block π (fun w => if G.Adj v w then Paper.opinion (c w) else 0)]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro w hw
  have ht := (mem_block π t w).mp hw
  simp [hc w, ht]

/-- Weighted block counts reconstruct the signed neighbor sum at any recorded day. -/
theorem neighborSum_history (G : SimpleGraph V) (c : V → Bool) (k : ℕ)
    (v : V) (r : Fin k) :
    neighborSum G (coloringOnDayV G c (r.val + 1)) v =
      ∑ t, Paper.opinion (bits k t r) * degreeArray (actualHistory G c k) G v t := by
  exact neighborSum_of_fiber_coloring (actualHistory G c k) G _ (fun t => bits k t r)
    (fun w => (bits_actualHistory G c k w r).symm) v

def actualRow (G : SimpleGraph V) (c : V → Bool) (k : ℕ) (v : V) : Row k :=
  WithLp.toLp 2 (fun t => (degreeArray (actualHistory G c k) G v t : ℝ))

@[simp] theorem actualRow_apply (G : SimpleGraph V) (c : V → Bool) (k : ℕ) (v : V)
    (t : Universal.History k) : actualRow G c k v t =
      (degreeArray (actualHistory G c k) G v t : ℝ) := rfl

@[simp] theorem opinion_cast (b : Bool) : (Paper.opinion b : ℝ) = sign b := by
  cases b <;> simp [Paper.opinion, sign]

theorem imbalance_actualRow (G : SimpleGraph V) (c : V → Bool) (k : ℕ)
    (v : V) (r : Fin k) :
    imbalance r (actualRow G c k v) =
      (neighborSum G (coloringOnDayV G c (r.val + 1)) v : ℝ) := by
  rw [neighborSum_history]
  simp [imbalance, character, Int.cast_sum, Int.cast_mul]

theorem actualRow_historyEvent (G : SimpleGraph V) (c : V → Bool) (n : ℕ) (v : V) :
    actualRow G c (n + 1) v ∈ historyEvent (actualHistory G c (n + 1) v) := by
  intro r
  simp only [bits_actualHistory, imbalance_actualRow, Fin.val_castSucc, Fin.val_succ]
  rw [coloringOnDay_succ]
  exact (nextColoring_decision G _ v _).mp rfl

theorem actualRow_childEvent_iff (G : SimpleGraph V) (c : V → Bool) (n : ℕ)
    (v : V) (s : Universal.History (n + 1)) (b : Bool)
    (hs : actualHistory G c (n + 1) v = s) :
    actualRow G c (n + 1) v ∈ childEvent s b ↔
      coloringOnDayV G c (n + 2) v = b := by
  subst s
  change (_ ∧ _) ↔ _
  rw [and_iff_right (actualRow_historyEvent G c n v)]
  change decision (last (actualHistory G c (n + 1) v)) b
    (imbalance (Fin.last n) (actualRow G c (n + 1) v)) ↔ _
  simp only [last_actualHistory, imbalance_actualRow, Fin.val_last]
  rw [← nextColoring_decision, coloringOnDay_succ]

theorem child_block_event (G : SimpleGraph V) (c : V → Bool) (n : ℕ)
    (v : V) (s : Universal.History (n + 1)) (b : Bool) :
    v ∈ block (actualHistory G c (n + 2)) (append s b) ↔
      v ∈ block (actualHistory G c (n + 1)) s ∧
        actualRow G c (n + 1) v ∈ childEvent s b := by
  simp only [mem_block, actualHistory_child_iff]
  exact and_congr_right fun hs => (actualRow_childEvent_iff G c n v s b hs).symm

end MajorityDynamics.GraphProcess.History
