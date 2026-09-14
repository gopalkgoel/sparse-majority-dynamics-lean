import MajorityDynamics.Binomial.TiltUniqueness
import MajorityDynamics.Universal.Events

/-!
# The binomial row model of §3, shared with §5 and Appendix E

Sizes are arbitrary natural-number vectors, independent of any graph partition.
The diagonal trial count is exactly `n[t]-1`. History and child events reuse
§4's literal tie-retention predicates, not its almost-everywhere Gaussian cones.
All row probabilities and moments below refer to the actual product binomial law.
The paper's positivity/admissibility conditions are separate hypotheses.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace MajorityDynamics.Local

open Universal

abbrev Sizes (n : ℕ) := History (n + 1) → ℕ
abbrev Tilt (n : ℕ) := History (n + 1) → History (n + 1) → Binomial.Probability
abbrev EdgeCounts (n : ℕ) := History (n + 1) → History (n + 1) → ℝ

variable {n : ℕ}

def trials (sizes : Sizes n) (s t : History (n + 1)) : ℕ :=
  sizes t - if s = t then 1 else 0

@[simp] theorem trials_self (sizes : Sizes n) (s : History (n + 1)) :
    trials sizes s s = sizes s - 1 := by simp [trials]

theorem trials_other (sizes : Sizes n) {s t : History (n + 1)} (h : s ≠ t) :
    trials sizes s t = sizes t := by simp [trials, h]

def rowVector {sizes : Sizes n} {s : History (n + 1)}
    (a : Binomial.Box (trials sizes s)) : Row (n + 1) := WithLp.toLp 2 (Binomial.vector a)

def rowLaw (sizes : Sizes n) (q : Tilt n) (s : History (n + 1)) : Measure (History (n + 1) → ℕ) :=
  Binomial.law (trials sizes s) (q s)

def historySupport (sizes : Sizes n) (s : History (n + 1)) : Finset (Binomial.Box (trials sizes s)) := by
  classical
  exact Finset.univ.filter fun a => rowVector a ∈ historyEvent s

def childSupport (sizes : Sizes n) (s : History (n + 1)) (b : Bool) :
    Finset (Binomial.Box (trials sizes s)) := by
  classical
  exact Finset.univ.filter fun a => rowVector a ∈ childEvent s b

@[simp] theorem mem_historySupport (sizes : Sizes n) (s : History (n + 1))
    (a : Binomial.Box (trials sizes s)) : a ∈ historySupport sizes s ↔ rowVector a ∈ historyEvent s := by
  classical
  simp [historySupport]

@[simp] theorem mem_childSupport (sizes : Sizes n) (s : History (n + 1)) (b : Bool)
    (a : Binomial.Box (trials sizes s)) : a ∈ childSupport sizes s b ↔ rowVector a ∈ childEvent s b := by
  classical
  simp [childSupport]

theorem childSupport_subset (sizes : Sizes n) (s : History (n + 1)) (b : Bool) :
    childSupport sizes s b ⊆ historySupport sizes s := by
  intro a ha
  exact (mem_historySupport _ _ _).mpr ((mem_childSupport _ _ _ _).mp ha).1

theorem childSupport_disjoint (sizes : Sizes n) (s : History (n + 1)) :
    Disjoint (childSupport sizes s false) (childSupport sizes s true) := by
  classical
  rw [Finset.disjoint_left]
  intro a ha hb
  exact Set.disjoint_left.mp (childEvent_disjoint s)
    ((mem_childSupport _ _ _ _).mp ha) ((mem_childSupport _ _ _ _).mp hb)

theorem childSupport_union (sizes : Sizes n) (s : History (n + 1)) :
    childSupport sizes s false ∪ childSupport sizes s true = historySupport sizes s := by
  classical
  ext a
  simp only [Finset.mem_union, mem_childSupport, mem_historySupport]
  exact Set.ext_iff.mp (childEvent_union s) (rowVector a)

def rowCondition (sizes : Sizes n) (q : Tilt n) (s : History (n + 1)) :=
  Binomial.conditionalLaw (trials sizes s) (q s) (historySupport sizes s)

def rowMean (sizes : Sizes n) (q : Tilt n) (s t : History (n + 1)) : ℝ :=
  Binomial.conditionalMean (trials sizes s) (q s) (historySupport sizes s) t

theorem rowMean_eq_integral (sizes : Sizes n) (q : Tilt n) (s t : History (n + 1)) :
    rowMean sizes q s t = ∫ a, (a t : ℝ) ∂rowCondition sizes q s :=
  Binomial.conditionalMean_eq_integral _ _ _ _

def splitProbability (sizes : Sizes n) (q : Tilt n) (s : History (n + 1)) (b : Bool) : ℝ :=
  Binomial.eventMass (trials sizes s) (q s) (childSupport sizes s b) /
    Binomial.eventMass (trials sizes s) (q s) (historySupport sizes s)

def splitMoment (sizes : Sizes n) (q : Tilt n) (s : History (n + 1))
    (b : Bool) (t : History (n + 1)) : ℝ :=
  (∑ a ∈ childSupport sizes s b, Binomial.mass (trials sizes s) (q s) a * Binomial.vector a t) /
    Binomial.eventMass (trials sizes s) (q s) (historySupport sizes s)

/-- Exact edge-count constraints; existence is the later idealized/faithful theorem. -/
def Solves (sizes : Sizes n) (m : EdgeCounts n) (q : Tilt n) : Prop :=
  ∀ s t, (sizes s : ℝ) * rowMean sizes q s t = m s t

theorem solving_tilt_unique (sizes : Sizes n) (hsizes : ∀ s, 0 < sizes s) (m : EdgeCounts n)
    (hspan : ∀ s, Analysis.FiniteTilt.FullAffineSupport (historySupport sizes s) Binomial.vector)
    {q q' : Tilt n} (hq : Solves sizes m q) (hq' : Solves sizes m q') : q = q' := by
  let : Nonempty (History (n + 1)) := ⟨(bits _).symm (fun _ => false)⟩
  funext s
  apply Binomial.conditionalMean_injective (trials sizes s) (historySupport sizes s)
    (hspan s).nonempty (hspan s)
  funext t
  have hp : (sizes s : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hsizes s)
  exact (mul_left_cancel₀ hp) ((hq s t).trans (hq' s t).symm)

end MajorityDynamics.Local
