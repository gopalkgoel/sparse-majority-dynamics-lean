import MajorityDynamics.Idealized.Process.Basic

/-!
# Exact reflection for the idealized process

The reflection permutes binomial coordinates; it does not negate them. All
identities below retain the original tie decisions and the one-trial diagonal
deletion. They are finite-sum identities for the actual row law, including its
conditional moments. Uniqueness of a solving tilt then forces its symmetry.
-/

noncomputable section
open scoped BigOperators

namespace MajorityDynamics.Idealized.Process

open Universal Local

variable {n : ℕ}

theorem decision_flip (old new : Bool) (z : ℝ) :
    decision (!old) (!new) (-z) ↔ decision old new z := by
  cases old <;> cases new <;> simp [decision, sign]

theorem rowFlip_mem_historyEvent (s : History (n + 1)) (x : Row (n + 1)) :
    rowFlip x ∈ historyEvent (flip s) ↔ x ∈ historyEvent s := by
  simp only [historyEvent, Set.mem_ofPred_eq, bits_flip, imbalance_rowFlip,
    decision_flip]

theorem rowFlip_mem_childEvent (s : History (n + 1)) (b : Bool)
    (x : Row (n + 1)) :
    rowFlip x ∈ childEvent (flip s) (!b) ↔ x ∈ childEvent s b := by
  simp only [childEvent, Set.mem_inter_iff, Set.mem_ofPred_eq,
    rowFlip_mem_historyEvent, last, bits_flip, imbalance_rowFlip, decision_flip]

@[simp] theorem parent_flip {k : ℕ} (s : History (k + 1)) :
    parent (flip s) = flip (parent s) := by
  rw [← append_parent_last s, flip_append]
  simp only [parent_append]

@[simp] theorem last_flip {k : ℕ} (s : History (k + 1)) :
    last (flip s) = !(last s) := by simp only [last, bits_flip]

theorem symmetric_imbalance_eq_zero (x : State n) (hx : StateSymmetric x)
    (r : Fin (n + 1)) :
    imbalance r (WithLp.toLp 2 (fun t => (x.sizes t : ℝ))) = 0 := by
  apply sum_character_of_flip_invariant
  intro t
  change (x.sizes (flip t) : ℝ) = (x.sizes t : ℝ)
  rw [hx.sizes]

theorem symmetric_history_balance (x : State n) (hx : StateSymmetric x)
    (s : History (n + 1)) (r : Fin n) :
    (∑ t, historyMatrix s r t * (x.sizes t : ℝ)) = 0 := by
  simp only [historyMatrix, mul_assoc, ← Finset.mul_sum]
  rw [show (∑ t, character r.castSucc t * (x.sizes t : ℝ)) = 0 from
    symmetric_imbalance_eq_zero x hx r.castSucc, mul_zero]

def reflectedTilt (q : Local.Tilt n) : Local.Tilt n :=
  fun s t => q (flip s) (flip t)

theorem trials_flip (sizes : Local.Sizes n)
    (hs : ∀ t, sizes (flip t) = sizes t) (s t : History (n + 1)) :
    trials sizes (flip s) (flip t) = trials sizes s t := by
  have hf : Function.Injective (@flip (n + 1)) := (flipEquiv (n + 1)).injective
  simp only [trials, hs, hf.eq_iff]

/-- The actual finite row-support equivalence, with dependent trial bounds. -/
def flipBox (sizes : Local.Sizes n) (hs : ∀ t, sizes (flip t) = sizes t)
    (s : History (n + 1)) (a : Binomial.Box (trials sizes s)) :
    Binomial.Box (trials sizes (flip s)) := fun t =>
  ⟨a (flip t), by simpa only [← trials_flip sizes hs s (flip t), Universal.flip_flip] using
    (a (flip t)).isLt⟩

@[simp] theorem flipBox_apply (sizes : Local.Sizes n)
    (hs : ∀ t, sizes (flip t) = sizes t) (s : History (n + 1))
    (a : Binomial.Box (trials sizes s)) (t : History (n + 1)) :
    (flipBox sizes hs s a t : ℕ) = a (flip t) := rfl

@[simp] theorem flipBox_flip_apply (sizes : Local.Sizes n)
    (hs : ∀ t, sizes (flip t) = sizes t) (s : History (n + 1))
    (a : Binomial.Box (trials sizes s)) (t : History (n + 1)) :
    (flipBox sizes hs s a (flip t) : ℕ) = a t :=
  congrArg (fun j => (a j : ℕ)) (Universal.flip_flip t)

def boxFlipEquiv (sizes : Local.Sizes n) (hs : ∀ t, sizes (flip t) = sizes t)
    (s : History (n + 1)) :
    Binomial.Box (trials sizes s) ≃ Binomial.Box (trials sizes (flip s)) where
  toFun := flipBox sizes hs s
  invFun a t := ⟨a (flip t), by
    simpa only [trials_flip sizes hs s t] using (a (flip t)).isLt⟩
  left_inv a := by
    funext t
    apply Fin.ext
    exact congrArg (fun j => (a j : ℕ)) (Universal.flip_flip t)
  right_inv a := by
    funext t
    apply Fin.ext
    exact congrArg (fun j => (a j : ℕ)) (Universal.flip_flip t)

@[simp] theorem boxFlipEquiv_apply (sizes : Local.Sizes n)
    (hs : ∀ t, sizes (flip t) = sizes t) (s : History (n + 1))
    (a : Binomial.Box (trials sizes s)) :
    boxFlipEquiv sizes hs s a = flipBox sizes hs s a := rfl

theorem rowVector_flipBox (sizes : Local.Sizes n)
    (hs : ∀ t, sizes (flip t) = sizes t) (s : History (n + 1))
    (a : Binomial.Box (trials sizes s)) :
    rowVector (flipBox sizes hs s a) = rowFlip (rowVector a) := rfl

theorem mass_flipBox (sizes : Local.Sizes n)
    (hs : ∀ t, sizes (flip t) = sizes t) (q : Local.Tilt n)
    (s : History (n + 1)) (a : Binomial.Box (trials sizes s)) :
    Binomial.mass (trials sizes (flip s)) (q (flip s)) (flipBox sizes hs s a) =
      Binomial.mass (trials sizes s) (reflectedTilt q s) a := by
  classical
  unfold Binomial.mass
  rw [← Equiv.prod_comp (flipEquiv (n + 1))]
  simp only [flipEquiv, Equiv.coe_fn_mk, trials_flip sizes hs, flipBox_flip_apply,
    reflectedTilt]

theorem sum_history_flip (sizes : Local.Sizes n)
    (hs : ∀ t, sizes (flip t) = sizes t) (s : History (n + 1))
    (f : Binomial.Box (trials sizes (flip s)) → ℝ) :
    (∑ a ∈ historySupport sizes (flip s), f a) =
      ∑ a ∈ historySupport sizes s, f (flipBox sizes hs s a) := by
  classical
  simp only [historySupport, Finset.sum_filter]
  rw [← (boxFlipEquiv sizes hs s).sum_comp]
  simp only [boxFlipEquiv_apply, rowVector_flipBox, rowFlip_mem_historyEvent]

theorem sum_child_flip (sizes : Local.Sizes n)
    (hs : ∀ t, sizes (flip t) = sizes t) (s : History (n + 1)) (b : Bool)
    (f : Binomial.Box (trials sizes (flip s)) → ℝ) :
    (∑ a ∈ childSupport sizes (flip s) (!b), f a) =
      ∑ a ∈ childSupport sizes s b, f (flipBox sizes hs s a) := by
  classical
  simp only [childSupport, Finset.sum_filter]
  rw [← (boxFlipEquiv sizes hs s).sum_comp]
  simp only [boxFlipEquiv_apply, rowVector_flipBox, rowFlip_mem_childEvent]

theorem historyMass_reflectedTilt (sizes : Local.Sizes n)
    (hs : ∀ t, sizes (flip t) = sizes t) (q : Local.Tilt n)
    (s : History (n + 1)) :
    Binomial.eventMass (trials sizes s) (reflectedTilt q s) (historySupport sizes s) =
      Binomial.eventMass (trials sizes (flip s)) (q (flip s))
        (historySupport sizes (flip s)) := by
  rw [Binomial.eventMass, Binomial.eventMass, sum_history_flip sizes hs]
  simp only [mass_flipBox]

theorem childMass_reflectedTilt (sizes : Local.Sizes n)
    (hs : ∀ t, sizes (flip t) = sizes t) (q : Local.Tilt n)
    (s : History (n + 1)) (b : Bool) :
    Binomial.eventMass (trials sizes s) (reflectedTilt q s) (childSupport sizes s b) =
      Binomial.eventMass (trials sizes (flip s)) (q (flip s))
        (childSupport sizes (flip s) (!b)) := by
  rw [Binomial.eventMass, Binomial.eventMass, sum_child_flip sizes hs]
  simp only [mass_flipBox]

theorem rowMean_reflectedTilt (sizes : Local.Sizes n)
    (hs : ∀ t, sizes (flip t) = sizes t) (q : Local.Tilt n)
    (s t : History (n + 1)) :
    rowMean sizes (reflectedTilt q) s t = rowMean sizes q (flip s) (flip t) := by
  simp only [rowMean, Binomial.conditionalMean, Binomial.expectation,
    Binomial.conditionalWeight]
  rw [sum_history_flip sizes hs]
  simp only [mass_flipBox, ← historyMass_reflectedTilt sizes hs q s,
    Binomial.vector, flipBox_flip_apply]

theorem splitProbability_reflectedTilt (sizes : Local.Sizes n)
    (hs : ∀ t, sizes (flip t) = sizes t) (q : Local.Tilt n)
    (s : History (n + 1)) (b : Bool) :
    splitProbability sizes (reflectedTilt q) s b =
      splitProbability sizes q (flip s) (!b) := by
  simp only [splitProbability, historyMass_reflectedTilt sizes hs,
    childMass_reflectedTilt sizes hs]

theorem splitMoment_reflectedTilt (sizes : Local.Sizes n)
    (hs : ∀ t, sizes (flip t) = sizes t) (q : Local.Tilt n)
    (s : History (n + 1)) (b : Bool) (t : History (n + 1)) :
    splitMoment sizes (reflectedTilt q) s b t =
      splitMoment sizes q (flip s) (!b) (flip t) := by
  simp only [splitMoment]
  rw [sum_child_flip sizes hs]
  simp only [mass_flipBox, ← historyMass_reflectedTilt sizes hs q s,
    Binomial.vector, flipBox_flip_apply]

theorem reflectedTilt_solves (x : State n) (hx : StateSymmetric x)
    (q : Local.Tilt n) (hq : Local.Solves x.sizes x.edges q) :
    Local.Solves x.sizes x.edges (reflectedTilt q) := by
  intro s t
  rw [rowMean_reflectedTilt x.sizes hx.sizes, ← hx.sizes s,
    hq (flip s) (flip t), hx.edges]

theorem solving_tilt_symmetric (x : State n) (hx : StateSymmetric x)
    (q : Local.Tilt n) (hq : Solvable x q) : TiltSymmetric q := by
  have he := hq.unique (reflectedTilt q) (reflectedTilt_solves x hx q hq.solves)
  intro s t
  exact congrFun (congrFun he s) t

theorem templateSizes_flip (x : State n) (hx : StateSymmetric x)
    (q : Local.Tilt n) (hq : TiltSymmetric q) (u : History (n + 2)) :
    templateSizes x.sizes q (flip u) = templateSizes x.sizes q u := by
  have he : reflectedTilt q = q := funext fun s => funext fun t => hq s t
  have hsplit := splitProbability_reflectedTilt x.sizes hx.sizes q (parent u) (last u)
  rw [he] at hsplit
  simp only [templateSizes, parent_flip, last_flip, hx.sizes, ← hsplit]

theorem templateHalfEdges_flip (x : State n) (hx : StateSymmetric x)
    (q : Local.Tilt n) (hq : TiltSymmetric q) (u : History (n + 2))
    (t : History (n + 1)) :
    templateHalfEdges x.sizes q (flip u) (flip t) = templateHalfEdges x.sizes q u t := by
  have he : reflectedTilt q = q := funext fun s => funext fun t => hq s t
  have hsplit := splitMoment_reflectedTilt x.sizes hx.sizes q (parent u) (last u) t
  rw [he] at hsplit
  simp only [templateHalfEdges, parent_flip, last_flip, hx.sizes, ← hsplit]

theorem templateEdges_flip (x : State n) (hx : StateSymmetric x)
    (q : Local.Tilt n) (hq : TiltSymmetric q) (u v : History (n + 2)) :
    templateEdges x.sizes x.edges q (flip u) (flip v) =
      templateEdges x.sizes x.edges q u v := by
  simp only [templateEdges, parent_flip, templateHalfEdges_flip x hx q hq, hx.edges]

theorem nextState_symmetric (x : State n) (hx : StateSymmetric x)
    (q : Local.Tilt n) (hq : TiltSymmetric q) : StateSymmetric (nextState x q) where
  sizes u := congrArg Nat.floor (templateSizes_flip x hx q hq u)
  edges := templateEdges_flip x hx q hq

theorem initialState_symmetric (N : ℕ) (p : Binomial.Probability) :
    StateSymmetric (initialState N p) where
  sizes _ := rfl
  edges s t := by
    have hf : Function.Injective (@flip 1) := (flipEquiv 1).injective
    simp only [initialState, hf.eq_iff]

end MajorityDynamics.Idealized.Process
