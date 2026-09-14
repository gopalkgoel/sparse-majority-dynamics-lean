import MajorityDynamics.GraphProcess.History.Dynamics

/-! Merging partition labels preserves the literal degree and edge totals. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace MajorityDynamics.GraphProcess.History
variable {V L M : Type*} [Fintype V] [Fintype L]

theorem sum_coarsen {A : Type*} [AddCommMonoid A] (π : V → L) (f : L → M)
    (a : V → A) (u : M) :
    ∑ v ∈ block (f ∘ π) u, a v = ∑ t ∈ block f u, ∑ v ∈ block π t, a v := by
  classical
  simp only [block, Finset.sum_filter]
  simp_rw [Finset.ite_sum_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  simp only [Function.comp_apply]
  simp_rw [← ite_and, and_comm, ite_and]
  simp

theorem degreeArray_coarsen (π : V → L) (G : SimpleGraph V) (f : L → M)
    (v : V) (u : M) :
    degreeArray (f ∘ π) G v u = ∑ t ∈ block f u, degreeArray π G v t := by
  classical
  exact sum_coarsen π f (fun w => if G.Adj v w then (1 : ℤ) else 0) u

theorem edgeTotals_coarsen (π : V → L) (G : SimpleGraph V) (f : L → M)
    (s t : M) :
    edgeTotals (f ∘ π) (degreeArray (f ∘ π) G) s t =
      ∑ a ∈ block f s, ∑ b ∈ block f t, edgeTotals π (degreeArray π G) a b := by
  unfold edgeTotals
  rw [sum_coarsen]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [degreeArray_coarsen]
  exact Finset.sum_comm

theorem sum_parent_fiber {k : ℕ} {A : Type*} [AddCommMonoid A]
    (a : Universal.History (k + 1) → A) (s : Universal.History k) :
    ∑ t ∈ block Universal.parent s, a t =
      a (Universal.append s false) + a (Universal.append s true) := by
  classical
  have hf : block Universal.parent s =
      {Universal.append s false, Universal.append s true} := by
    ext t
    simp only [mem_block, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      have ht := Universal.append_parent_last t
      rw [h] at ht
      cases hb : Universal.last t
      · exact Or.inl (by simpa [hb] using ht.symm)
      · exact Or.inr (by simpa [hb] using ht.symm)
    · rintro (rfl | rfl) <;> simp
  have hn : Universal.append s false ≠ Universal.append s true := by
    intro h
    have := congrArg Universal.last h
    simp at this
  rw [hf]
  simp [hn]

theorem degreeArray_parent (G : SimpleGraph V) (c : V → Bool) (k : ℕ)
    (v : V) (s : Universal.History k) :
    degreeArray (actualHistory G c k) G v s =
      degreeArray (actualHistory G c (k + 1)) G v (Universal.append s false) +
      degreeArray (actualHistory G c (k + 1)) G v (Universal.append s true) := by
  have hp : Universal.parent ∘ actualHistory G c (k + 1) = actualHistory G c k := by
    funext w
    simp
  rw [← hp, degreeArray_coarsen, sum_parent_fiber]

theorem edgeTotals_parent (G : SimpleGraph V) (c : V → Bool) (k : ℕ)
    (s t : Universal.History k) :
    edgeTotals (actualHistory G c k) (degreeArray (actualHistory G c k) G) s t =
      ∑ a : Bool, ∑ b : Bool,
        edgeTotals (actualHistory G c (k + 1)) (degreeArray (actualHistory G c (k + 1)) G)
          (Universal.append s a) (Universal.append t b) := by
  have hp : Universal.parent ∘ actualHistory G c (k + 1) = actualHistory G c k := by
    funext w
    simp
  rw [← hp, edgeTotals_coarsen]
  simp only [sum_parent_fiber]
  simp [add_comm]

end MajorityDynamics.GraphProcess.History
