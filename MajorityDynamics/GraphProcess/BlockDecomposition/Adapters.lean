import MajorityDynamics.GraphProcess.BlockDecomposition.Edges
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.BlockDecomposition
open History
open MajorityDynamics.Probability.FixedDegreeSampling
variable {V L : Type*} [Fintype V]

private theorem cast_eq_iff (n : ℕ) (z : ℤ) (hz : 0 ≤ z) :
    (n : ℤ) = z ↔ n = z.toNat := by omega

/-- Identity on actual graphs; nonnegativity justifies the natural-degree API. -/
def internalNatEquiv (π : V → L) (d : V → L → ℤ) (s : L)
    (hd : ∀ v : Block π s, 0 ≤ d v s) :
    InternalFiber π d s ≃ graphFamily (fun v : Block π s => (d v s).toNat) :=
  Equiv.subtypeEquivRight fun G => by
    change (∀ v, (G.degree v : ℤ) = d v s) ↔ ∀ v, G.degree v = (d v s).toNat
    exact forall_congr' fun v => cast_eq_iff _ _ (hd v)

/-- Identity on actual cross-edge subsets, with both side casts justified. -/
def crossNatEquiv (π : V → L) (d : V → L → ℤ) (s t : L)
    (hl : ∀ v : Block π s, 0 ≤ d v t) (hr : ∀ w : Block π t, 0 ≤ d w s) :
    CrossFiber π d s t ≃
      bipartiteFamily (fun v : Block π s => (d v t).toNat)
        (fun w : Block π t => (d w s).toNat) :=
  Equiv.subtypeEquivRight fun E => by
    change ((∀ v, (leftDegree E v : ℤ) = d v t) ∧
      ∀ w, (rightDegree E w : ℤ) = d w s) ↔
      (∀ v, leftDegree E v = (d v t).toNat) ∧ ∀ w, rightDegree E w = (d w s).toNat
    exact and_congr (forall_congr' fun v => cast_eq_iff _ _ (hl v))
      (forall_congr' fun w => cast_eq_iff _ _ (hr w))

@[simp] theorem internalNatEquiv_val (π : V → L) (d : V → L → ℤ) (s : L)
    (hd : ∀ v : Block π s, 0 ≤ d v s) (G : InternalFiber π d s) :
    (internalNatEquiv π d s hd G).val = G.val := rfl

@[simp] theorem crossNatEquiv_val (π : V → L) (d : V → L → ℤ) (s t : L)
    (hl : ∀ v : Block π s, 0 ≤ d v t) (hr : ∀ w : Block π t, 0 ≤ d w s)
    (E : CrossFiber π d s t) : (crossNatEquiv π d s t hl hr E).val = E.val := rfl

theorem internal_count_nat (π : V → L) (d : V → L → ℤ) (s : L)
    (hd : ∀ v : Block π s, 0 ≤ d v s) :
    Nat.card (InternalFiber π d s) = graphCount (fun v : Block π s => (d v s).toNat) := by
  exact Nat.card_congr (internalNatEquiv π d s hd)

theorem cross_count_nat (π : V → L) (d : V → L → ℤ) (s t : L)
    (hl : ∀ v : Block π s, 0 ≤ d v t) (hr : ∀ w : Block π t, 0 ≤ d w s) :
    Nat.card (CrossFiber π d s t) =
      bipartiteCount (fun v : Block π s => (d v t).toNat)
        (fun w : Block π t => (d w s).toNat) := by
  exact Nat.card_congr (crossNatEquiv π d s t hl hr)

variable {n : ℕ}

theorem fact_graphical_blockwise {k : ℕ} (π : V → Universal.History k)
    (d : V → Universal.History k → ℤ) :
    FineState.Realizable π d ↔
      (∀ s, InternalGraphical π d s) ∧
      (∀ s t, s ≠ t → CrossGraphical π d s t) := graphical_blockwise π d

def stateFiberEquiv (σ : FineState.State V n) :
    GraphFiber σ.part σ.deg ≃ ComponentFiber σ.part σ.deg := fiberEquiv σ.part σ.deg

theorem state_components_nonempty (σ : FineState.State V n) :
    Nonempty (ComponentFiber σ.part σ.deg) := by
  obtain ⟨G, hG⟩ := σ.realizable
  exact ⟨stateFiberEquiv σ ⟨G, hG⟩⟩

theorem state_internal_nonempty (σ : FineState.State V n) (s : Universal.History (n+1)) :
    Nonempty (InternalFiber σ.part σ.deg s) := by
  obtain ⟨F⟩ := state_components_nonempty σ
  exact ⟨F.1 s⟩

theorem state_cross_nonempty (σ : FineState.State V n)
    (s t : Universal.History (n+1)) : Nonempty (CrossFiber σ.part σ.deg s t) := by
  obtain ⟨G, hG⟩ := σ.realizable
  exact ⟨⟨cross σ.part G s t,
    fun v => (cross_leftDegree σ.part G s t v).trans (congrFun (congrFun hG v) t),
    fun w => (cross_rightDegree σ.part G s t w).trans (congrFun (congrFun hG w) s)⟩⟩

theorem state_degree_nonneg (σ : FineState.State V n) (v : V)
    (t : Universal.History (n+1)) : 0 ≤ σ.deg v t := by
  obtain ⟨G, hG⟩ := σ.realizable
  rw [← hG]
  exact degreeArray_nonneg σ.part G v t

theorem state_degree_toNat_cast (σ : FineState.State V n) (v : V)
    (t : Universal.History (n+1)) : ((σ.deg v t).toNat : ℤ) = σ.deg v t :=
  Int.toNat_of_nonneg (state_degree_nonneg σ v t)

def stateInternalNatEquiv (σ : FineState.State V n) (s : Universal.History (n+1)) :
    InternalFiber σ.part σ.deg s ≃
      graphFamily (fun v : Block σ.part s => (σ.deg v s).toNat) :=
  (internalNatEquiv σ.part σ.deg s (fun v => state_degree_nonneg σ v s)).trans
    (Equiv.setCongr (by congr 1; exact Subsingleton.elim _ _))

def stateCrossNatEquiv (σ : FineState.State V n) (s t : Universal.History (n+1)) :
    CrossFiber σ.part σ.deg s t ≃
      bipartiteFamily (fun v : Block σ.part s => (σ.deg v t).toNat)
        (fun w : Block σ.part t => (σ.deg w s).toNat) :=
  (crossNatEquiv σ.part σ.deg s t (fun v => state_degree_nonneg σ v t)
    (fun w => state_degree_nonneg σ w s)).trans
    (Equiv.setCongr (by congr 1 <;> exact Subsingleton.elim _ _))

theorem state_graphFamily_nonempty (σ : FineState.State V n) (s : Universal.History (n+1)) :
    (graphFamily (fun v : Block σ.part s => (σ.deg v s).toNat)).Nonempty := by
  obtain ⟨G⟩ := state_internal_nonempty σ s
  exact ⟨(stateInternalNatEquiv σ s G).val, (stateInternalNatEquiv σ s G).property⟩

theorem state_bipartiteFamily_nonempty (σ : FineState.State V n)
    (s t : Universal.History (n+1)) :
    (bipartiteFamily (fun v : Block σ.part s => (σ.deg v t).toNat)
      (fun w : Block σ.part t => (σ.deg w s).toNat)).Nonempty := by
  obtain ⟨E⟩ := state_cross_nonempty σ s t
  exact ⟨(stateCrossNatEquiv σ s t E).val, (stateCrossNatEquiv σ s t E).property⟩

/-- Exact product of the existing fixed-degree sampling counts. -/
theorem state_realization_count (σ : FineState.State V n) :
    Nat.card (GraphFiber σ.part σ.deg) =
      (∏ s, graphCount (fun v : Block σ.part s => (σ.deg v s).toNat)) *
      ∏ p : Pair (Universal.History (n+1)),
        bipartiteCount (fun v : Block σ.part p.val.1 => (σ.deg v p.val.2).toNat)
          (fun w : Block σ.part p.val.2 => (σ.deg w p.val.1).toNat) := by
  rw [realization_count]
  congr 1
  · apply Finset.prod_congr rfl
    intro s _
    convert! internal_count_nat σ.part σ.deg s (fun v => state_degree_nonneg σ v s) using 1
    exact congrArg (fun fi : Fintype (Block σ.part s) =>
      @graphCount (Block σ.part s) fi (fun v => (σ.deg v s).toNat)) (Subsingleton.elim _ _)
  · apply Finset.prod_congr (Finset.ext (fun _ => by simp only [Finset.mem_univ]))
    intro p _
    convert! cross_count_nat σ.part σ.deg p.val.1 p.val.2 (fun v => state_degree_nonneg σ v p.val.2)
      (fun w => state_degree_nonneg σ w p.val.1) using 1
    exact congrArg₂ (fun (fi : Fintype (Block σ.part p.val.1))
        (fj : Fintype (Block σ.part p.val.2)) =>
      @bipartiteCount (Block σ.part p.val.1) (Block σ.part p.val.2) fi fj
        (fun v => (σ.deg v p.val.2).toNat) (fun w => (σ.deg w p.val.1).toNat))
      (Subsingleton.elim _ _) (Subsingleton.elim _ _)

end MajorityDynamics.GraphProcess.BlockDecomposition
