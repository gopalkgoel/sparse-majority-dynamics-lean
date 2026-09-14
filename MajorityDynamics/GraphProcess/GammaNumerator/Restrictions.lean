import MajorityDynamics.GraphProcess.RowArray.Statistics
import MajorityDynamics.Probability.DegreeConcentration.Sites
import MajorityDynamics.Probability.DegreeConcentration.Basic

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq

namespace MajorityDynamics.GraphProcess.GammaNumerator
open MajorityDynamics.Probability.DegreeConcentration
variable {V L : Type*} [Fintype V]

abbrev Block (π : V → L) (s : L) := {v : V // π v = s}
def blockSize (π : V → L) (s : L) : ℕ := Fintype.card (Block π s)
def blockEquiv (π : V → L) (s : L) : Fin (blockSize π s) ≃ Block π s :=
  (Fintype.equivFin (Block π s)).symm
def vertex (π : V → L) (s : L) (i : Fin (blockSize π s)) : V :=
  (blockEquiv π s i).val

theorem vertex_label (π : V → L) (s : L) (i : Fin (blockSize π s)) :
    π (vertex π s i) = s := (blockEquiv π s i).property

theorem vertex_injective (π : V → L) (s : L) : Function.Injective (vertex π s) :=
  Subtype.val_injective.comp (blockEquiv π s).injective

@[simp] theorem blockSize_eq {n : ℕ} (π : V → Universal.History (n+1))
    (s : Universal.History (n+1)) : blockSize π s = Local.partSizes π s := by
  rw [blockSize, Fintype.card_subtype]
  calc
    _ = (History.block π s).card := by
      congr 1
      ext v
      simp [History.block]
    _ = _ := History.block_card_partSizes π s

def internal (π : V → L) (s : L) (G : SimpleGraph V) : Graph (blockSize π s) :=
  G.comap (vertex π s)

def cross (π : V → L) (s t : L) (G : SimpleGraph V) :
    CrossEdges (blockSize π s) (blockSize π t) :=
  {e | G.Adj (vertex π s e.1) (vertex π t e.2)}

@[simp] theorem internal_adj (π : V → L) (s : L) (G : SimpleGraph V)
    (i j : Fin (blockSize π s)) :
    (internal π s G).Adj i j ↔ G.Adj (vertex π s i) (vertex π s j) := Iff.rfl

@[simp] theorem mem_cross (π : V → L) (s t : L) (G : SimpleGraph V)
    (e : Fin (blockSize π s) × Fin (blockSize π t)) :
    e ∈ cross π s t G ↔ G.Adj (vertex π s e.1) (vertex π t e.2) := Iff.rfl

/-- Injective selection of Bernoulli coordinates preserves their actual joint product law. -/
theorem siteLaw_map_restrict {A B : Type*} [Fintype A] [Fintype B]
    (u : Set A) (v : Set B) (e : B ↪ A) (p : unitInterval)
    (he : ∀ b, e b ∈ u ↔ b ∈ v) :
    (siteLaw u p).map (fun ω b => ω (e b)) = siteLaw v p := by
  have hi := (iIndepFun_infinitePi (P := fun a : A => Ber(a ∈ u, False, p))
    (X := fun _ (q : Prop) => q) (fun _ => measurable_id)).precomp e.injective
  unfold siteLaw
  rw [hi.map_fun_eq_infinitePi_map (fun _ => by fun_prop)]
  congr 1
  funext b
  rw [Measure.infinitePi_map_eval]
  simp only [he b]

def internalEmbedding (π : V → L) (s : L) : Sym2 (Fin (blockSize π s)) ↪ Sym2 V :=
  (⟨vertex π s, vertex_injective π s⟩ : Fin (blockSize π s) ↪ V).sym2Map

theorem internalEmbedding_diag (π : V → L) (s : L) (e : Sym2 (Fin (blockSize π s))) :
    internalEmbedding π s e ∈ (Sym2.diagSetᶜ : Set (Sym2 V)) ↔
      e ∈ (Sym2.diagSetᶜ : Set (Sym2 (Fin (blockSize π s)))) := by
  induction e using Sym2.inductionOn with
  | _ i j => simp [internalEmbedding, (vertex_injective π s).eq_iff]

theorem internal_fromEdgeSet (π : V → L) (s : L) (ω : Sym2 V → Prop) :
    internal π s (SimpleGraph.fromEdgeSet {e | ω e}) =
      SimpleGraph.fromEdgeSet {e | ω (internalEmbedding π s e)} := by
  ext i j
  simp [internal, SimpleGraph.fromEdgeSet_adj, internalEmbedding,
    (vertex_injective π s).eq_iff]

/-- The actual reindexed induced graph has A.10's binomial graph law. -/
theorem internal_law (π : V → L) (s : L) (p : unitInterval) :
    (SimpleGraph.binomialRandom V p).map (internal π s) = graphLaw (blockSize π s) p := by
  rw [binomialRandom_eq_map_siteLaw, Measure.map_map (by fun_prop) (by fun_prop)]
  have hf : (internal π s ∘ fun ω : Sym2 V → Prop => SimpleGraph.fromEdgeSet {e | ω e}) =
      (fun ω : Sym2 (Fin (blockSize π s)) → Prop => SimpleGraph.fromEdgeSet {e | ω e}) ∘
        (fun ω e => ω (internalEmbedding π s e)) := by
    funext ω
    exact internal_fromEdgeSet π s ω
  rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop),
    siteLaw_map_restrict _ _ _ p (internalEmbedding_diag π s)]
  exact (binomialRandom_eq_map_siteLaw (Fin (blockSize π s)) p).symm

theorem cross_vertex_ne (π : V → L) {s t : L} (hst : s ≠ t)
    (i : Fin (blockSize π s)) (j : Fin (blockSize π t)) :
    vertex π s i ≠ vertex π t j := by
  intro h
  have hh := congrArg π h
  rw [vertex_label π s i, vertex_label π t j] at hh
  exact hst hh

def crossEmbedding (π : V → L) (s t : L) (hst : s ≠ t) :
    (Fin (blockSize π s) × Fin (blockSize π t)) ↪ Sym2 V where
  toFun e := s(vertex π s e.1, vertex π t e.2)
  inj' := by
    intro a b h
    rcases Sym2.eq_iff.mp h with h | h
    · exact Prod.ext ((vertex_injective π s) h.1) ((vertex_injective π t) h.2)
    · exact False.elim (cross_vertex_ne π hst _ _ h.1)

theorem crossEmbedding_nondiag (π : V → L) (s t : L) (hst : s ≠ t)
    (e : Fin (blockSize π s) × Fin (blockSize π t)) :
    crossEmbedding π s t hst e ∈ (Sym2.diagSetᶜ : Set (Sym2 V)) := by
  change ¬ (s(vertex π s e.1, vertex π t e.2)).IsDiag
  exact cross_vertex_ne π hst e.1 e.2

theorem cross_fromEdgeSet (π : V → L) (s t : L) (hst : s ≠ t) (ω : Sym2 V → Prop) :
    cross π s t (SimpleGraph.fromEdgeSet {e | ω e}) =
      {e | ω (crossEmbedding π s t hst e)} := by
  ext e
  change (SimpleGraph.fromEdgeSet {e | ω e}).Adj (vertex π s e.1) (vertex π t e.2) ↔
    ω s(vertex π s e.1, vertex π t e.2)
  simp [SimpleGraph.fromEdgeSet_adj, cross_vertex_ne π hst]

/-- The actual cross-edge restriction has A.10's independent bipartite law. -/
theorem cross_law (π : V → L) (s t : L) (hst : s ≠ t) (p : unitInterval) :
    (SimpleGraph.binomialRandom V p).map (cross π s t) =
      bipartiteLaw (blockSize π s) (blockSize π t) p := by
  rw [binomialRandom_eq_map_siteLaw, Measure.map_map (by fun_prop) (by fun_prop)]
  have hf : (cross π s t ∘ fun ω : Sym2 V → Prop => SimpleGraph.fromEdgeSet {e | ω e}) =
      (fun ω : (Fin (blockSize π s) × Fin (blockSize π t)) → Prop => {e | ω e}) ∘
        (fun ω e => ω (crossEmbedding π s t hst e)) := by
    funext ω
    exact cross_fromEdgeSet π s t hst ω
  rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop),
    siteLaw_map_restrict _ Set.univ _ p (fun e => by
      simp only [Set.mem_univ, iff_true]; exact crossEmbedding_nondiag π s t hst e)]
  exact (setBernoulli_eq_map_siteLaw Set.univ p).symm

end MajorityDynamics.GraphProcess.GammaNumerator
