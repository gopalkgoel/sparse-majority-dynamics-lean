import MajorityDynamics.Literature.EdgeProbabilities.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite

noncomputable section
open MeasureTheory
open scoped Classical
namespace MajorityDynamics.Literature.LWAdapters
open MajorityDynamics.Probability.FixedDegreeSampling

theorem ncard_equiv {V W : Type*} (e : V ≃ W) (S : Set V) (T : Set W)
    (h : ∀ x, x ∈ S ↔ e x ∈ T) : S.ncard = T.ncard := by
  apply Set.ncard_congr (fun x _ => e x)
  · exact fun x hx => (h x).mp hx
  · exact fun x y _ _ hh => e.injective hh
  · intro y hy
    exact ⟨e.symm y, (h _).mpr (by simpa using hy), by simp⟩

theorem uniform_real_reindex {V W : Type*} [Fintype V] [Fintype W]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    [MeasurableSpace W] [MeasurableSingletonClass W]
    (e : V ≃ W) (S A : Set V) (T B : Set W)
    (hS : ∀ x, x ∈ S ↔ e x ∈ T) (hA : ∀ x, x ∈ A ↔ e x ∈ B) :
    (ProbabilityTheory.uniformOn S).real A = (ProbabilityTheory.uniformOn T).real B := by
  rw [measureReal_def, measureReal_def, uniform_apply, uniform_apply,
    ncard_equiv e S T hS, ncard_equiv e (S ∩ A) (T ∩ B) (fun x => and_congr (hS x) (hA x))]

def graphEquiv {V W : Type*} (e : V ≃ W) : SimpleGraph V ≃ SimpleGraph W where
  toFun G := G.comap e.symm
  invFun G := G.comap e
  left_inv G := by ext x y; simp
  right_inv G := by ext x y; simp

theorem degree_graphEquiv {V W : Type*} [Fintype V] [Fintype W]
    (e : V ≃ W) (G : SimpleGraph V) (w : W) :
    (graphEquiv e G).degree w = G.degree (e.symm w) := by
  exact ((SimpleGraph.Iso.comap e.symm G).degree_eq w).symm

theorem graph_family_reindex {V W : Type*} [Fintype V] [Fintype W]
    (e : V ≃ W) (d : V → ℕ) (G : SimpleGraph V) :
    G ∈ graphFamily d ↔ graphEquiv e G ∈ graphFamily (d ∘ e.symm) := by
  simp only [graphFamily, Set.mem_ofPred_eq, degree_graphEquiv, Function.comp_apply]
  exact e.symm.surjective.forall

theorem graph_law_reindex {V W : Type*} [Fintype V] [Fintype W]
    (e : V ≃ W) (d : V → ℕ) (a b : V) :
    (fixedDegreeLaw d).real {G | G.Adj a b} =
      (fixedDegreeLaw (d ∘ e.symm)).real {G | G.Adj (e a) (e b)} := by
  apply uniform_real_reindex (graphEquiv e) _ _ _ _ (graph_family_reindex e d)
  intro G
  simp [graphEquiv]

def crossEquiv {L R L' R' : Type*} (e : L ≃ L') (f : R ≃ R') :
    CrossEdges L R ≃ CrossEdges L' R' where
  toFun E := {p | (e.symm p.1, f.symm p.2) ∈ E}
  invFun E := {p | (e p.1, f p.2) ∈ E}
  left_inv E := by ext p; simp
  right_inv E := by ext p; simp

theorem leftDegree_crossEquiv {L R L' R' : Type*}
    [Fintype L] [Fintype R] [Fintype L'] [Fintype R']
    (e : L ≃ L') (f : R ≃ R') (E : CrossEdges L R) (i : L') :
    leftDegree (crossEquiv e f E) i = leftDegree E (e.symm i) := by
  unfold leftDegree
  apply Finset.card_bij (fun j _ => f.symm j)
  · intro j hj
    have hh := (Finset.mem_filter.mp hj).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩
  · exact fun j k _ _ h => f.symm.injective h
  · intro j hj
    refine ⟨f j, ?_, by simp⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change (e.symm i, f.symm (f j)) ∈ E
    simpa only [Equiv.symm_apply_apply] using (Finset.mem_filter.mp hj).2

theorem rightDegree_crossEquiv {L R L' R' : Type*}
    [Fintype L] [Fintype R] [Fintype L'] [Fintype R']
    (e : L ≃ L') (f : R ≃ R') (E : CrossEdges L R) (j : R') :
    rightDegree (crossEquiv e f E) j = rightDegree E (f.symm j) := by
  unfold rightDegree
  apply Finset.card_bij (fun i _ => e.symm i)
  · intro i hi
    have hh := (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩
  · exact fun i k _ _ h => e.symm.injective h
  · intro i hi
    refine ⟨e i, ?_, by simp⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change (e.symm (e i), f.symm j) ∈ E
    simpa only [Equiv.symm_apply_apply] using (Finset.mem_filter.mp hi).2

theorem bipartite_family_reindex {L R L' R' : Type*}
    [Fintype L] [Fintype R] [Fintype L'] [Fintype R']
    (e : L ≃ L') (f : R ≃ R') (a : L → ℕ) (b : R → ℕ) (E : CrossEdges L R) :
    E ∈ bipartiteFamily a b ↔
      crossEquiv e f E ∈ bipartiteFamily (a ∘ e.symm) (b ∘ f.symm) := by
  simp only [bipartiteFamily, Set.mem_ofPred_eq, leftDegree_crossEquiv,
    rightDegree_crossEquiv, Function.comp_apply]
  exact and_congr e.symm.surjective.forall f.symm.surjective.forall

theorem bipartite_law_reindex {L R L' R' : Type*}
    [Fintype L] [Fintype R] [Fintype L'] [Fintype R']
    (e : L ≃ L') (f : R ≃ R') (a : L → ℕ) (b : R → ℕ) (i : L) (j : R) :
    (bipartiteFixedDegreeLaw a b).real {E | (i,j) ∈ E} =
      (bipartiteFixedDegreeLaw (a ∘ e.symm) (b ∘ f.symm)).real {E | (e i,f j) ∈ E} := by
  apply uniform_real_reindex (crossEquiv e f) _ _ _ _ (bipartite_family_reindex e f a b)
  intro E
  simp [crossEquiv]

theorem degreeVariance_reindex {V W : Type*} [Fintype V] [Fintype W]
    (e : V ≃ W) (d : V → ℕ) (D : ℝ) :
    EdgeProbabilities.degreeVariance (d ∘ e.symm) D = EdgeProbabilities.degreeVariance d D := by
  unfold EdgeProbabilities.degreeVariance
  rw [Fintype.card_congr e]
  congr 1
  exact Equiv.sum_comp e.symm (fun i => ((d i : ℝ)-D)^2)

end MajorityDynamics.Literature.LWAdapters
