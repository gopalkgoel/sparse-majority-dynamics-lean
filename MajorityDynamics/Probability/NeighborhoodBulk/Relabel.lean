import MajorityDynamics.Probability.NeighborhoodBulk.Adapters

/-! Cardinality transport between labeled carriers, including deletion subtypes.
The graph objects and cross-edge families are the actual sampling spaces. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodBulk
open FixedDegreeSampling
variable {V W L L' R R' : Type*}
  [Fintype V] [Fintype W] [Fintype L] [Fintype L'] [Fintype R] [Fintype R']

theorem graph_relabel_degree (e : V ≃ W) (G : SimpleGraph V) (w : W) :
    (e.simpleGraph G).degree w = G.degree (e.symm w) := by
  exact (SimpleGraph.Iso.comap e.symm G).degree_eq w |>.symm

theorem graph_relabel_mem (e : V ≃ W) (d : V → ℕ) (G : SimpleGraph V) :
    e.simpleGraph G ∈ graphFamily (fun w => d (e.symm w)) ↔ G ∈ graphFamily d := by
  change (∀ w, (e.simpleGraph G).degree w = d (e.symm w)) ↔ _
  simp_rw [graph_relabel_degree]
  exact (e.symm.surjective.forall (p := fun v => G.degree v = d v)).symm

theorem graphCount_relabel (e : V ≃ W) (d : V → ℕ) :
    graphCount (fun w => d (e.symm w)) = graphCount d := by
  symm
  apply Set.ncard_congr (fun G _ => e.simpleGraph G)
  · intro G hG
    exact (graph_relabel_mem e d G).mpr hG
  · intro G H _ _ h
    exact e.simpleGraph.injective h
  · intro H hH
    obtain ⟨G, rfl⟩ := e.simpleGraph.surjective H
    exact ⟨G, (graph_relabel_mem e d G).mp hH, rfl⟩

def crossRelabel (e : L ≃ L') (f : R ≃ R') (E : CrossEdges L R) : CrossEdges L' R' :=
  (e.prodCongr f).symm ⁻¹' E

omit [Fintype L] [Fintype L'] in
theorem crossRelabel_leftNeighbors (e : L ≃ L') (f : R ≃ R')
    (E : CrossEdges L R) (v : L') :
    leftNeighbors (crossRelabel e f E) v = (leftNeighbors E (e.symm v)).map f.toEmbedding := by
  ext w
  simp [leftNeighbors, crossRelabel]

omit [Fintype R] [Fintype R'] in
theorem crossRelabel_rightNeighbors (e : L ≃ L') (f : R ≃ R')
    (E : CrossEdges L R) (w : R') :
    rightNeighbors (crossRelabel e f E) w = (rightNeighbors E (f.symm w)).map e.toEmbedding := by
  ext v
  simp [rightNeighbors, crossRelabel]

omit [Fintype L] [Fintype L'] in
theorem crossRelabel_leftDegree (e : L ≃ L') (f : R ≃ R') (E : CrossEdges L R) (v : L') :
    leftDegree (crossRelabel e f E) v = leftDegree E (e.symm v) := by
  simp only [leftDegree, crossRelabel_leftNeighbors, Finset.card_map]

omit [Fintype R] [Fintype R'] in
theorem crossRelabel_rightDegree (e : L ≃ L') (f : R ≃ R') (E : CrossEdges L R) (w : R') :
    rightDegree (crossRelabel e f E) w = rightDegree E (f.symm w) := by
  simp only [rightDegree, crossRelabel_rightNeighbors, Finset.card_map]

omit [Fintype L] [Fintype L'] [Fintype R] [Fintype R'] in
theorem crossRelabel_inverse (e : L ≃ L') (f : R ≃ R') (E : CrossEdges L R) :
    crossRelabel e.symm f.symm (crossRelabel e f E) = E := by
  ext ⟨v, w⟩
  simp [crossRelabel]

theorem bipartite_relabel_mem (e : L ≃ L') (f : R ≃ R')
    (a : L → ℕ) (b : R → ℕ) (E : CrossEdges L R) :
    crossRelabel e f E ∈ bipartiteFamily (fun v => a (e.symm v)) (fun w => b (f.symm w)) ↔
      E ∈ bipartiteFamily a b := by
  change ((∀ v, leftDegree (crossRelabel e f E) v = _) ∧
    (∀ w, rightDegree (crossRelabel e f E) w = _)) ↔ _
  simp_rw [crossRelabel_leftDegree, crossRelabel_rightDegree]
  exact and_congr
    (e.symm.surjective.forall (p := fun v => leftDegree E v = a v)).symm
    (f.symm.surjective.forall (p := fun w => rightDegree E w = b w)).symm

theorem bipartiteCount_relabel (e : L ≃ L') (f : R ≃ R') (a : L → ℕ) (b : R → ℕ) :
    bipartiteCount (fun v => a (e.symm v)) (fun w => b (f.symm w)) = bipartiteCount a b := by
  symm
  apply Set.ncard_congr (fun E _ => crossRelabel e f E)
  · intro E hE
    exact (bipartite_relabel_mem e f a b E).mpr hE
  · intro E F _ _ h
    have hh := congrArg (crossRelabel e.symm f.symm) h
    simpa only [crossRelabel_inverse] using hh
  · intro E hE
    refine ⟨crossRelabel e.symm f.symm E, ?_, ?_⟩
    · have hh := (bipartite_relabel_mem e.symm f.symm
        (fun v => a (e.symm v)) (fun w => b (f.symm w)) E).mpr hE
      simpa only [Equiv.symm_symm, Equiv.symm_apply_apply] using hh
    · exact crossRelabel_inverse e.symm f.symm E

theorem uniformOn_map_equiv {A B : Type*} [Fintype A] [Fintype B]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSingletonClass A]
    [MeasurableSingletonClass B] (e : A ≃ B) (s : Set A) :
    (uniformOn s).map e = uniformOn (e '' s) := by
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply .of_discrete (measurableSet_singleton _), uniform_apply, uniform_apply]
  have he : e ⁻¹' {b} = {e.symm b} := by
    ext a
    exact e.eq_symm_apply.symm
  rw [he, Set.ncard_image_of_injective s e.injective]
  by_cases h : e.symm b ∈ s
  · have hb : b ∈ e '' s := ⟨e.symm b, h, e.apply_symm_apply b⟩
    rw [Set.inter_singleton_of_mem h, Set.inter_singleton_of_mem hb]
    simp
  · have hb : b ∉ e '' s := by simpa using h
    rw [Set.inter_singleton_eq_empty.mpr h, Set.inter_singleton_eq_empty.mpr hb]
    simp

theorem fixedDegreeLaw_relabel (e : V ≃ W) (d : V → ℕ) :
    (fixedDegreeLaw d).map e.simpleGraph = fixedDegreeLaw (fun w => d (e.symm w)) := by
  rw [fixedDegreeLaw, uniformOn_map_equiv]
  congr 1
  ext H
  obtain ⟨G, rfl⟩ := e.simpleGraph.surjective H
  rw [e.simpleGraph.injective.mem_set_image]
  exact (graph_relabel_mem e d G).symm

def crossRelabelEquiv (e : L ≃ L') (f : R ≃ R') : CrossEdges L R ≃ CrossEdges L' R' where
  toFun := crossRelabel e f
  invFun := crossRelabel e.symm f.symm
  left_inv := crossRelabel_inverse e f
  right_inv := crossRelabel_inverse e.symm f.symm

theorem bipartiteFixedDegreeLaw_relabel (e : L ≃ L') (f : R ≃ R') (a : L → ℕ) (b : R → ℕ) :
    (bipartiteFixedDegreeLaw a b).map (crossRelabel e f) =
      bipartiteFixedDegreeLaw (fun v => a (e.symm v)) (fun w => b (f.symm w)) := by
  change (uniformOn (bipartiteFamily a b)).map (crossRelabelEquiv e f) = _
  rw [uniformOn_map_equiv]
  congr 1
  ext E
  obtain ⟨F, rfl⟩ := (crossRelabelEquiv e f).surjective E
  rw [(crossRelabelEquiv e f).injective.mem_set_image]
  exact (bipartite_relabel_mem e f a b F).symm

end MajorityDynamics.Probability.NeighborhoodBulk
