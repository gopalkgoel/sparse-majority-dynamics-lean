import MajorityDynamics.Probability.NeighborhoodBulk.Main
import MajorityDynamics.Probability.NeighborhoodBulk.SparseCounts
import MajorityDynamics.Probability.NeighborhoodBulk.SparseProfiles
import MajorityDynamics.Combinatorics.DegreeRatios.Sparse

/-! Closed neighborhood bulk estimates for the actual fixed-degree laws
on the uniform sparse range, retaining the original error scale. -/
noncomputable section
open Filter
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodBulk
open FixedDegreeSampling
open MajorityDynamics.Combinatorics.DegreeRatios
open MajorityDynamics.Literature.DegreeEnumeration

def SparseGraphNeighborhoodBulkTheorem : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 3 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ p : ℝ, SparseDensityWindow θ T n p →
        0 < p ∧ p < 1 ∧ GraphConclusion C T n p

def SparseBipartiteNeighborhoodBulkTheorem : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 3 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ p : ℝ, SparseDensityWindow θ T n p →
        0 < p ∧ p < 1 ∧ BipartiteConclusion C T n p

def SparseNeighborhoodBulkTheorem : Prop :=
  ∀ θ T : ℝ, 1 / 2 < θ → θ < 1 → 1 < T →
    ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 3 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ p : ℝ, SparseDensityWindow θ T n p →
        0 < p ∧ p < 1 ∧ GraphConclusion C T n p ∧ BipartiteConclusion C T n p


theorem eventually_graph_input_nonempty_sparse (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ,
      MajorityDynamics.Combinatorics.DegreeRatios.SparseDensityWindow θ T n p →
        ∀ (m : ℤ) (d : Fin n → ℤ), GraphInput T n p m d →
          (MajorityDynamics.Probability.FixedDegreeSampling.graphFamily
            (fun i => (d i).toNat)).Nonempty := by
  filter_upwards [eventually_graph_count_control_sparse θ T hθlo hθhi hT] with n hn
  intro p hp m d hd
  have hc := (hn p hp m d hd).2.1
  exact (Set.ncard_pos (Set.toFinite _)).mp (by exact_mod_cast hc)


theorem eventually_bipartite_input_nonempty_sparse (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ,
      MajorityDynamics.Combinatorics.DegreeRatios.SparseDensityWindow θ T n p →
        ∀ (ell m : ℤ) (a : Fin ell.toNat → ℤ) (b : Fin n → ℤ),
          BipartiteInput T n p ell m a b →
            (MajorityDynamics.Probability.FixedDegreeSampling.bipartiteFamily
              (fun i => (a i).toNat) (fun j => (b j).toNat)).Nonempty := by
  filter_upwards [eventually_bipartite_count_control_sparse θ T hθlo hθhi hT] with n hn
  intro p hp ell m a b hd
  have hc := (hn p hp ell m a b hd).2.1
  exact (Set.ncard_pos (Set.toFinite _)).mp (by exact_mod_cast hc)


theorem graph_atom_bounds_sparse (θ T : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, SparseDensityWindow θ T n p →
      ∀ (m : ℤ) (d : Fin n → ℤ), GraphInput T n p m d →
        ∀ (v : Fin n) (R : Finset (Fin n)), v ∉ R → R.card = (d v).toNat →
          MultiplicativeBound C n
            ((fixedDegreeLaw (fun i => (d i).toNat)).real {G | G.neighborFinset v = R})
            (Real.exp (graphWeight p d v R) / ((n - 1).choose (d v).toNat : ℝ)) := by
  obtain ⟨C, N, hC, _, hratio⟩ := graph_degree_ratio_sparse θ T hθlo hθhi hT
  refine ⟨17427 + C + 32 * (T + 1), by linarith, ?_⟩
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop (3 : ℕ),
    eventually_sparse_large_parameters θ T hθlo hθhi hT,
    eventually_graph_count_control_sparse θ T hθlo hθhi hT,
    eventually_graph_residual_count_control_sparse θ T hθlo hθhi hT,
    eventually_graph_residual_source_sparse θ T hθlo hθhi hT,
    eventually_graph_profile_sparse θ T hθlo hθhi hT] with n hnN hn hl ho hr hs hpB
  intro p hp m d hd v R hv hR
  have hlarge := hl p hp
  have hx : 0 < p * n := mul_pos hlarge.2.2.1 (by exact_mod_cast (by omega : 0 < n))
  have hdwin : DegreeWindow n p (d v) :=
    (standardizedDegree_bound_iff p n (d v) (Real.log n) hx).mp (hd.2.2.2 v)
  have hc3 := hratio n hnN p hp m (d v) ⟨hd.2.2.1, hdwin⟩
  have hdo : ∀ i, (d i).toNat ≤ n - 1 := by intro i; have := hd.1 i; omega
  have hmn : (m.toNat : ℤ) = m := Int.toNat_of_nonneg (graph_input_nat_sum hd).1
  have hdn : ∀ i, ((d i).toNat : ℤ) = d i := fun i => Int.toNat_of_nonneg (hd.1 i).1
  have hdreal : ∀ i, ((d i).toNat : ℝ) = (d i : ℝ) := by intro i; exact_mod_cast hdn i
  have hmod := graph_model_ratio (m := m.toNat) (fun i => (d i).toNat) v R (by omega) hv hdo
    (hs p hp m d hd v R hv hR).1.2.2
  rw [hmn, hdn] at hmod
  simp only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one, hdreal] at hmod
  have horig := ho p hp m d hd
  have hres := hr p hp m d hd v R hv hR
  have hprof := hpB p hp m d hd v R hv hR
  have hchoose : 0 < ((n - 1).choose (d v).toNat : ℝ) := by
    exact_mod_cast Nat.choose_pos (hdo v)
  have hlog := count_ratio_log_control hres.2.1 horig.2.1 hres.1 horig.1 hres.2.2 horig.2.2
  have hbound := profile_ratio_log_control
    (z := (d v : ℝ) * Real.log p - p * n) (w := graphWeight p d v R)
    (D := C * Real.log n) (E := 32 * (T + 1) * Real.log n ^ 2) (div_pos hres.2.1 horig.2.1) hc3.2.1 hprof.1
    hchoose hmod hlog
    (by convert hc3.2.2 using 1; congr 1; ring)
    (by convert hprof.2 using 1; congr 1; ring)
  have he := bound_enlarge (le_of_lt (div_pos (Real.exp_pos _) hchoose))
    (log_error_enlarge hlarge.2.1 hC.le hT) hbound
  unfold MultiplicativeBound
  rw [graph_removal_real _ _ _ (hs p hp m d hd v R hv hR).1]
  rw [graphResidualFin_count] at he
  simp only [neg_mul]
  convert he using 1 <;> congr!

theorem bipartite_atom_bounds_sparse (θ T : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, SparseDensityWindow θ T n p →
      ∀ (ell m : ℤ) (a : Fin ell.toNat → ℤ) (b : Fin n → ℤ),
        BipartiteInput T n p ell m a b →
          ∀ (v : Fin ell.toNat) (R : Finset (Fin n)), R.card = (a v).toNat →
            MultiplicativeBound C n
              ((bipartiteFixedDegreeLaw (fun i => (a i).toNat) (fun j => (b j).toNat)).real
                {E | leftNeighbors E v = R})
              (Real.exp (bipartiteWeight p ell b R) / (n.choose (a v).toNat : ℝ)) := by
  obtain ⟨C, N, hC, _, hratio⟩ := bipartite_degree_ratio_sparse θ T hθlo hθhi hT
  refine ⟨17427 + C + 32 * (T + 1), by linarith, ?_⟩
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop (3 : ℕ),
    eventually_sparse_large_parameters θ T hθlo hθhi hT,
    eventually_bipartite_count_control_sparse θ T hθlo hθhi hT,
    eventually_bipartite_residual_count_control_sparse θ T hθlo hθhi hT,
    eventually_bipartite_residual_source_sparse θ T hθlo hθhi hT,
    eventually_bipartite_profile_sparse θ T hθlo hθhi hT] with n hnN hn hl ho hr hs hpB
  intro p hp ell m a b hd v R hR
  have hlarge := hl p hp
  have hx : 0 < p * n := mul_pos hlarge.2.2.1 (by exact_mod_cast (by omega : 0 < n))
  have hdwin : DegreeWindow n p (a v) :=
    (standardizedDegree_bound_iff p n (a v) (Real.log n) hx).mp (hd.2.2.2.2.2.2.2.1 v)
  have hc3 := hratio n hnN p hp ell m (a v)
    ⟨by simpa only [div_eq_mul_inv, mul_comm] using hd.1, hd.2.1, hd.2.2.2.2.2.2.1, hdwin⟩
  have ha : ∀ i, (a i).toNat ≤ n := by intro i; have := hd.2.2.1 i; omega
  have hb : ∀ j, (b j).toNat ≤ ell.toNat := by intro j; have := hd.2.2.2.1 j; omega
  have hmn : (m.toNat : ℤ) = m := Int.toNat_of_nonneg (bipartite_input_nat_sums hd).1
  have helln : (ell.toNat : ℤ) = ell := Int.toNat_of_nonneg (by have := hc3.1.1; omega)
  have han : ∀ i, ((a i).toNat : ℤ) = a i := fun i => Int.toNat_of_nonneg (hd.2.2.1 i).1
  have hbreal : ∀ j, ((b j).toNat : ℝ) = (b j : ℝ) := by
    intro j
    exact_mod_cast Int.toNat_of_nonneg (hd.2.2.2.1 j).1
  have hellreal : (ell.toNat : ℝ) = (ell : ℝ) := by exact_mod_cast helln
  have hmod := bipartite_model_ratio (m := m.toNat) (fun i => (a i).toNat)
    (fun j => (b j).toNat) v R (by have := hc3.1.1; omega) ha hb
    (hs p hp ell m a b hd v R hR).1.2
  rw [hmn, helln, han] at hmod
  simp only [hbreal, hellreal] at hmod
  have horig := ho p hp ell m a b hd
  have hres := hr p hp ell m a b hd v R hR
  have hprof := hpB p hp ell m a b hd v R hR
  have hchoose : 0 < (n.choose (a v).toNat : ℝ) := by exact_mod_cast Nat.choose_pos (ha v)
  have hlog := count_ratio_log_control hres.2.1 horig.2.1 hres.1 horig.1 hres.2.2 horig.2.2
  have hlog' : |Real.log ((bipartiteCount (leftResidualFin (fun i => (a i).toNat) v)
      (residualRightDegree (fun j => (b j).toNat) R) : ℝ) /
        bipartiteCount (fun i => (a i).toNat) (fun j => (b j).toNat)) -
      Real.log (bipartiteCountModel (m.toNat - (a v).toNat)
        (leftResidualFin (fun i => (a i).toNat) v) (residualRightDegree (fun j => (b j).toNat) R) /
        bipartiteCountModel m.toNat (fun i => (a i).toNat) (fun j => (b j).toNat))| ≤
      16400 * Real.log n ^ 4 + 1 + (1025 * Real.log n ^ 4 + 1) := by
    exact hlog.trans (by nlinarith [(by positivity : 0 ≤ Real.log n ^ 4)])
  have hbound := profile_ratio_log_control
    (z := (a v : ℝ) * Real.log p - p * n) (w := bipartiteWeight p ell b R)
    (D := C * Real.log n) (E := 32 * (T + 1) * Real.log n ^ 2)
    (div_pos hres.2.1 horig.2.1) hc3.2.1 hprof.1 hchoose hmod hlog'
    (by convert hc3.2.2 using 1; congr 1; ring)
    (by convert hprof.2 using 1; congr 1; ring)
  have he := bound_enlarge (le_of_lt (div_pos (Real.exp_pos _) hchoose))
    (log_error_enlarge hlarge.2.1 hC.le hT) hbound
  unfold MultiplicativeBound
  rw [bipartite_removal_real _ _ _ _ (hs p hp ell m a b hd v R hR).1]
  rw [bipartiteResidualFin_count] at he
  simp only [neg_mul]
  convert he using 1 <;> congr!


theorem graph_neighborhood_bulk_sparse : SparseGraphNeighborhoodBulkTheorem := by
  intro θ T hθlo hθhi hT
  obtain ⟨C, hC, hbound⟩ := graph_atom_bounds_sparse θ T hθlo hθhi hT
  have hev : ∀ᶠ n : ℕ in atTop, 3 ≤ n ∧ ∀ p : ℝ, SparseDensityWindow θ T n p →
      0 < p ∧ p < 1 ∧ GraphConclusion C T n p := by
    filter_upwards [eventually_ge_atTop (3 : ℕ), hbound,
      eventually_graph_probability_range_sparse θ T hθlo hθhi hT,
      eventually_graph_input_nonempty_sparse θ T hθlo hθhi hT] with n hn hb hp hnemp
    refine ⟨hn, ?_⟩
    intro p hw
    refine ⟨(hp p hw).1, (hp p hw).2, ?_⟩
    intro m d hd
    refine ⟨hnemp p hw m d hd, ?_⟩
    intro v S _ _ t ht htd
    rw [graph_event_sum d v S t ht htd, graph_comparison_sum]
    apply multiplicative_sum
    intro R₁ h₁ R₂ h₂
    obtain ⟨hs₁, hc₁⟩ := Finset.mem_powersetCard.mp h₁
    obtain ⟨hs₂, hc₂⟩ := Finset.mem_powersetCard.mp h₂
    apply hb p hw m d hd v (R₁ ∪ R₂)
    · intro hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact (Finset.mem_erase.mp (hs₁ hv)).1 rfl
      · exact (Finset.mem_sdiff.mp (hs₂ hv)).2 (Finset.mem_insert_self _ _)
    · have hdis := (graph_partition_disjoint v S).mono hs₁ hs₂
      rw [Finset.card_union_of_disjoint hdis, hc₁, hc₂]
      omega
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  exact ⟨C, N, hC, (hN N le_rfl).1, fun n hn => (hN n hn).2⟩

theorem bipartite_neighborhood_bulk_sparse : SparseBipartiteNeighborhoodBulkTheorem := by
  intro θ T hθlo hθhi hT
  obtain ⟨C, hC, hbound⟩ := bipartite_atom_bounds_sparse θ T hθlo hθhi hT
  have hev : ∀ᶠ n : ℕ in atTop, 3 ≤ n ∧ ∀ p : ℝ, SparseDensityWindow θ T n p →
      0 < p ∧ p < 1 ∧ BipartiteConclusion C T n p := by
    filter_upwards [eventually_ge_atTop (3 : ℕ), hbound,
      eventually_graph_probability_range_sparse θ T hθlo hθhi hT,
      eventually_bipartite_input_nonempty_sparse θ T hθlo hθhi hT] with n hn hb hp hnemp
    refine ⟨hn, ?_⟩
    intro p hw
    refine ⟨(hp p hw).1, (hp p hw).2, ?_⟩
    intro ell m a b hd
    refine ⟨hnemp p hw ell m a b hd, ?_⟩
    intro v S _ _ t ht htd
    rw [bipartite_event_sum a b v S t ht htd, bipartite_comparison_sum]
    apply multiplicative_sum
    intro R₁ h₁ R₂ h₂
    obtain ⟨hs₁, hc₁⟩ := Finset.mem_powersetCard.mp h₁
    obtain ⟨hs₂, hc₂⟩ := Finset.mem_powersetCard.mp h₂
    apply hb p hw ell m a b hd v (R₁ ∪ R₂)
    have hdis : Disjoint R₁ R₂ := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      exact (Finset.mem_sdiff.mp (hs₂ hj)).2 (hs₁ hi)
    rw [Finset.card_union_of_disjoint hdis, hc₁, hc₂]
    omega
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  exact ⟨C, N, hC, (hN N le_rfl).1, fun n hn => (hN n hn).2⟩


theorem neighborhood_bulk_sparse : SparseNeighborhoodBulkTheorem := by
  intro θ T hθlo hθhi hT
  obtain ⟨Cg, Ng, hCg, hNg, hg⟩ := graph_neighborhood_bulk_sparse θ T hθlo hθhi hT
  obtain ⟨Cb, Nb, _, _, hb⟩ := bipartite_neighborhood_bulk_sparse θ T hθlo hθhi hT
  refine ⟨max Cg Cb, max Ng Nb, hCg.trans_le (le_max_left _ _), hNg.trans (le_max_left _ _), ?_⟩
  intro n hn p hp
  have hgraph := hg n ((le_max_left _ _).trans hn) p hp
  have hbip := hb n ((le_max_right _ _).trans hn) p hp
  refine ⟨hgraph.1, hgraph.2.1, ?_, ?_⟩
  · intro m d hd
    obtain ⟨hne, he⟩ := hgraph.2.2 m d hd
    refine ⟨hne, ?_⟩
    intro v S hS hSc t ht htd
    exact (he v S hS hSc t ht htd).mono (graphComparison_nonneg p d v S t) (le_max_left _ _)
  · intro ell m a b hd
    obtain ⟨hne, he⟩ := hbip.2.2 ell m a b hd
    refine ⟨hne, ?_⟩
    intro v S hS hSc t ht htd
    exact (he v S hS hSc t ht htd).mono
      (bipartiteComparison_nonneg p ell b (a v) S t) (le_max_right _ _)

end MajorityDynamics.Probability.NeighborhoodBulk

