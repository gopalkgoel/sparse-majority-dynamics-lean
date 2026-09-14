import MajorityDynamics.Literature.DegreeEnumeration.Uniformity
import MajorityDynamics.Literature.DegreeEnumeration.Graph
import MajorityDynamics.Literature.DegreeEnumeration.Bipartite

/-! Uniform finite-family versions of the two source theorems. The source
growth conditions remain explicit obligations of applications. Uniformity
over edge totals is proved by finite maximization, not added to an axiom. -/
noncomputable section
open Filter
open scoped Classical
namespace MajorityDynamics.Literature.DegreeEnumeration

theorem graph_enumeration_uniform_finite :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧
      ∀ α : ℝ, 1 / 2 < α → α < 3 / 5 →
      ∀ s : ℕ → Finset ℕ, (∀ n, (s n).Nonempty) →
      (∀ᶠ n in atTop, ∀ m ∈ s n,
        m ≤ n.choose 2 ∧ graphDensity n m ≤ μ₀ ∧ 0 < graphErrorScale α n m) →
      (∀ m : ℕ → ℕ, (∀ n, m n ∈ s n) → ∀ K : ℝ, 0 < K →
        Asymptotics.IsLittleO atTop (fun n : ℕ => Real.log n ^ K / (n : ℝ))
          (fun n => graphDensity n (m n))) →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, ∀ m ∈ s n, ∀ d : Fin n → ℕ,
        GraphSourceData α n m d → RelativeApproximation (C * graphErrorScale α n m)
          ((graphDegreeLaw (Fin n) m).real {d})
          ((graphBinomialLaw (Fin n) m).real {d} * graphCorrection m d) := by
  obtain ⟨μ₀, hμ₀, hsource⟩ := liebenau_wormald_graph
  refine ⟨μ₀, hμ₀, ?_⟩
  intro α hαlo hαhi s hs hcap hgrowth
  let A : ℕ → Type := fun n => {m : ℕ // m ∈ s n} × (Fin n → Fin (n + 1))
  have : ∀ n, Fintype (A n) := fun n => by dsimp [A]; infer_instance
  have : ∀ n, Nonempty (A n) := by
    intro n
    obtain ⟨m, hm⟩ := hs n
    exact ⟨⟨⟨m, hm⟩, fun _ => ⟨0, by omega⟩⟩⟩
  let deg : ∀ n, A n → Fin n → ℕ := fun _ a i => (a.2 i).val
  let valid : ∀ n, A n → Prop := fun n a =>
    GraphSourceData α n a.1.val (deg n a) ∧ 0 < graphErrorScale α n a.1.val
  let E : ∀ n, A n → ℝ := fun n a => graphErrorScale α n a.1.val
  let P : ∀ n, A n → ℝ := fun n a => (graphDegreeLaw (Fin n) a.1.val).real {deg n a}
  let Q : ∀ n, A n → ℝ := fun n a =>
    (graphBinomialLaw (Fin n) a.1.val).real {deg n a} * graphCorrection a.1.val (deg n a)
  have hE : ∀ n a, valid n a → 0 < E n a := fun _ _ h => h.2
  have hQ : ∀ n a, valid n a → Q n a ≠ 0 := by
    intro n a h
    exact (mul_pos (graphBinomialLaw_atom_pos (deg n a) h.1.1 h.1.2.1)
      (Real.exp_pos _)).ne'
  have hseq : ∀ f : ∀ n, A n, ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      valid n (f n) → RelativeApproximation (C * E n (f n)) (P n (f n)) (Q n (f n)) := by
    intro f
    let m : ℕ → ℕ := fun n => (f n).1.val
    have hm : ∀ n, m n ∈ s n := fun n => (f n).1.property
    have hdom : ∀ᶠ n in atTop, m n ≤ n.choose 2 ∧ graphDensity n (m n) ≤ μ₀ := by
      filter_upwards [hcap] with n hn
      exact ⟨(hn (m n) (hm n)).1, (hn (m n) (hm n)).2.1⟩
    obtain ⟨C, hC, hc⟩ := hsource α hαlo hαhi m hdom (hgrowth m hm)
    refine ⟨C, hC, ?_⟩
    filter_upwards [hc] with n hn
    intro hv
    exact hn (deg n (f n)) hv.1
  obtain ⟨C, hC, hc⟩ := uniform_relativeApproximation_of_sequences valid E P Q hE hQ hseq
  refine ⟨C, hC, ?_⟩
  filter_upwards [hc, hcap] with n hn hdom
  intro m hm d hd
  let a : A n := (⟨m, hm⟩, fun i => ⟨d i, by have := hd.1 i; omega⟩)
  exact hn a ⟨hd, (hdom m hm).2.2⟩

theorem bipartite_enumeration_uniform_finite :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧
      ∀ α : ℝ, 1 / 2 < α → α < 3 / 5 →
      ∀ s : ℕ → Finset (ℕ × ℕ), (∀ n, (s n).Nonempty) →
      (∀ᶠ n in atTop, ∀ q ∈ s n, 0 < q.1 ∧ q.2 ≤ q.1 * n ∧
        bipartiteDensity q.1 n q.2 < μ₀ ∧ 0 < bipartiteErrorScale α q.1 n q.2) →
      (∀ ell m : ℕ → ℕ, (∀ n, (ell n, m n) ∈ s n) →
        Asymptotics.IsLittleO atTop
          (fun n => ((ell n : ℝ) + n) ^ (5 - 5 * α))
          (fun n => (ell n : ℝ) * n * (m n : ℝ) ^ (3 - 5 * α)) ∧
        ∀ K : ℝ, 0 < K → Asymptotics.IsLittleO atTop
          (fun n => (ell n : ℝ) * Real.log n ^ K + (n : ℝ) * Real.log (ell n) ^ K)
          (fun n => (m n : ℝ))) →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, ∀ q ∈ s n,
        ∀ (a : Fin q.1 → ℕ) (b : Fin n → ℕ), BipartiteSourceData α q.1 n q.2 a b →
          RelativeApproximation (C * bipartiteErrorScale α q.1 n q.2)
            ((bipartiteDegreeLaw (Fin q.1) (Fin n) q.2).real {(a, b)})
            ((bipartiteBinomialLaw (Fin q.1) (Fin n) q.2).real {(a, b)} *
              bipartiteCorrection q.2 a b) := by
  obtain ⟨μ₀, hμ₀, hsource⟩ := liebenau_wormald_bipartite
  refine ⟨μ₀, hμ₀, ?_⟩
  intro α hαlo hαhi s hs hcap hgrowth
  let A : ℕ → Type := fun n => Σ q : {q : ℕ × ℕ // q ∈ s n},
    (Fin q.val.1 → Fin (n + 1)) × (Fin n → Fin (q.val.1 + 1))
  have : ∀ n, Fintype (A n) := fun n => by dsimp [A]; infer_instance
  have : ∀ n, Nonempty (A n) := by
    intro n
    obtain ⟨q, hq⟩ := hs n
    exact ⟨⟨⟨q, hq⟩, (fun _ => ⟨0, by omega⟩), (fun _ => ⟨0, by omega⟩)⟩⟩
  let left : ∀ n, (u : A n) → Fin u.1.val.1 → ℕ := fun _ u i => (u.2.1 i).val
  let right : ∀ n, A n → Fin n → ℕ := fun _ u j => (u.2.2 j).val
  let valid : ∀ n, A n → Prop := fun n u =>
    BipartiteSourceData α u.1.val.1 n u.1.val.2 (left n u) (right n u) ∧
      0 < bipartiteErrorScale α u.1.val.1 n u.1.val.2
  let E : ∀ n, A n → ℝ := fun n u => bipartiteErrorScale α u.1.val.1 n u.1.val.2
  let P : ∀ n, A n → ℝ := fun n u =>
    (bipartiteDegreeLaw (Fin u.1.val.1) (Fin n) u.1.val.2).real {(left n u, right n u)}
  let Q : ∀ n, A n → ℝ := fun n u =>
    (bipartiteBinomialLaw (Fin u.1.val.1) (Fin n) u.1.val.2).real {(left n u, right n u)} *
      bipartiteCorrection u.1.val.2 (left n u) (right n u)
  have hE : ∀ n u, valid n u → 0 < E n u := fun _ _ h => h.2
  have hQ : ∀ n u, valid n u → Q n u ≠ 0 := by
    intro n u h
    exact (mul_pos (bipartiteBinomialLaw_atom_pos (left n u) (right n u)
      h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1) (Real.exp_pos _)).ne'
  have hseq : ∀ f : ∀ n, A n, ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      valid n (f n) → RelativeApproximation (C * E n (f n)) (P n (f n)) (Q n (f n)) := by
    intro f
    let ell : ℕ → ℕ := fun n => (f n).1.val.1
    let m : ℕ → ℕ := fun n => (f n).1.val.2
    have hm : ∀ n, (ell n, m n) ∈ s n := fun n => (f n).1.property
    have hdom : ∀ᶠ n in atTop, 0 < ell n ∧ m n ≤ ell n * n ∧
        bipartiteDensity (ell n) n (m n) < μ₀ := by
      filter_upwards [hcap] with n hn
      exact ⟨(hn _ (hm n)).1, (hn _ (hm n)).2.1, (hn _ (hm n)).2.2.1⟩
    obtain ⟨C, hC, hc⟩ := hsource α hαlo hαhi ell m hdom
      (hgrowth ell m hm).1 (hgrowth ell m hm).2
    refine ⟨C, hC, ?_⟩
    filter_upwards [hc] with n hn
    intro hv
    exact hn (left n (f n)) (right n (f n)) hv.1
  obtain ⟨C, hC, hc⟩ := uniform_relativeApproximation_of_sequences valid E P Q hE hQ hseq
  refine ⟨C, hC, ?_⟩
  filter_upwards [hc, hcap] with n hn hdom
  intro q hq a b hd
  let u : A n := ⟨⟨q, hq⟩, (fun i => ⟨a i, by have := hd.1 i; omega⟩),
    (fun j => ⟨b j, by change b j < q.1 + 1; have := hd.2.1 j; omega⟩)⟩
  exact hn u ⟨hd, (hdom q hq).2.2.2⟩

end MajorityDynamics.Literature.DegreeEnumeration
