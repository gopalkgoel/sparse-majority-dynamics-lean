import MajorityDynamics.Literature.EdgeProbabilities.Source
import MajorityDynamics.Literature.EdgeProbabilities.Uniformity

/-! Uniform finite source-formula bounds, proved from the sequence-level imports.
These are application interfaces, not additional axioms or original-window conclusions. -/
noncomputable section
open MeasureTheory Filter
open scoped Classical Topology
namespace MajorityDynamics.Literature.EdgeProbabilities
open MajorityDynamics.Probability.FixedDegreeSampling
universe u v w

/-- Uniform source error over any collection of graph test data whose every divergent
sequence satisfies the source conditions. The constant and threshold precede all test data,
including the degree vector and the queried pair. -/
theorem graph_uniform_source_error {X : Type w}
    (n m : X → ℕ) (V : X → Type u) [∀ x, Fintype (V x)]
    (d : (x : X) → V x → ℕ) (a b : (x : X) → V x)
    (Valid : X → Prop) (α : ℝ) (hαlo : 1 / 2 < α) (hαhi : α < 3 / 5)
    (hsequence : ∀ x : ℕ → X, (∀ k, Valid (x k)) →
      Tendsto (fun k => n (x k)) atTop atTop →
      Tendsto (fun k => graphDensity (n (x k)) (m (x k))) atTop (𝓝 0) ∧
      (∀ K : ℝ, 0 < K → Asymptotics.IsLittleO atTop
        (fun k => (Real.log (n (x k))) ^ K / (n (x k) : ℝ))
        (fun k => graphDensity (n (x k)) (m (x k)))) ∧
      ∀ᶠ k in atTop, GraphConditions (n (x k)) (m (x k)) α (d (x k)) ∧
        a (x k) ≠ b (x k)) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ x, N₀ ≤ n x → Valid x →
      |(fixedDegreeLaw (d x)).real {G | G.Adj (a x) (b x)} -
        graphApproximation (n x) (m x) (d x (a x)) (d x (b x))| ≤
          C * graphErrorScale (n x) (m x) := by
  apply uniform_bound_of_sequence_bound n Valid
    (fun x => |(fixedDegreeLaw (d x)).real {G | G.Adj (a x) (b x)} -
      graphApproximation (n x) (m x) (d x (a x)) (d x (b x))|)
    (fun x => graphErrorScale (n x) (m x))
  · intro x _
    unfold graphErrorScale graphAverage
    positivity
  · intro x hx hn
    obtain ⟨μ₀, hμ₀, hsource⟩ := graph_edge_probability.{u}
    obtain ⟨hdensity, hlogs, hconditions⟩ := hsequence x hx hn
    obtain ⟨C, hC, hevent⟩ := hsource α hαlo hαhi
      (fun k => n (x k)) (fun k => m (x k)) hn
      (hdensity.eventually_le_const hμ₀) hlogs
    refine ⟨C, hC, ?_⟩
    filter_upwards [hevent, hconditions] with k hk hc
    exact hk (V (x k)) (d (x k)) hc.1 (a (x k)) (b (x k)) hc.2

/-- Bipartite counterpart, preserving the prefactor outside the bracket error.
The collection may include different left and right cardinalities and carriers. -/
theorem bipartite_uniform_source_error {X : Type w}
    (ell n m : X → ℕ) (L : X → Type u) (R : X → Type v)
    [∀ x, Fintype (L x)] [∀ x, Fintype (R x)]
    (a : (x : X) → L x → ℕ) (b : (x : X) → R x → ℕ)
    (i : (x : X) → L x) (j : (x : X) → R x)
    (Valid : X → Prop) (α : ℝ) (hαlo : 1 / 2 < α) (hαhi : α < 3 / 5)
    (hsequence : ∀ x : ℕ → X, (∀ k, Valid (x k)) →
      Tendsto (fun k => n (x k)) atTop atTop →
      Tendsto (fun k => ell (x k)) atTop atTop ∧
      Tendsto (fun k => bipartiteDensity (ell (x k)) (n (x k)) (m (x k)))
        atTop (𝓝 0) ∧
      Asymptotics.IsLittleO atTop
        (fun k => ((ell (x k) : ℝ) + n (x k)) ^ (5 - 5 * α))
        (fun k => (ell (x k) : ℝ) * n (x k) * (m (x k) : ℝ) ^ (3 - 5 * α)) ∧
      (∀ K : ℝ, 0 < K → Asymptotics.IsLittleO atTop
        (fun k => (ell (x k) : ℝ) * (Real.log (n (x k))) ^ K +
          (n (x k) : ℝ) * (Real.log (ell (x k))) ^ K)
        (fun k => (m (x k) : ℝ))) ∧
      ∀ᶠ k in atTop, BipartiteConditions (ell (x k)) (n (x k)) (m (x k)) α
        (a (x k)) (b (x k))) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ x, N₀ ≤ n x → Valid x →
      |(bipartiteFixedDegreeLaw (a x) (b x)).real {E | (i x, j x) ∈ E} -
        bipartiteApproximation (ell x) (n x) (m x) (a x) (b x) (i x) (j x)| ≤
          C * (bipartitePrefactor (m x) (a x (i x)) (b x (j x)) *
            bipartiteErrorScale (ell x) (n x) (m x) α) := by
  apply uniform_bound_of_sequence_bound n Valid
    (fun x => |(bipartiteFixedDegreeLaw (a x) (b x)).real {E | (i x, j x) ∈ E} -
      bipartiteApproximation (ell x) (n x) (m x) (a x) (b x) (i x) (j x)|)
    (fun x => bipartitePrefactor (m x) (a x (i x)) (b x (j x)) *
      bipartiteErrorScale (ell x) (n x) (m x) α)
  · intro x _
    unfold bipartitePrefactor bipartiteErrorScale leftAverage rightAverage
    positivity
  · intro x hx hn
    obtain ⟨μ₀, hμ₀, hsource⟩ := bipartite_edge_probability.{u, v}
    obtain ⟨hell, hdensity, hpowers, hlogs, hconditions⟩ := hsequence x hx hn
    obtain ⟨C, hC, hevent⟩ := hsource α hαlo hαhi
      (fun k => ell (x k)) (fun k => n (x k)) (fun k => m (x k)) hn hell
      (hdensity.eventually_lt_const hμ₀) hpowers hlogs
    refine ⟨C, hC, ?_⟩
    filter_upwards [hevent, hconditions] with k hk hc
    simpa only [mul_left_comm] using
      hk (L (x k)) (R (x k)) (a (x k)) (b (x k)) hc (i (x k)) (j (x k))

end MajorityDynamics.Literature.EdgeProbabilities
