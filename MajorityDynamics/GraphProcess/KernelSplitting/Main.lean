import MajorityDynamics.GraphProcess.KernelSplitting.Applications
import MajorityDynamics.GraphProcess.KernelSplitting.Laws
import MajorityDynamics.GraphProcess.KernelSplitting.Union
import MajorityDynamics.GraphProcess.KernelEdgeSplitting.Main

/-! The complete original-input kernel-splitting proposition (S1, S2 and S3). -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.KernelSplitting
open Universal BlockDecomposition FineKernel KernelInputs
open MajorityDynamics.Probability.NeighborhoodTail
open MajorityDynamics.Combinatorics.DegreeRatios
universe u

/-- Every actual next-degree point outside the regularity window inherits the
same C.2 stretched exponential, including both cross orientations. -/
theorem sampled_point_tail {V : Type u} [Fintype V] {n : ℕ}
    {θ T φ p U c : ℝ} {y : Local.CoarseData V n} {σ : FineState.State V n}
    (h : Verified θ T φ p U y σ) (hρ : CoarseKernel.rho p σ = y) (hc : 0 < c)
    (hg : ∀ s, GraphCarrierConclusion c U (Block σ.part s) p)
    (hb : ∀ s t, BipartiteCarrierConclusion c U (Block σ.part s) (Block σ.part t) p)
    (v : V) (t : History (n+1)) (b : Bool) (a : ℤ)
    (ha : 0 ≤ a) (had : a ≤ σ.deg v t)
    (hbad : (p*Fintype.card V)^((4:ℝ)/7) < |(a:ℝ)-p*(child σ t b).card|) :
    (componentLaw σ).real {F | (sampleNext σ F).deg v (append t b) = a} ≤
      Real.exp (-c*(p*Fintype.card V)^((1:ℝ)/7)) := by
  let x : Block σ.part (σ.part v) := ⟨v,rfl⟩
  by_cases hst : σ.part v = t
  · subst t
    change (componentLaw σ).real {F | (sampleNext σ F).deg x (append (σ.part v) b) = a} ≤ _
    rw [internal_degree_real σ (σ.part v) x b a]
    exact internal_point_tail h hρ hc (σ.part v) (hg _) x b a ha had hbad
  · change (componentLaw σ).real {F | (sampleNext σ F).deg x (append t b) = a} ≤ _
    rw [cross_degree_real σ (σ.part v) t hst x b a]
    exact bipartite_point_tail h hρ hc (σ.part v) t (hb _ _) x b a ha had hbad

/-- S2 has uniformly superpolynomially small failure probability from original
local admissibility, rho-fiber equality and R1/R2 only. The threshold precedes
all varying carriers, densities, coarse data, tilts and actual fine states. -/
theorem uniform_regularity_failure {θ T φ Cf A : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) (hCf : 0 ≤ Cf) (hA : 0 < A) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      Local.Admissible y q T φ p → ∀ σ : FineState.State V n,
      CoarseKernel.rho p σ = y → DegreeTypical y p σ → SizeTypical y q Cf σ →
      (K σ).real {τ | ¬ CoarseKernel.Regular p τ.part τ.deg} ≤ (N:ℝ)^(-A) := by
  obtain ⟨U,hU,N₁,h₁⟩ := uniform_inputs.{u} n hθlo hθhi hT hφ hφ1 hCf
  obtain ⟨c,r₀,hc,_hr₀,hg,hb⟩ := carrier_neighborhood_tail.{u,u,u} θ U hθlo hθhi hU
  obtain ⟨N₂,h₂⟩ := KernelEdgeSplitting.Numerics.uniform_block_log hT r₀
  obtain ⟨N₃,h₃⟩ := Numerics.union_absorption n hθlo hθhi hT hc hA
  refine ⟨max (max N₁ N₂) N₃,?_⟩
  intro N hN V inst hcard p hlo hhi y q hLA σ hρ hR1 hR2
  have hn1 := ((le_max_left N₁ N₂).trans (le_max_left (max N₁ N₂) N₃)).trans hN
  have hn2 := ((le_max_right N₁ N₂).trans (le_max_left (max N₁ N₂) N₃)).trans hN
  have hn3 := (le_max_right (max N₁ N₂) N₃).trans hN
  have h := h₁ N hn1 V hcard p hlo hhi y q hLA σ hρ hR1 hR2
  have hs (s : History (n+1)) : r₀ ≤ Fintype.card (Block σ.part s) := by
    rw [block_card hρ]
    exact (h₂ N hn2 (y.sizes s)
      (by simpa only [hcard] using (h.parent_sizes s).1)
      (by simpa only [hcard] using (h.parent_sizes s).2.1)).1
  have hd (s : History (n+1)) : DensityWindow θ U (Fintype.card (Block σ.part s)) p := by
    simpa only [DensityWindow, block_card hρ] using h.density s
  have hg' (s : History (n+1)) : GraphCarrierConclusion c U (Block σ.part s) p :=
    (hg (Block σ.part s) (hs s) p (hd s)).2.2
  have hb' (s t : History (n+1)) :
      BipartiteCarrierConclusion c U (Block σ.part s) (Block σ.part t) p :=
    (hb (Block σ.part s) (Block σ.part t) (hs t) p (hd t)).2.2
  have hp := K_regularity_failure_le σ p
    (Real.exp (-c*(p*Fintype.card V)^((1:ℝ)/7))) (Real.exp_nonneg _)
    (sampled_point_tail h hρ hc hg' hb')
  rw [hcard] at hp
  exact hp.trans (h₃ N hn3 p hlo hhi)

/-- Complete kernel-splitting proposition: actual deterministic split, regularity,
and every ordered edge-mass split hold simultaneously with the exact constant 2T. -/
theorem kernel_splitting_estimates {θ T φ Cf A : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) (hCf : 0 ≤ Cf) (hA : 0 < A) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      Local.Admissible y q T φ p → ∀ σ : FineState.State V n,
      CoarseKernel.rho p σ = y → DegreeTypical y p σ → SizeTypical y q Cf σ →
      (K σ).real {τ | ¬ LocalTransition.KernelGood y p (2*T) σ τ} ≤
        (N:ℝ)^(-A) + KernelEdgeSplitting.unionError n N := by
  obtain ⟨N₁,h₁⟩ := uniform_regularity_failure.{u} n hθlo hθhi hT hφ hφ1 hCf hA
  obtain ⟨N₂,h₂⟩ := KernelEdgeSplitting.uniform_kernelGood_failure.{u}
    n hθlo hθhi hT hφ hφ1 hCf
  refine ⟨max N₁ N₂,?_⟩
  intro N hN V inst hcard p hlo hhi y q hLA σ hρ hR1 hR2
  exact h₂ N ((le_max_right _ _).trans hN) V hcard p hlo hhi y q hLA σ hρ hR1 hR2
    ((N:ℝ)^(-A))
    (h₁ N ((le_max_left _ _).trans hN) V hcard p hlo hhi y q hLA σ hρ hR1 hR2)

/-- Uniform 1-o(1) form of the complete kernel proposition. -/
theorem kernel_splitting_estimates_epsilon {θ T φ Cf ε : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) (hCf : 0 ≤ Cf) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      Local.Admissible y q T φ p → ∀ σ : FineState.State V n,
      CoarseKernel.rho p σ = y → DegreeTypical y p σ → SizeTypical y q Cf σ →
      (K σ).real {τ | ¬ LocalTransition.KernelGood y p (2*T) σ τ} ≤ ε := by
  obtain ⟨N₁,h₁⟩ := kernel_splitting_estimates.{u} (A:=1)
    n hθlo hθhi hT hφ hφ1 hCf zero_lt_one
  obtain ⟨N₂,h₂⟩ := KernelEdgeSplitting.Numerics.eventually_unionError_lt n
    (show 0 < ε/2 by positivity)
  have hn : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun N : ℕ => (N:ℝ)^(-(1:ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop zero_lt_one).comp hn
  obtain ⟨N₃,h₃⟩ := eventually_atTop.mp
    (ht.eventually (eventually_lt_nhds (show 0 < ε/2 by positivity)))
  refine ⟨max (max N₁ N₂) N₃,?_⟩
  intro N hN V inst hcard p hlo hhi y q hLA σ hρ hR1 hR2
  have hn1 := ((le_max_left N₁ N₂).trans (le_max_left (max N₁ N₂) N₃)).trans hN
  have hn2 := ((le_max_right N₁ N₂).trans (le_max_left (max N₁ N₂) N₃)).trans hN
  have hn3 := (le_max_right (max N₁ N₂) N₃).trans hN
  exact (h₁ N hn1 V hcard p hlo hhi y q hLA σ hρ hR1 hR2).trans
    (by linarith [h₂ N hn2,h₃ N hn3])

/-- Direct adapter to the full typicality predicate used by LocalTransition.
Only its R1/R2 projections are used; no R3 input enters the primary proposition. -/
theorem typical_kernel_splitting_estimates {θ T φ Cf A : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) (hCf : 0 ≤ Cf) (hA : 0 < A) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      Local.Admissible y q T φ p → ∀ σ : FineState.State V n,
      CoarseKernel.rho p σ = y → LocalTransition.FiberTypical y q p Cf σ →
      (K σ).real {τ | ¬ LocalTransition.KernelGood y p (2*T) σ τ} ≤
        (N:ℝ)^(-A) + KernelEdgeSplitting.unionError n N := by
  obtain ⟨N₀,h₀⟩ := kernel_splitting_estimates.{u} n hθlo hθhi hT hφ hφ1 hCf hA
  refine ⟨N₀,?_⟩
  intro N hN V inst hcard p hlo hhi y q hLA σ hρ htyp
  exact h₀ N hN V hcard p hlo hhi y q hLA σ hρ htyp.1 htyp.2.1

/-- Epsilon adapter in precisely the FiberTypical form consumed by the local
transition assembly. The remaining statistical obligation there is fiber-side. -/
theorem typical_kernel_splitting_epsilon {θ T φ Cf ε : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) (hCf : 0 ≤ Cf) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      Local.Admissible y q T φ p → ∀ σ : FineState.State V n,
      CoarseKernel.rho p σ = y → LocalTransition.FiberTypical y q p Cf σ →
      (K σ).real {τ | ¬ LocalTransition.KernelGood y p (2*T) σ τ} ≤ ε := by
  obtain ⟨N₀,h₀⟩ := kernel_splitting_estimates_epsilon.{u} n hθlo hθhi hT hφ hφ1 hCf hε
  refine ⟨N₀,?_⟩
  intro N hN V inst hcard p hlo hhi y q hLA σ hρ htyp
  exact h₀ N hN V hcard p hlo hhi y q hLA σ hρ htyp.1 htyp.2.1

/-- Literal manuscript input form. Current regularity is derived from R1;
only partition equality and the prescribed ordered edge totals are assumed. -/
theorem manuscript_kernel_splitting_epsilon {θ T φ Cf ε : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) (hCf : 0 ≤ Cf) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      Local.Admissible y q T φ p → ∀ σ : FineState.State V n,
      σ.part = y.part → History.edgeTotals σ.part σ.deg = y.edge →
      DegreeTypical y p σ → SizeTypical y q Cf σ →
      (K σ).real {τ | ¬ LocalTransition.KernelGood y p (2*T) σ τ} ≤ ε := by
  obtain ⟨N₁,h₁⟩ := kernel_splitting_estimates_epsilon.{u}
    n hθlo hθhi hT hφ hφ1 hCf hε
  obtain ⟨N₂,h₂⟩ := Numerics.uniform_regime (Cf:=Cf) hθlo hθhi hT hφ hφ1
  refine ⟨max N₁ N₂,?_⟩
  intro N hN V inst hcard p hlo hhi y q hLA σ hpart hedge hR1 hR2
  have hr := h₂ N ((le_max_right _ _).trans hN) p hlo hhi
  have hw := hr.degree_window (N:ℝ)
    (by apply (div_le_iff₀ (by linarith : 0 < T)).2; nlinarith [hr.N_pos]) le_rfl
  have hreg : CoarseKernel.Regular p σ.part σ.deg := by
    intro v t
    have hv := hR1 v t
    change |(σ.deg v t : ℝ) - p * (y.sizes t : ℝ)| ≤ _ at hv
    simpa only [hpart,hcard,Local.CoarseData.sizes] using hv.trans (by simpa only [hcard] using hw)
  have hρ : CoarseKernel.rho p σ = y :=
    CoarseKernel.coarse_ext hpart hedge
      ((CoarseKernel.flag_true p σ.part σ.deg).2 hreg |>.trans hLA.regularity.symm)
  exact h₁ N ((le_max_left _ _).trans hN) V hcard p hlo hhi y q hLA σ hρ hR1 hR2

end MajorityDynamics.GraphProcess.KernelSplitting
