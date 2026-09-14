import MajorityDynamics.GraphProcess.KernelEdgeSplitting.Counts
import MajorityDynamics.GraphProcess.KernelEdgeSplitting.Algebra
import MajorityDynamics.GraphProcess.KernelEdgeSplitting.Laws
import MajorityDynamics.GraphProcess.KernelEdgeSplitting.Inputs

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.KernelEdgeSplitting
open Universal BlockDecomposition KernelInputs
open MajorityDynamics.Probability.FixedDegreeEdgeConcentration
open MajorityDynamics.Probability.FixedDegreeSampling
variable {V : Type*} [Fintype V] {n : ℕ}

/-- The actual transition is the pushforward of its actual component sampler. -/
theorem K_real (σ : FineState.State V n) (A : Set (FineState.State V (n+1))) :
    (FineKernel.K σ).real A =
      (FineKernel.componentLaw σ).real {F | FineKernel.sampleNext σ F ∈ A} := by
  simp only [measureReal_def, FineKernel.K_apply]

/-- An ordered diagonal child count is twice the internal edge count, including
its center and threshold. -/
theorem internal_failure_le {θ T φ p U : ℝ} {y : Local.CoarseData V n}
    {σ : FineState.State V n} (h : Verified θ T φ p U y σ)
    (s : History (n+1)) (b : Bool)
    (hg : GraphConcentration (y.sizes s) (y.edge s s / 2).toNat p
      (fun v : Block σ.part s => (σ.deg v s).toNat)) :
    (FineKernel.K σ).real {τ | ¬ EdgeGood y p (2*T) σ τ s s b b} ≤
      1 / Real.log (y.sizes s : ℝ) := by
  rw [K_real]
  let A := {G : SimpleGraph (Block σ.part s) | edgeThreshold (y.sizes s) p ≤
    |(internalCount (childInBlock σ s b) G : ℝ) -
      (∑ v ∈ childInBlock σ s b, ((σ.deg v s).toNat : ℝ))^2 /
        (4*((y.edge s s / 2).toNat : ℝ))|}
  calc
    _ ≤ (FineKernel.componentLaw σ).real {F | internalSample σ s F ∈ A} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro F hF
      change ¬ EdgeGood y p (2*T) σ (FineKernel.sampleNext σ F) s s b b at hF
      unfold EdgeGood at hF
      rw [sampleNext_internal_count, internal_center] at hF
      have hs := h.doubled_edge_scale s
      change 2*edgeThreshold (y.sizes s) p ≤ _ at hs
      change edgeThreshold (y.sizes s) p ≤ _
      have he : |2 * (internalCount (childInBlock σ s b) (internalSample σ s F) : ℝ) -
          2 * (∑ v ∈ childInBlock σ s b, ((σ.deg v s).toNat : ℝ))^2 /
            (4*((y.edge s s / 2).toNat : ℝ))| =
          2 * |(internalCount (childInBlock σ s b) (internalSample σ s F) : ℝ) -
            (∑ v ∈ childInBlock σ s b, ((σ.deg v s).toNat : ℝ))^2 /
              (4*((y.edge s s / 2).toNat : ℝ))| := by
        rw [mul_div_assoc, ← mul_sub, abs_mul]
        norm_num
      rw [he] at hF
      linarith [lt_of_not_ge hF]
    _ = (fixedDegreeLaw (fun v : Block σ.part s => (σ.deg v s).toNat)).real A :=
      internalSample_real σ s A
    _ ≤ _ := (hg (childInBlock σ s b)).1.le

/-- Different Boolean children are complementary subsets of their parent. -/
theorem cut_failure_le {θ T φ p U : ℝ} {y : Local.CoarseData V n}
    {σ : FineState.State V n} (h : Verified θ T φ p U y σ) (hT : 1 < T)
    (s : History (n+1)) (b c : Bool) (hbc : b ≠ c)
    (hg : GraphConcentration (y.sizes s) (y.edge s s / 2).toNat p
      (fun v : Block σ.part s => (σ.deg v s).toNat)) :
    (FineKernel.K σ).real {τ | ¬ EdgeGood y p (2*T) σ τ s s b c} ≤
      1 / Real.log (y.sizes s : ℝ) := by
  rw [K_real]
  let A := {G : SimpleGraph (Block σ.part s) | edgeThreshold (y.sizes s) p ≤
    |(cutCount (childInBlock σ s b) G : ℝ) -
      (∑ v ∈ childInBlock σ s b, ((σ.deg v s).toNat : ℝ)) *
      (∑ v ∈ Finset.univ \ childInBlock σ s b, ((σ.deg v s).toNat : ℝ)) /
        (2*((y.edge s s / 2).toNat : ℝ))|}
  calc
    _ ≤ (FineKernel.componentLaw σ).real {F | internalSample σ s F ∈ A} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro F hF
      change ¬ EdgeGood y p (2*T) σ (FineKernel.sampleNext σ F) s s b c at hF
      unfold EdgeGood at hF
      rw [sampleNext_cut_count σ F p s b c hbc, cut_center y σ s b c hbc] at hF
      exact (verified_scale h hT s).trans (lt_of_not_ge hF).le
    _ = (fixedDegreeLaw (fun v : Block σ.part s => (σ.deg v s).toNat)).real A :=
      internalSample_real σ s A
    _ ≤ _ := by
      convert (hg (childInBlock σ s b)).2.le using 1
      · rfl
      · congr 1
        ext G
        simp only [A, Set.mem_ofPred_eq]
        congr! 8


/-- Different parents use the actual bipartite rectangle in either orientation. -/
theorem cross_failure_le {θ T φ p U : ℝ} {y : Local.CoarseData V n}
    {σ : FineState.State V n} (h : Verified θ T φ p U y σ) (hT : 1 < T)
    (s t : History (n+1)) (hst : s ≠ t) (b c : Bool)
    (hb : BipartiteConcentration (y.sizes t) (y.edge s t).toNat p
      (fun v : Block σ.part s => (σ.deg v t).toNat)
      (fun w : Block σ.part t => (σ.deg w s).toNat)) :
    (FineKernel.K σ).real {τ | ¬ EdgeGood y p (2*T) σ τ s t b c} ≤
      1 / Real.log (y.sizes t : ℝ) := by
  rw [K_real]
  let A := {E : CrossEdges (Block σ.part s) (Block σ.part t) |
    edgeThreshold (y.sizes t) p ≤
    |(rectangleCount (childInBlock σ s b) (childInBlock σ t c) E : ℝ) -
      (∑ v ∈ childInBlock σ s b, ((σ.deg v t).toNat : ℝ)) *
      (∑ w ∈ childInBlock σ t c, ((σ.deg w s).toNat : ℝ)) /
        ((y.edge s t).toNat : ℝ)|}
  calc
    _ ≤ (FineKernel.componentLaw σ).real {F | crossSample σ s t F ∈ A} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro F hF
      change ¬ EdgeGood y p (2*T) σ (FineKernel.sampleNext σ F) s t b c at hF
      unfold EdgeGood at hF
      rw [sampleNext_rectangle_count, cross_center] at hF
      exact (verified_scale h hT t).trans (lt_of_not_ge hF).le
    _ = (bipartiteFixedDegreeLaw
        (fun v : Block σ.part s => (σ.deg v t).toNat)
        (fun w : Block σ.part t => (σ.deg w s).toNat)).real A :=
      crossSample_real σ s t hst A
    _ ≤ _ := (hb (childInBlock σ s b) (childInBlock σ t c)).le

/-- All three literal edge-count cases share the same global per-pair bound. -/
theorem pair_failure_le {θ T φ p U : ℝ} {y : Local.CoarseData V n}
    {σ : FineState.State V n} (h : Verified θ T φ p U y σ) (hT : 1 < T)
    (_hρ : CoarseKernel.rho p σ = y) (N : ℕ)
    (hg : ∀ s, GraphConcentration (y.sizes s) (y.edge s s / 2).toNat p
      (fun v : Block σ.part s => (σ.deg v s).toNat))
    (hb : ∀ s t, BipartiteConcentration (y.sizes t) (y.edge s t).toNat p
      (fun v : Block σ.part s => (σ.deg v t).toNat)
      (fun w : Block σ.part t => (σ.deg w s).toNat))
    (hl : ∀ s, 1 / Real.log (y.sizes s : ℝ) ≤ 2 / Real.log N)
    (s t : History (n+1)) (b c : Bool) :
    (FineKernel.K σ).real {τ | ¬ EdgeGood y p (2*T) σ τ s t b c} ≤
      2 / Real.log N := by
  by_cases hst : s = t
  · subst t
    by_cases hbc : b = c
    · subst c
      exact (internal_failure_le h s b (hg s)).trans (hl s)
    · exact (cut_failure_le h hT s b c hbc (hg s)).trans (hl s)
  · exact (cross_failure_le h hT s t hst b c (hb s t)).trans (hl t)

end MajorityDynamics.GraphProcess.KernelEdgeSplitting
