import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations
import MajorityDynamics.Analysis.GaussianRegularity.Basic

/-!
# Compact regularity of normalized moments

The algebraic last step of Lemma E.2: raw moments and positive event mass
that are locally Lipschitz on a parameter domain give Lipschitz conditional moments
and covariances on every compact parameter set. The compact set need not
be convex. No probability or regularity hypotheses are installed as axioms.
-/

noncomputable section

namespace MajorityDynamics.Analysis.GaussianRegularity

variable {E : Type*} [NormedAddCommGroup E]

/-- Smooth scalar operations preserve local Lipschitz regularity. -/
theorem locallyLipschitzOn_binary {U : Set E} {f g : E → ℝ}
    (hf : LocallyLipschitzOn U f) (hg : LocallyLipschitzOn U g)
    (H : ℝ × ℝ → ℝ) (hH : ∀ x ∈ U, ContDiffAt ℝ 1 H (f x, g x)) :
    LocallyLipschitzOn U (fun x => H (f x, g x)) := by
  intro x hx
  obtain ⟨Kf, V, hV, hfV⟩ := hf hx
  obtain ⟨Kg, W, hW, hgW⟩ := hg hx
  obtain ⟨KH, Q, hQ, hHQ⟩ := (hH x hx).exists_lipschitzOnWith
  have hp := (hf.continuousOn x hx).prodMk (hg.continuousOn x hx)
  refine ⟨KH * max Kf Kg, (V ∩ W) ∩ (fun x => (f x, g x)) ⁻¹' Q,
    Filter.inter_mem (Filter.inter_mem hV hW) (hp hQ), ?_⟩
  exact hHQ.comp
    (((hfV.mono Set.inter_subset_left).prodMk (hgW.mono Set.inter_subset_right)).mono
      Set.inter_subset_left)
    ((Set.mapsTo_preimage _ _).mono_left Set.inter_subset_right)

theorem locallyLipschitzOn_normalized {U : Set E} {mass raw : E → ℝ}
    (hmass : LocallyLipschitzOn U mass) (hraw : LocallyLipschitzOn U raw)
    (hpos : ∀ x ∈ U, 0 < mass x) :
    LocallyLipschitzOn U (fun x => raw x / mass x) :=
  locallyLipschitzOn_binary hraw hmass (fun z => z.1 / z.2)
    (fun x hx => contDiffAt_fst.div contDiffAt_snd (hpos x hx).ne')

theorem locallyLipschitzOn_normalized_covariance {U : Set E}
    {mass first left second : E → ℝ}
    (hmass : LocallyLipschitzOn U mass) (hfirst : LocallyLipschitzOn U first)
    (hleft : LocallyLipschitzOn U left) (hsecond : LocallyLipschitzOn U second)
    (hpos : ∀ x ∈ U, 0 < mass x) :
    LocallyLipschitzOn U
      (fun x => second x / mass x - (first x / mass x) * (left x / mass x)) := by
  have hprod := locallyLipschitzOn_binary
    (locallyLipschitzOn_normalized hmass hfirst hpos)
    (locallyLipschitzOn_normalized hmass hleft hpos) (fun z => z.1 * z.2)
    (fun _ _ => contDiffAt_fst.mul contDiffAt_snd)
  exact locallyLipschitzOn_binary (locallyLipschitzOn_normalized hmass hsecond hpos)
    hprod (fun z => z.1 - z.2) (fun _ _ => contDiffAt_fst.sub contDiffAt_snd)

theorem compact_lipschitz_finite_of_locallyLipschitz {ι : Type*} [Fintype ι]
    {U P : Set E} (hP : IsCompact P) (hPU : P ⊆ U) (f : ι → E → ℝ)
    (hf : ∀ i, LocallyLipschitzOn U (f i)) :
    ∃ K, ∀ i, LipschitzOnWith K (f i) P := by
  classical
  choose K hK using fun i =>
    ((hf i).mono hPU).exists_lipschitzOnWith_of_compact hP
  exact ⟨Finset.univ.sup K, fun i => (hK i).weaken
    (Finset.le_sup (f := K) (Finset.mem_univ i))⟩

/-- Assemble the exact E.2 regularity conclusion from positive mass and the
three locally Lipschitz raw Gaussian moment families. Compact sets are arbitrary. -/
theorem regularOn_of_locallyLipschitz {d r : ℕ} (M : Matrix (Fin r) (Fin d) ℝ)
    {U P : Set (Parameters d r)} (hP : IsCompact P) (hPU : P ⊆ U)
    (hlower : ∃ c : ℝ, 0 < c ∧ ∀ p ∈ P, c ≤ mass M p)
    (hpos : ∀ p ∈ U, 0 < mass M p)
    (hmass : LocallyLipschitzOn U (mass M))
    (hfirst : ∀ t, LocallyLipschitzOn U (firstMoment M t))
    (hsecond : ∀ t t', LocallyLipschitzOn U (secondMoment M t t')) : RegularOn M P := by
  obtain ⟨K₀, hK₀⟩ := (hmass.mono hPU).exists_lipschitzOnWith_of_compact hP
  obtain ⟨K₁, hK₁⟩ := compact_lipschitz_finite_of_locallyLipschitz hP hPU _ hfirst
  obtain ⟨K₂, hK₂⟩ := compact_lipschitz_finite_of_locallyLipschitz hP hPU
    (fun tt : Fin d × Fin d => secondMoment M tt.1 tt.2)
    (fun tt => hsecond tt.1 tt.2)
  obtain ⟨K₃, hK₃⟩ := compact_lipschitz_finite_of_locallyLipschitz hP hPU
    (conditionalFirst M) (fun t => locallyLipschitzOn_normalized hmass (hfirst t) hpos)
  obtain ⟨K₄, hK₄⟩ := compact_lipschitz_finite_of_locallyLipschitz hP hPU
    (fun tt : Fin d × Fin d => conditionalSecond M tt.1 tt.2)
    (fun tt => locallyLipschitzOn_normalized hmass (hsecond tt.1 tt.2) hpos)
  obtain ⟨K₅, hK₅⟩ := compact_lipschitz_finite_of_locallyLipschitz hP hPU
    (fun tt : Fin d × Fin d => conditionalCovariance M tt.1 tt.2)
    (fun tt => locallyLipschitzOn_normalized_covariance hmass (hfirst tt.1)
      (hfirst tt.2) (hsecond tt.1 tt.2) hpos)
  classical
  refine ⟨hlower, ({K₀, K₁, K₂, K₃, K₄, K₅} : Finset NNReal).sup id, hK₀.weaken (Finset.le_sup (f := id) (by simp)),
    fun t => (hK₁ t).weaken (Finset.le_sup (f := id) (by simp)),
    fun t t' => (hK₂ (t, t')).weaken (Finset.le_sup (f := id) (by simp)),
    fun t => (hK₃ t).weaken (Finset.le_sup (f := id) (by simp)),
    fun t t' => (hK₄ (t, t')).weaken (Finset.le_sup (f := id) (by simp)),
    fun t t' => (hK₅ (t, t')).weaken (Finset.le_sup (f := id) (by simp))⟩

end MajorityDynamics.Analysis.GaussianRegularity
