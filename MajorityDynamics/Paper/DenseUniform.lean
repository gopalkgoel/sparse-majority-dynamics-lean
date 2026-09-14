import MajorityDynamics.Literature.FKMAdapters.FixedInitial
import MajorityDynamics.Literature.FKMAdapters.GraphLaw
import MajorityDynamics.Paper.UniformCleanup

/-! Translation of the independently checked FKM fixed-coloring estimates to
the paper's Boolean convention, exact initial floors and actual graph law. -/
noncomputable section
open Finset Filter MeasureTheory
open scoped Classical ENNReal
namespace MajorityDynamics.Paper.UniformInternal
open MajorityDynamics.Literature.FKMAdapters

variable {N : ℕ}

lemma nsum_eq (x : MD.Ω N) (c : Coloring N) (v : Fin N) :
    MD.nsum x (fun w => !c w) v = neighborSum (sampleGraph x) c v := by
  unfold MD.nsum neighborSum
  apply sum_congr rfl
  intro w _
  rw [sampleGraph_adj]
  congr 1
  change MD.val (!c w) = opinion (c w)
  cases c w <;> rfl

lemma step_eq (x : MD.Ω N) (c : Coloring N) :
    MD.step x (fun w => !c w) = fun v => !(nextColoring (sampleGraph x) c v) := by
  funext v
  unfold MD.step
  rw [nsum_eq]
  unfold nextColoring
  split_ifs <;> rfl

lemma dynamics_eq (x : MD.Ω N) (c : Coloring N) (k : ℕ) :
    MD.Sfix x (fun v => !c v) k = fun v => !((nextColoring (sampleGraph x))^[k] c v) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [MD.Sfix, ih, step_eq, Function.iterate_succ_apply']

lemma initial_excess (T τ : ℝ) (hT : 1 < T) (c : Coloring N)
    (hτ : T⁻¹ ≤ τ) (hc : initialBias N τ c) (hs : 5 * T ≤ Real.sqrt N) :
    T⁻¹ * Real.sqrt N ≤
      (((MD.sset (fun v => !c v) true).card : ℝ) - 2 -
        (MD.sset (fun v => !c v) false).card) := by
  have hT0 : 0 < T := by linarith
  have he : (MD.sset (fun v => !c v) true).card = plusCount c := by
    congr 1
    ext v
    simp [MD.sset]
  have ht := MD.card_sset_add (fun v => !c v)
  have hfloor : τ * Real.sqrt N - 1 ≤ (⌊τ * Real.sqrt N⌋₊ : ℝ) :=
    (Nat.sub_one_lt_floor _).le
  have hhalf : (N : ℝ) - 1 ≤ 2 * (N / 2 : ℕ) := by
    have hh : N ≤ 2 * (N/2) + 1 := by omega
    have hh' : (N : ℝ) ≤ 2 * (N/2 : ℕ) + 1 := by exact_mod_cast hh
    linarith
  have hτs := mul_le_mul_of_nonneg_right hτ (Real.sqrt_nonneg (N:ℝ))
  have hfive : 5 ≤ T⁻¹ * Real.sqrt N := by
    have hh := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hT0.le)
    have hi : T⁻¹ * (5*T) = (5:ℝ) := by field_simp
    rwa [hi] at hh
  rw [he]
  unfold initialBias at hc
  have ht' : ((MD.sset (fun v => !c v) true).card : ℝ) +
      (MD.sset (fun v => !c v) false).card = N := by exact_mod_cast ht
  rw [he, hc, Nat.cast_add] at ht'
  rw [hc, Nat.cast_add]
  linarith

/-- Dense half of the proof, uniform over deterministic initial colorings. -/
lemma dense_uniform (T : ℝ) (hT : 1 < T) (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 0 < L ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (p : unitInterval) (τ : ℝ) (c : Coloring N),
        L / Real.sqrt N ≤ (p:ℝ) → T⁻¹ ≤ τ → initialBias N τ c →
          graphLaw N p {G | ¬ ∀ v, (nextColoring G)^[4] c v = false} ≤ ENNReal.ofReal ε := by
  have hT0 : 0 < T := by linarith
  obtain ⟨L,hL,Nf,hf⟩ := MD.fixed_initial_dense T⁻¹ (inv_pos.mpr hT0)
    (by exact (inv_le_one₀ hT0).mpr hT.le) ε hε
  refine ⟨L,hL, max (Nf+1) ⌈(5*T)^2⌉₊, ?_⟩
  intro N hN p τ c hp hτ hc
  have hs : 5*T ≤ Real.sqrt N := by
    apply Real.le_sqrt_of_sq_le
    exact (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈(5*T)^2⌉₊ ≤ N by omega))
  have h := hf N (by omega) p hp p.property.2 (fun v => !c v)
    (initial_excess T τ hT c hτ hc hs)
  rw [event_probability]
  apply ENNReal.ofReal_le_ofReal
  convert h using 1
  apply MD.Pr_congr
  intro x
  simp [dynamics_eq]

end MajorityDynamics.Paper.UniformInternal
