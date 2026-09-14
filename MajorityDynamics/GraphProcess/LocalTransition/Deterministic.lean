import MajorityDynamics.GraphProcess.LocalTransition.Basic
import MajorityDynamics.GraphProcess.LocalTransition.Mass

noncomputable section
open MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.LocalTransition
open Universal
variable {V : Type*} [Fintype V] {n : ℕ}
universe u

/-- The exact two-R3 replacement of the ordered mass quotient. -/
theorem mass_quotient_error (y : Local.CoarseData V n) (q : Local.Tilt n) (p Cf : ℝ)
    (σ : FineState.State V n) (hρ : CoarseKernel.rho p σ = y)
    (hsol : Local.Solves y.sizes y.realEdges q) (hpos : ∀ s t, 0 < y.realEdges s t)
    (hf : FiberGood y q p Cf σ) (s t : History (n+1)) (b c : Bool) :
    |(RowArray.childMass (RowArray.stateArray σ) s b t : ℝ) *
       (RowArray.childMass (RowArray.stateArray σ) t c s : ℝ) / y.realEdges s t -
       Local.templateEdges y.sizes y.realEdges q (append s b) (append t c)| ≤
      2 * Cf * massScale (Fintype.card V) p := by
  have ha := childMass_bounds p y σ hρ s b t
  have hb := childMass_bounds p y σ hρ t c s
  have hc := templateHalfEdges_bounds y q hsol s b t
  have hd := templateHalfEdges_bounds y q hsol t c s
  rw [y.realEdges_symm t s] at hb hd
  have he := quotient_difference_le (hpos s t) ha.1 ha.2 hb.1 hb.2 hc.1 hc.2 hd.1 hd.2
  simp only [Local.templateEdges, parent_append]
  exact he.trans (by have h1 := hf.2 s t b; have h2 := hf.2 t s c; linarith)

/-- Finite deterministic assembly with only simple scalar conditions beyond
original solvability/positivity, fiber R2/R3, and kernel S1–S3. -/
theorem deterministic_finite (y : Local.CoarseData V n) (q : Local.Tilt n)
    (p Cf Cs : ℝ) (σ : FineState.State V n) (τ : FineState.State V (n+1))
    (hN : 1 ≤ (Fintype.card V : ℝ)) (hp : 0 < p)
    (hgrowth : 2 ≤ (p * Fintype.card V)^((1:ℝ)/14))
    (hCf : 0 ≤ Cf) (hCs : 0 ≤ Cs)
    (hsol : Local.Solves y.sizes y.realEdges q) (hpos : ∀ s t, 0 < y.realEdges s t)
    (hρ : CoarseKernel.rho p σ = y)
    (hf : FiberGood y q p Cf σ) (hk : KernelGood y p Cs σ τ) :
    LocalSuccess y q p (Cf+Cs) (CoarseKernel.rho p τ) := by
  have hpart : σ.part = y.part := congrArg Local.CoarseData.part hρ
  have hmass := massScale_nonneg (Fintype.card V) p hN hp.le
  have hsize := sizeScale_nonneg (Fintype.card V) hN
  refine ⟨?_, (CoarseKernel.flag_true p τ.part τ.deg).mpr hk.2.1, ?_, ?_⟩
  · intro v
    change parent (τ.part v) = y.part v
    rw [hk.1, FineState.parent_refinement, hpart]
  · intro s b
    have hc : (CoarseKernel.rho p τ).sizes (append s b) =
        (RowArray.childSet (RowArray.stateArray σ) s b).card := by
      rw [RowArray.childSet_stateArray, History.block_card_partSizes]
      change Local.partSizes τ.part (append s b) = _
      rw [hk.1]
    rw [hc]
    exact (hf.1 s b).trans (mul_le_mul_of_nonneg_right (by linarith) hsize)
  · intro s t b c
    let a := (RowArray.childMass (RowArray.stateArray σ) s b t : ℝ) *
      (RowArray.childMass (RowArray.stateArray σ) t c s : ℝ) / y.realEdges s t
    have hq := mass_quotient_error y q p Cf σ hρ hsol hpos hf s t b c
    have hscale : 2 * Cf * massScale (Fintype.card V) p ≤
        Cf * edgeScale (Fintype.card V) p := by
      rw [edgeScale_eq _ _ (by linarith) hp]
      have hx := mul_le_mul_of_nonneg_right hgrowth (mul_nonneg hCf hmass)
      nlinarith
    calc
      _ ≤ |(CoarseKernel.rho p τ).realEdges (append s b) (append t c) - a| +
          |a - Local.templateEdges y.sizes y.realEdges q (append s b) (append t c)| :=
        abs_sub_le _ _ _
      _ ≤ Cs * edgeScale (Fintype.card V) p + Cf * edgeScale (Fintype.card V) p :=
        add_le_add (hk.2.2 s t b c) (hq.trans hscale)
      _ = _ := by ring

/-- Original density and unchanged LA discharge all deterministic scalar and mass
conditions. The threshold is independent even of the two error constants. -/
theorem uniform_deterministic {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n) (φ : ℝ),
      Local.Admissible y q T φ p → ∀ Cf Cs : ℝ, 0 ≤ Cf → 0 ≤ Cs →
      ∀ (σ : FineState.State V n) (τ : FineState.State V (n+1)),
      CoarseKernel.rho p σ = y → FiberGood y q p Cf σ → KernelGood y p Cs σ τ →
      LocalSuccess y q p (Cf+Cs) (CoarseKernel.rho p τ) := by
  obtain ⟨N₀,h₀⟩ := uniform_numerical_regime hθlo hθhi hT
  refine ⟨N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi y q φ ha Cf Cs hCf hCs σ τ hρ hf hk
  obtain ⟨hN2,hp,_,hg⟩ := h₀ N hN p hlo hhi
  apply deterministic_finite y q p Cf Cs σ τ _ hp _ hCf hCs ha.solves ha.positive hρ hf hk
  · rw [hcard]; exact_mod_cast (show 1 ≤ N by omega)
  · simpa only [hcard] using hg

end MajorityDynamics.GraphProcess.LocalTransition
