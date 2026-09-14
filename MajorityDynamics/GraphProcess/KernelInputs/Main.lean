import MajorityDynamics.GraphProcess.KernelInputs.Verified
import MajorityDynamics.GraphProcess.KernelInputs.Subsets
import MajorityDynamics.GraphProcess.KernelInputs.Numerics
import MajorityDynamics.GraphProcess.KernelInputs.CountWindows

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MajorityDynamics.GraphProcess.KernelInputs
open Universal
universe u

/-- All deterministic kernel-application hypotheses, uniformly from the original
LA and R1/R2 inputs. The fixed application parameter precedes the size threshold;
no numerical certificate, attainability, or graph estimate is assumed. -/
theorem uniform_inputs {θ T φ Cf : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) (_hCf : 0 ≤ Cf) :
    ∃ U : ℝ, 1 < U ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      Local.Admissible y q T φ p → ∀ σ : FineState.State V n,
      CoarseKernel.rho p σ = y → DegreeTypical y p σ → SizeTypical y q Cf σ →
      Verified θ T φ p U y σ := by
  obtain ⟨N₀,h₀⟩ := Numerics.uniform_regime (Cf:=Cf) hθlo hθhi hT hφ hφ1
  have hU := Numerics.parameter_bounds hT hφ hφ1
  refine ⟨Numerics.parameter T φ,hU.1,N₀,?_⟩
  intro N hN V inst hcard p hlo hhi y q hLA σ hρ h1 h2
  have hg := h₀ N hN p hlo hhi
  have hN0 := hg.N_pos
  have hp0 := hg.p_pos
  have hT0 : 0 < T := by linarith
  have hs (s : History (n+1)) : (N:ℝ)/T ≤ (y.sizes s : ℝ) := by
    simpa only [hcard, div_eq_mul_inv, mul_comm] using hLA.sizes s
  have hsN (s : History (n+1)) : (y.sizes s : ℝ) ≤ N := by
    exact_mod_cast (y.sizes_le_card s).trans_eq hcard
  have hs2 (s : History (n+1)) : (2:ℝ) ≤ y.sizes s := hg.block_size _ (hs s) (hsN s)
  have hs0 (s : History (n+1)) : (0:ℝ) < y.sizes s := by linarith [hs2 s]
  have herr : Cf*LocalTransition.sizeScale (Fintype.card V) ≤ φ*Fintype.card V/(2*T) := by
    simpa only [LocalTransition.sizeScale, hcard, ← mul_assoc] using hg.size_error
  have hc (s : History (n+1)) (b : Bool) : φ*N/(2*T) ≤ ((child σ s b).card : ℝ) := by
    simpa only [hcard] using child_size_lower hT0 hφ.le hLA h2 herr s b
  have hcN (s : History (n+1)) (b : Bool) : ((child σ s b).card : ℝ) ≤ N := by
    exact_mod_cast (child_card_le σ s b).trans_eq hcard
  have hc0 (s : History (n+1)) (b : Bool) : (0:ℝ) < (child σ s b).card :=
    (by positivity : (0:ℝ) < φ*N/(2*T)).trans_le (hc s b)
  have hrel (s t : History (n+1)) (b : Bool) :=
    Numerics.relative_sizes hT hφ hφ1 hg.N_pos (hs t) (hsN t) (hs s) (hsN s) (hc s b)
  have hcounts (s t : History (n+1)) :
      |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*((N:ℝ)^2*p/Real.sqrt (p*N)) := by
    simpa only [Local.CoarseData.realEdges, Local.edgeScale, hcard] using hLA.edge_scale s t
  have hcount_scale (t : History (n+1)) :
      2*T^3*((y.sizes t : ℝ)^2*p/Real.sqrt (p*y.sizes t)) ≤
        Numerics.parameter T φ*(y.sizes t : ℝ)^2*p/Real.sqrt (p*y.sizes t) := by
    calc
      _ ≤ Numerics.parameter T φ*((y.sizes t : ℝ)^2*p/Real.sqrt (p*y.sizes t)) :=
        mul_le_mul_of_nonneg_right hU.2.2.1 (by positivity)
      _ = _ := by ring
  refine {
    N_pos := by simpa only [hcard] using hg.N_pos
    p_pos := hg.p_pos
    p_lt_one := hg.p_lt_one
    part_eq := fiber_part hρ
    parent_sizes := ?_
    child_sizes := ?_
    density := fun t => hg.density _ (hs t) (hsN t)
    relative_sizes := fun s t => ⟨(hrel s t false).1,(hrel s t false).2.1⟩
    subset_sizes := ?_
    cross_count := ?_
    internal_count := ?_
    radius_window := ?_
    radius_log_window := ?_
    degree_window := ?_
    normalized_window := ?_
    normalized_identity := fun v t => normalized_reconstruct hg.p_pos (hs0 t)
    edge_scale := ?_
    doubled_edge_scale := ?_
    tail_threshold := ?_ }
  · intro s
    simpa only [hcard] using (show (N:ℝ)/T ≤ (y.sizes s : ℝ) ∧
      (y.sizes s : ℝ) ≤ N ∧ 2 ≤ (y.sizes s : ℝ) from ⟨hs s,hsN s,hs2 s⟩)
  · intro s b
    simpa only [hcard] using (show φ*N/(2*T) ≤ ((child σ s b).card : ℝ) ∧
      ((child σ s b).card : ℝ) ≤ N ∧ 0 < ((child σ s b).card : ℝ) from ⟨hc s b,hcN s b,hc0 s b⟩)
  · intro s t b
    refine ⟨(hrel s t b).2.2,?_⟩
    rw [child_complement_card σ hρ s b]
    exact (hrel s t (!b)).2.2
  · intro s t
    exact (cross_count_window hT hg.p_pos hg.p_lt_one.le (hs2 t) (hs t) (hsN t)
      (hcounts s t)).trans (hcount_scale t)
  · intro t
    have he : (y.edge t t : ℝ) = 2*((y.edge t t/2).toNat : ℝ) :=
      (internal_total_half_real y t).symm
    have hh : |(y.edge t t : ℝ)-p*(y.sizes t : ℝ)^2| ≤
        T*((N:ℝ)^2*p/Real.sqrt (p*N)) := by
      simpa only [pow_two, mul_assoc] using hcounts t t
    exact (internal_count_window hT hg.p_pos hg.p_lt_one.le (hs2 t) (hs t) (hsN t)
      he hh).trans (hcount_scale t)
  · intro t
    simpa only [hcard] using hg.degree_window _ (hs t) (hsN t)
  · intro s t
    simpa only [hcard] using hg.log_window _ _ (hs t) (hsN t) (hs s) (hsN s)
  · intro v u t
    exact (h1 v t).trans (by simpa only [hcard] using hg.degree_window _ (hs u) (hsN u))
  · intro v s t
    apply normalized_abs_le hg.p_pos (hs0 s)
    exact (h1 v s).trans (by simpa only [hcard] using hg.log_window _ _ (hs t) (hsN t) (hs s) (hsN s))
  · intro t
    exact localEdgeScale_le_global (by linarith [hs2 t])
      (by simpa only [hcard] using hsN t) hg.p_pos
  · intro t
    exact doubled_localEdgeScale_le_global (by linarith [hs2 t])
      (by simpa only [hcard] using hsN t) hg.p_pos hT.le
  · intro s t b a hbad
    refine ⟨by simpa only [hcard] using hg.growth _ (hs t) (hsN t),?_⟩
    exact kappa_normalized_lower hg.p_pos (hc0 s b)
      (by simpa only [hcard] using hcN s b) hbad

/-- Direct unchanged FiberTypical consumer; its R3 component is not used. -/
theorem uniform_typical_inputs {θ T φ Cf : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) (hCf : 0 ≤ Cf) :
    ∃ U : ℝ, 1 < U ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N → ∀ p : ℝ,
      T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      Local.Admissible y q T φ p → ∀ σ : FineState.State V n,
      CoarseKernel.rho p σ = y → LocalTransition.FiberTypical y q p Cf σ →
      Verified θ T φ p U y σ := by
  obtain ⟨U,hU,N₀,h₀⟩ := uniform_inputs n hθlo hθhi hT hφ hφ1 hCf
  refine ⟨U,hU,N₀,?_⟩
  intro N hN V inst hcard p hlo hhi y q hLA σ hρ htyp
  exact h₀ N hN V hcard p hlo hhi y q hLA σ hρ htyp.1 htyp.2.1

end MajorityDynamics.GraphProcess.KernelInputs
