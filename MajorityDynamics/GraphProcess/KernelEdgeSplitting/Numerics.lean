import MajorityDynamics.GraphProcess.KernelEdgeSplitting.Basic

noncomputable section
open Filter
open scoped Topology
namespace MajorityDynamics.GraphProcess.KernelEdgeSplitting.Numerics

/-- One global threshold makes every linearly sized block large enough for C.1
and converts its reciprocal logarithmic error to the global logarithm. -/
theorem uniform_block_log {T : ℝ} (hT : 1 < T) (r₀ : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ r : ℕ,
      (N : ℝ)/T ≤ r → (r : ℝ) ≤ N →
      r₀ ≤ r ∧ 0 < Real.log (N : ℝ) ∧ 0 < Real.log (r : ℝ) ∧
      1 / Real.log (r : ℝ) ≤ 2 / Real.log (N : ℝ) := by
  have hT0 : 0 < T := by linarith
  obtain ⟨N₁,h₁⟩ := KernelInputs.Numerics.eventually_size_log
    (φ := 1) (Cf := 0) hT zero_lt_one
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  obtain ⟨N₂,h₂⟩ := eventually_atTop.mp (hnat.eventually_ge_atTop (T*r₀))
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN r hr hrN
  have hs := h₁ N ((le_max_left _ _).trans hN)
  have hb := KernelInputs.Numerics.block_log hT hs.1 hr hrN hs.2.2.2.1
  have hg : 0 < Real.log (N : ℝ) := by linarith [hs.2.1]
  have hl : 0 < Real.log (r : ℝ) := by linarith [hb.2.1]
  refine ⟨?_, hg, hl, ?_⟩
  · have hn := h₂ N ((le_max_right _ _).trans hN)
    have hr' := (div_le_iff₀ hT0).mp hr
    have hx : (r₀ : ℝ) ≤ r := by nlinarith
    exact_mod_cast hx
  · apply (div_le_div_iff₀ hl hg).mpr
    linarith [hb.2.1]

/-- The explicit finite child-pair union error vanishes for fixed history length. -/
theorem tendsto_unionError (n : ℕ) :
    Tendsto (unionError n) atTop (𝓝 0) := by
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  exact (Real.tendsto_log_atTop.comp hnat).const_div_atTop ((2 : ℝ)^(2*n+5))

/-- Every prescribed positive tolerance eventually bounds the union error. -/
theorem eventually_unionError_lt (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, unionError n N < ε := by
  exact eventually_atTop.mp ((tendsto_unionError n).eventually (eventually_lt_nhds hε))

end MajorityDynamics.GraphProcess.KernelEdgeSplitting.Numerics
