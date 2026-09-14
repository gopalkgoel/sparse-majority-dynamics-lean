import MajorityDynamics.Idealized.CriticalDay.SparseFaithfulRows
import MajorityDynamics.Idealized.CriticalDay.CoreAdmissibilityBudget
import MajorityDynamics.Idealized.PerturbedEvolution.Basic

noncomputable section
open Filter Topology
open scoped BigOperators
namespace MajorityDynamics.Idealized.CriticalDay
open Universal LinearResponse PerturbedTilt PerturbedEvolution RowLimits
open Binomial.Approximation (SparseRange scale)

/-- The terminal step supplies an actual core-admissible tilt and signed
template gain for every faithful coarse state in the stopping window. -/
theorem terminal_faithful_core_sparse (θ T δ r : ℝ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hr : 0 < r) (hr3 : r ≤ 1/3) (hgap : r/4 < δ) (n ell : ℕ) :
    ∃ U φ ζ : ℝ, T ≤ U ∧ 1 < U ∧ 0 < φ ∧ 0 < ζ ∧
      ∀ᶠ N : ℕ in atTop, ∀ p : Binomial.Probability, SparseRange θ T N p →
      scale N p^r ≤ (betaScale N p n*scale N p)*scale N p →
      betaScale N p n*scale N p ≤ scale N p^r →
      ∀ a : Process.Data, Process.LevelEstimates N p ell (a.state n) →
      Process.StateSymmetric (a.state n) →
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ (V : Type*) [Fintype V], Fintype.card V = N →
      ∀ y : Local.CoarseData V n, Faithful N p T δ τ a y →
      ∃ q : Local.Tilt n, Local.CoreAdmissible y q U φ p ∧
        ∀ s b, ζ*min (betaScale N p n*scale N p) 1*N ≤ sign b*
          (Local.templateSizes y.sizes q (append s b)-(N:ℝ)*ν (n+1) (append s b)) := by
  classical
  have hT0 : 0 < T := by linarith
  obtain ⟨R,φ,ζ,hR,hφ,hζ,hrows⟩ := terminal_faithful_rows_sparse θ T δ r
    hθlo hθhi hT hr hr3 hgap n ell
  obtain ⟨Ct,hCt,htilt⟩ := row_tilt_bound_sparse n R hR.le
  obtain ⟨v,hv,hvle⟩ := finite_common_positive (ν n) (ν_positive n)
  obtain ⟨_,zeta,hnd⟩ := universal_nondegeneracy_exists n
  have hzeta := hnd.separation_pos
  let d : ℝ := Fintype.card (History (n+1))
  have hd : 0 < d := Nat.cast_pos.mpr Fintype.card_pos
  let M := 1+∑ s : History (n+1), ∑ t : History (n+1), |ν n t*μ n s t|
  have hM : 0 < M := by dsimp [M]; positivity
  have hMb (s t) : |ν n t*μ n s t| ≤ M := by
    have h1 := Finset.single_le_sum (fun t _ => abs_nonneg (ν n t*μ n s t)) (Finset.mem_univ t)
    have h2 := Finset.single_le_sum (fun s _ =>
      show 0 ≤ ∑ t, |ν n t*μ n s t| by positivity) (Finset.mem_univ s)
    dsimp [M]
    linarith
  obtain ⟨K,hK1,_,hcore⟩ := core_admissible_of_centered_budget n (half_pos hv)
    hzeta hM.le hCt.le hMb hnd.separation
  have hK : 0 < K := zero_lt_one.trans_le hK1
  let ε := min (v/2) (min (zeta/4) (min 1 (zeta/(4*d))))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεv : ε ≤ v/2 := min_le_left _ _
  have hεz : ε ≤ zeta/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hεc : ε ≤ min 1 (zeta/(4*d)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨K+T,φ,ζ,by linarith,by linarith,hφ,hζ,?_⟩
  filter_upwards [hrows ε hε,htilt θ T hθlo hθhi hT,
    eventually_basic_sparse θ T hθlo hθhi hT,
    density_scale_lower_power_sparse θ T ((M+1)/(v/2)+1) 0 hθhi hT0 (by positivity)]
    with N hrow htil hb hlarge
  intro p hp halo hahi a ha hsym τ hτ hτT V inst hcard y hf
  obtain ⟨_,_,hsize,hhist,hcenter,σ,hσ,hsol,hmass,hgain⟩ :=
    hrow p hp halo hahi a ha hsym τ hτ hτT y.integerSizes y.edge hf.2
  simp only [naturalSizes_coarse,realEdges_coarse,
    Local.CoarseData.integerSizes,Int.cast_natCast] at hsize hhist hcenter hsol hmass hgain
  have hn : 0 < (N:ℝ) := Nat.cast_pos.mpr hb.1
  have hs : 0 < scale N p := Real.sqrt_pos.mpr (mul_pos p.property.1 hn)
  have hsz : ∀ s, (v/2)*N ≤ (y.sizes s:ℝ) := by
    intro s
    have hh := (abs_le.mp (hsize s)).1
    have hvN := mul_le_mul_of_nonneg_left (hvle s) hn.le
    have heN := mul_le_mul_of_nonneg_left hεv hn.le
    nlinarith only [hh,hvN,heN]
  have hbal : ∀ j : Fin n, |∑ t, character j.castSucc t*(y.sizes t:ℝ)| ≤
      (zeta/4)*N/scale N p := by
    intro j
    let s0 : History (n+1) := Classical.choice inferInstance
    have hh := hhist s0 j
    simp only [historyMatrix,mul_assoc,← Finset.mul_sum] at hh
    rw [abs_mul] at hh
    have hab : |sign (bits (n+1) s0 j.succ)| = 1 := by
      cases bits (n+1) s0 j.succ <;> norm_num
    rw [hab,one_mul] at hh
    exact hh.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hεz hn.le) hs.le)
  let q : Local.Tilt n := fun s => rowTilt N p (σ s)
  have had : Local.CoreAdmissible y q K φ p := by
    apply hcore V N hcard p hn p.property.1
      (by have hh := hlarge p hp; simp only [pow_zero,mul_one] at hh; change _ < scale N p; linarith)
      y hf.1 hsz hbal (fun s t => (hcenter s t).trans hεc) q hsol
    · exact htil p hp σ hσ
    · exact hmass
  exact ⟨q,had.mono hK (by linarith) le_rfl p.property.1.le,hgain⟩

end MajorityDynamics.Idealized.CriticalDay
