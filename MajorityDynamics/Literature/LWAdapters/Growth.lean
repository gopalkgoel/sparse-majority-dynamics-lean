import MajorityDynamics.Literature.LWAdapters.Diagonal
import MajorityDynamics.Literature.DegreeEnumeration.Statements

noncomputable section
open Filter Asymptotics
open scoped Topology
namespace MajorityDynamics.Literature.LWAdapters
open DegreeEnumeration

theorem graph_log_lower (n m : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (hlogs : ∀ K : ℝ, 0 < K → IsLittleO atTop
      (fun k => Real.log (n k) ^ K / (n k : ℝ))
      (fun k => graphDensity (n k) (m k))) :
    ∀ i : ℕ, ∀ᶠ k in atTop,
      Real.log (n k) ^ ((i : ℝ) + 1) ≤ graphAverage (n k) (m k) := by
  intro i
  have hb := (hlogs ((i : ℝ)+1) (by positivity)).bound (by norm_num : (0:ℝ) < 1/2)
  filter_upwards [hb, hn.eventually_ge_atTop 2] with k hk hk2
  have hn2 : (2 : ℝ) ≤ n k := by exact_mod_cast hk2
  have hn0 : (0 : ℝ) < n k := by linarith
  have hD : 0 ≤ graphAverage (n k) (m k) := by unfold graphAverage; positivity
  have hd : 0 ≤ graphDensity (n k) (m k) := by
    unfold graphDensity
    exact div_nonneg hD (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), abs_of_nonneg hd] at hk
  have hh := (div_le_iff₀ hn0).mp hk
  have hrat : graphDensity (n k) (m k) * (n k : ℝ) ≤ 2 * graphAverage (n k) (m k) := by
    unfold graphDensity
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : 0 < (n k : ℝ)-1)]
    nlinarith
  nlinarith

theorem graph_slow_growth (n m : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (hlogs : ∀ K : ℝ, 0 < K → IsLittleO atTop
      (fun k => Real.log (n k) ^ K / (n k : ℝ))
      (fun k => graphDensity (n k) (m k))) :
    ∃ ω : ℕ → ℝ, Tendsto ω atTop atTop ∧
      ∀ᶠ k in atTop, Real.log (n k) ^ ω (n k) ≤ graphAverage (n k) (m k) := by
  obtain ⟨w, hw, hP⟩ := slow_parameter n hn
    (fun i k => Real.log (n k) ^ ((i:ℝ)+1) ≤ graphAverage (n k) (m k))
    (graph_log_lower n m hn hlogs)
  refine ⟨fun N => (w N : ℝ)+1, ?_, hP⟩
  apply tendsto_atTop_mono (fun N => le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 1))
  exact tendsto_natCast_atTop_atTop.comp hw

theorem bipartite_slow_growth (l n m : ℕ → ℕ) (hn : Tendsto n atTop atTop) (α : ℝ)
    (hpowers : IsLittleO atTop
      (fun k => ((l k : ℝ)+n k)^(5-5*α))
      (fun k => (l k : ℝ)*n k*(m k : ℝ)^(3-5*α)))
    (hlogs : ∀ K : ℝ, 0 < K → IsLittleO atTop
      (fun k => (l k : ℝ)*Real.log (n k)^K + (n k : ℝ)*Real.log (l k)^K)
      (fun k => (m k : ℝ))) :
    ∃ ω : ℕ → ℝ, Tendsto ω atTop atTop ∧ ∀ᶠ k in atTop,
      ω (n k)*((l k : ℝ)+n k)^(5-5*α) ≤ (l k : ℝ)*n k*(m k : ℝ)^(3-5*α) ∧
      (l k : ℝ)*Real.log (n k)^ω (n k) + (n k : ℝ)*Real.log (l k)^ω (n k) ≤ m k := by
  have hP (i : ℕ) : ∀ᶠ k in atTop,
      ((i:ℝ)+1)*((l k : ℝ)+n k)^(5-5*α) ≤ (l k : ℝ)*n k*(m k : ℝ)^(3-5*α) ∧
      (l k : ℝ)*Real.log (n k)^((i:ℝ)+1) + (n k : ℝ)*Real.log (l k)^((i:ℝ)+1) ≤ m k := by
    have hi : (0:ℝ) < (i:ℝ)+1 := by positivity
    have hp := hpowers.bound (inv_pos.mpr hi)
    have hl := (hlogs ((i:ℝ)+1) hi).bound (by norm_num : (0:ℝ) < 1)
    filter_upwards [hp,hl] with k hk hkl
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)] at hk
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity), one_mul] at hkl
    refine ⟨?_, hkl⟩
    have hh := mul_le_mul_of_nonneg_left hk hi.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hi.ne', one_mul] using hh
  obtain ⟨w, hw, hP⟩ := slow_parameter n hn _ hP
  refine ⟨fun N => (w N : ℝ)+1, ?_, hP⟩
  apply tendsto_atTop_mono (fun N => le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 1))
  exact tendsto_natCast_atTop_atTop.comp hw

end MajorityDynamics.Literature.LWAdapters
