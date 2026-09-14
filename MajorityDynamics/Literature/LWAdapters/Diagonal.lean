import Mathlib.Tactic

noncomputable section
open Filter
open scoped Topology
namespace MajorityDynamics.Literature.LWAdapters

/-- A slowly growing integer parameter, indexed by the actual size rather than
the sequence index. Repeated sizes cause no loss of uniformity. -/
theorem slow_parameter (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (P : ℕ → ℕ → Prop) (hP : ∀ i, ∀ᶠ k in atTop, P i k) :
    ∃ w : ℕ → ℕ, Tendsto w atTop atTop ∧ ∀ᶠ k in atTop, P (w (n k)) k := by
  classical
  choose K hK using fun i => eventually_atTop.mp (hP i)
  let T : ℕ → ℕ := fun i => (Finset.range (K i)).sup n + 1
  have hT (i k : ℕ) (h : T i ≤ n k) : P i k := by
    apply hK i k
    by_contra hh
    have hk : k ∈ Finset.range (K i) := Finset.mem_range.mpr (by omega)
    have := Finset.le_sup (f := n) hk
    dsimp [T] at h
    omega
  let w : ℕ → ℕ := fun N => Nat.findGreatest (fun i => T i ≤ N) N
  have hw : Tendsto w atTop atTop := by
    apply tendsto_atTop_atTop.mpr
    intro i
    refine ⟨max i (T i), fun N hN => ?_⟩
    exact Nat.le_findGreatest (le_trans (le_max_left _ _) hN)
      (le_trans (le_max_right _ _) hN)
  refine ⟨w, hw, ?_⟩
  filter_upwards [hn.eventually_ge_atTop (T 0)] with k hk
  apply hT
  exact Nat.findGreatest_spec (P := fun i => T i ≤ n k) (Nat.zero_le (n k)) hk

end MajorityDynamics.Literature.LWAdapters
