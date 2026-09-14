import MajorityDynamics.GraphProcess.EnumerationBounds.Asymptotics
import MajorityDynamics.Local.CoarseData
import MajorityDynamics.Probability.DegreeConcentration.Basic

noncomputable section
open scoped Classical
namespace MajorityDynamics.GraphProcess.GammaNumerator
open Universal

/-- The original kappa tolerance is small compared to every block mean. -/
theorem tolerance_le_block {N T p a : ℝ} (hT : 0 < T) (hp : 0 ≤ p)
    (ha : N/T ≤ a) (hx : T*(p*N)^((4:ℝ)/7) ≤ p*N) :
    (p*N)^((4:ℝ)/7) ≤ p*a := by
  have hh := mul_le_mul_of_nonneg_left ((div_le_iff₀ hT).mp ha) hp
  nlinarith

/-- Every two large blocks satisfy the exact A.10 size-ratio window. -/
theorem block_sizeRange {N T : ℝ} {a b : ℕ} (hT : 0 < T)
    (ha : N/T ≤ (a:ℝ)) (hb : N/T ≤ (b:ℝ))
    (haN : (a:ℝ) ≤ N) (hbN : (b:ℝ) ≤ N) :
    Probability.DegreeConcentration.sizeRange T a b := by
  constructor
  · rw [← div_eq_inv_mul]
    apply (div_le_iff₀ hT).mpr
    exact haN.trans ((div_le_iff₀ hT).mp hb)
  · simpa [mul_comm] using hbN.trans ((div_le_iff₀ hT).mp ha)

universe u

/-- A single threshold chosen before the density, carrier and partition gives all
of A.10's numerical hypotheses, including the same tolerance on both cross sides. -/
theorem uniform_regime {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ π : V → History (n+1),
      (∀ s, (N : ℝ)/T ≤ (Local.partSizes π s : ℝ)) →
      0 < (N : ℝ) ∧ 0 < p ∧ p < 1 ∧ 2*T ≤ (N : ℝ) ∧
      (∀ s, 2 ≤ Local.partSizes π s) ∧
      (∀ s, (p*N)^((4:ℝ)/7) ≤ p*(Local.partSizes π s : ℝ)) ∧
      (∀ s t, Probability.DegreeConcentration.sizeRange T
        (Local.partSizes π t) (Local.partSizes π s)) := by
  obtain ⟨X,hX,hpow⟩ := EnumerationBounds.eventually_mul_rpow_le
    (a := (4:ℝ)/7) (b := 1) (A := T) (B := 1) (by norm_num) zero_lt_one
  obtain ⟨N₀,h₀⟩ := EnumerationBounds.eventually_window hθlo hθhi hT
    (L := X) (U := 1/2) (M := 2*T) hX (by norm_num) (by linarith)
  refine ⟨N₀, ?_⟩
  intro N hN V inst hcard p hlo hhi π hsizes
  obtain ⟨hNp,hp,hNT,hx,hp1⟩ := h₀ N hN p hlo hhi
  have hT0 : 0 < T := by linarith
  have hup (s : History (n+1)) : (Local.partSizes π s : ℝ) ≤ N := by
    have hh : Local.partSizes π s ≤ Fintype.card V :=
      (Finset.card_filter_le _ _).trans_eq Finset.card_univ
    rw [hcard] at hh
    exact_mod_cast hh
  have htol : T*(p*N)^((4:ℝ)/7) ≤ p*N := by
    simpa only [Real.rpow_one, one_mul] using hpow (p*N) hx
  refine ⟨hNp,hp,by linarith,hNT,?_,?_,?_⟩
  · intro s
    have hh := (div_le_iff₀ hT0).mp (hsizes s)
    have hh' : (2:ℝ) ≤ Local.partSizes π s := by nlinarith
    exact_mod_cast hh'
  · intro s
    exact tolerance_le_block hT0 hp.le (hsizes s) htol
  · intro s t
    exact block_sizeRange hT0 (hsizes t) (hsizes s) (hup t) (hup s)

/-- A fixed finite union costs no exponential rate beyond one unit. -/
theorem eventually_exp_absorption (h : ℕ) (K : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (h:ℝ)^2 * Real.exp (-(K+1)*(N:ℝ)) ≤ Real.exp (-K*(N:ℝ)) := by
  obtain ⟨N₀,h₀⟩ := Filter.eventually_atTop.mp
    ((tendsto_natCast_atTop_atTop : Filter.Tendsto (fun N : ℕ => (N:ℝ))
      Filter.atTop Filter.atTop).eventually_ge_atTop ((h:ℝ)^2))
  refine ⟨N₀, ?_⟩
  intro N hN
  have hh : (h:ℝ)^2 ≤ Real.exp (N:ℝ) := by
    have he := Real.add_one_le_exp (N:ℝ)
    linarith [h₀ N hN]
  calc
    (h:ℝ)^2 * Real.exp (-(K+1)*(N:ℝ)) ≤
        Real.exp (N:ℝ) * Real.exp (-(K+1)*(N:ℝ)) :=
      mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
    _ = Real.exp (-K*(N:ℝ)) := by rw [← Real.exp_add]; congr 1; ring

end MajorityDynamics.GraphProcess.GammaNumerator

/-- info: 'MajorityDynamics.GraphProcess.GammaNumerator.tolerance_le_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GammaNumerator.tolerance_le_block

/-- info: 'MajorityDynamics.GraphProcess.GammaNumerator.block_sizeRange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GammaNumerator.block_sizeRange

/-- info: 'MajorityDynamics.GraphProcess.GammaNumerator.uniform_regime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GammaNumerator.uniform_regime

/-- info: 'MajorityDynamics.GraphProcess.GammaNumerator.eventually_exp_absorption' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GammaNumerator.eventually_exp_absorption
