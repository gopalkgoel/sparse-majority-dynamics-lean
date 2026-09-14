import MajorityDynamics.Idealized.CriticalDay.RowInputs
import MajorityDynamics.Idealized.CriticalDay.CenteredTarget
import MajorityDynamics.Idealized.CriticalDay.AdmissibilitySeparation
import MajorityDynamics.Idealized.CriticalDay.AdmissibilityEdges

noncomputable section
open Filter Topology
open scoped BigOperators
namespace MajorityDynamics.Idealized.CriticalDay
open Universal LinearResponse PerturbedTilt
open Binomial.Approximation (Density scale)

set_option maxHeartbeats 1600000 in
theorem admissibility_spec (θ T δ : ℝ) (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hδ : 0 < δ) (n ell : ℕ)
    (hk : (n : ℝ)+1 = 1/(1-θ)) (C : ℝ) (hC : 0 ≤ C) :
    ∃ K : ℝ, T ≤ K ∧ C ≤ K ∧ 0 < K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ p : Binomial.Probability, Density θ T N p →
      ∀ a : Process.Data, Process.Specification N p (responseHorizon θ) ell a →
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ (V : Type*) [Fintype V] (y : Local.CoarseData V n), Fintype.card V = N →
      y.reg = true → FaithfulNumericalData N (p : ℝ) T δ τ a n y.integerSizes y.edge →
      ∀ q : Local.Tilt n, Local.Solves y.sizes y.realEdges q →
      (∀ s t, |(q s t : ℝ)-(p : ℝ)| ≤ C*(p : ℝ)/Real.sqrt ((p : ℝ)*N)) →
      ∀ φ : ℝ,
      (∀ s, φ ≤ Binomial.eventMass (Local.trials y.sizes s) (q s)
        (Local.historySupport y.sizes s)) →
      (∀ s b, φ ≤ Local.splitProbability y.sizes q s b ∧
        Local.splitProbability y.sizes q s b ≤ 1-φ) →
      Local.Admissible y q K φ (p : ℝ) := by
  classical
  have hT0 : 0 < T := by linarith
  obtain ⟨U,D,hUT,hD,hrow⟩ := faithful_row_inputs θ T δ hθlo hθhi hT hδ n ell hk
  obtain ⟨F,hF,htarget⟩ := centered_target θ T δ hθlo hθhi hT hδ n ell hk
  obtain ⟨v,hv,hvle⟩ := RowLimits.finite_common_positive (ν n) (ν_positive n)
  obtain ⟨φ₀,ζ,hnd⟩ := universal_nondegeneracy_exists n
  have hζ := hnd.separation_pos
  let d : ℝ := Fintype.card (History (n+1))
  have hd : 0 < d := Nat.cast_pos.mpr Fintype.card_pos
  let M : ℝ := 1+∑ s : History (n+1), ∑ t : History (n+1), |ν n t*μ n s t|
  have hM : 0 < M := by dsimp [M]; positivity
  have hMb : ∀ s t, |ν n t*μ n s t| ≤ M := by
    intro s t
    have h1 := Finset.single_le_sum (fun t _ => abs_nonneg (ν n t*μ n s t)) (Finset.mem_univ t)
    have h2 := Finset.single_le_sum (fun s _ => show 0 ≤ ∑ t, |ν n t*μ n s t| by positivity)
      (Finset.mem_univ s)
    dsimp [M]
    linarith
  let K := T+C+2/v+(M+1)+8/(v*ζ)+U
  have hU0 : 0 < U := hT0.trans_le hUT
  have hdivv : 0 < 2/v := by positivity
  have hdivζ : 0 < 8/(v*ζ) := by positivity
  have hKv : 2/v ≤ K := by dsimp [K]; linarith
  have hKM : M+1 ≤ K := by dsimp [K]; linarith
  have hKζ : 8/(v*ζ) ≤ K := by dsimp [K]; linarith
  have hKU : U ≤ K := by dsimp [K]; linarith
  have hKT : T ≤ K := by dsimp [K]; linarith
  have hKC : C ≤ K := by dsimp [K]; linarith
  have hK0 : 0 < K := hT0.trans_le hKT
  have hKinv : K⁻¹ < v*ζ/4 := by
    have hh := (div_le_iff₀ (mul_pos hv hζ)).mp hKζ
    have hi : K⁻¹ ≤ v*ζ/8 := by
      rw [inv_eq_one_div,div_le_iff₀ hK0]
      nlinarith
    nlinarith [mul_pos hv hζ]
  have hρ := (targetRate_bounds (rate_pos hθlo hθhi) hδ).1
  refine ⟨K,hKT,hKC,hK0,?_⟩
  filter_upwards [hrow,htarget,eventually_basic θ T hθlo hθhi hT,
    RowLimits.density_scale_lower_power θ T (2/v) (ell+1) hθhi hT0 (by positivity),
    RowLimits.density_scale_lower_power θ T (2*(M+1)/v+1) 0 hθhi hT0 (by positivity),
    eventually_rpow_neg_le (targetRate θ δ) ((min 1 (ζ/(4*d)))/F) hρ (by positivity),
    eventually_rpow_neg_le δ (ζ/(4*D)) hδ (by positivity)]
    with N hrow htarget hbasic hsize hlarge hterr hberr
  intro p hp a ha τ hτ hτT V inst y hcard hreg hf q hq htilt φ hcond hsplit
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr hbasic.1
  have hS : 0 < scale N p := Real.sqrt_pos.mpr (mul_pos p.property.1 hN)
  have hr := hrow p hp a ha τ hτ hτT y.integerSizes y.edge hf
  have ht := htarget p hp a ha τ hτ hτT y.integerSizes y.edge hf
  simp only [PerturbedEvolution.naturalSizes_coarse] at hr
  simp only [Local.CoarseData.integerSizes,Int.cast_natCast] at ht
  have ht' : ∀ s t, |(y.realEdges s t/(y.sizes s : ℝ)-(p : ℝ)*(y.sizes t : ℝ))/scale N p-
      ν n t*μ n s t| ≤ min 1 (ζ/(4*d)) := by
    intro s t
    apply (ht s t).trans
    have hh := mul_le_mul_of_nonneg_left hterr hF.le
    simpa only [mul_div_cancel₀ _ hF.ne'] using hh
  have hslo : ∀ s, (v/2)*(N : ℝ) ≤ (y.sizes s : ℝ) := by
    intro s
    have hc := (hr.2 s).close s
    change |(y.sizes s : ℝ)-(N : ℝ)*ν n s| ≤
      (N : ℝ)/scale N p*Real.log N^(ell+1) at hc
    have hlog := hsize p hp
    have hb : (N : ℝ)/scale N p*Real.log N^(ell+1) ≤ (v/2)*N := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hS).mpr
      have hh := mul_le_mul_of_nonneg_left hlog (show 0 ≤ v/2*(N : ℝ) by positivity)
      have hid : v/2*(N : ℝ)*(2/v*Real.log N^(ell+1)) = (N : ℝ)*Real.log N^(ell+1) := by
        field_simp
      rwa [hid] at hh
    have hvN := mul_le_mul_of_nonneg_right (hvle s) hN.le
    nlinarith only [hvN,(abs_le.mp (hc.trans hb)).1]
  have hbal : ∀ r : Fin n, |∑ t, character r.castSucc t*(y.sizes t : ℝ)| ≤
      (ζ/4)*(N : ℝ)/scale N p := by
    intro r
    have hh := (hr.2 (Classical.choice inferInstance)).history_balance r
    simp only [historyMatrix] at hh
    have heq : |∑ t, sign (bits (n+1) (Classical.choice inferInstance) r.succ)*
      character r.castSucc t*(y.sizes t : ℝ)| =
        |∑ t, character r.castSucc t*(y.sizes t : ℝ)| := by
      simp only [mul_assoc, ← Finset.mul_sum]
      rw [abs_mul]
      have hsign : |sign (bits (n+1) (Classical.choice inferInstance) r.succ)| = 1 := by
        cases bits (n+1) (Classical.choice inferInstance) r.succ <;> norm_num [sign]
      rw [hsign,one_mul]
    rw [heq] at hh
    apply hh.trans
    have hb := mul_le_mul_of_nonneg_left hberr hD.le
    have hid : D*(ζ/(4*D)) = ζ/4 := by field_simp
    rw [hid] at hb
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb hN.le) hS.le
  have hsp := separation_of_centered_target hN p.property.1 (half_pos hv) hζ
    (fun s => (y.sizes s : ℝ)) y.realEdges hslo hbal
    (fun s t => (ht' s t).trans (min_le_right _ _)) hnd.separation
  -- Edge estimates are supplied by the generic algebraic consequence of the same centered target.
  have hed := admissible_edges_of_centered y hcard hN p.property.1 (half_pos hv)
    hM.le hslo hMb (fun s t => (ht' s t).trans (min_le_left _ _)) (by
      have hh := hlarge p hp
      simp only [pow_zero,mul_one] at hh
      have hid : (M+1)/(v/2) = 2*(M+1)/v := by field_simp
      rw [hid]
      change 2*(M+1)/v < scale N p
      linarith)
  have hp0 := p.property.1
  have hEsc : 0 < Local.edgeScale N p := by unfold Local.edgeScale; positivity
  refine ⟨hreg,?_,?_,?_,?_,?_,?_,hcond,hq,hsplit⟩
  · intro s
    have hi : K⁻¹ ≤ v/2 := by
      rw [inv_eq_one_div,div_le_iff₀ hK0]
      have hh := (div_le_iff₀ hv).mp hKv
      nlinarith
    simpa only [hcard] using (mul_le_mul_of_nonneg_right hi hN.le).trans (hslo s)
  · intro r
    have hbalU : |∑ t, character r.castSucc t*(y.sizes t : ℝ)| ≤ U*(N : ℝ)/scale N p := by
      -- The same signed-matrix identity yields the original row-input bound.
      have hh := (hr.2 (Classical.choice inferInstance)).history_balance r
      simp only [historyMatrix] at hh
      have hid : (∑ t, sign (bits (n+1) (Classical.choice inferInstance) r.succ)*
          character r.castSucc t*(y.sizes t : ℝ)) =
          sign (bits (n+1) (Classical.choice inferInstance) r.succ)*
          ∑ t, character r.castSucc t*(y.sizes t : ℝ) := by rw [Finset.mul_sum]; congr 1; funext t; ring
      rw [hid,abs_mul] at hh
      have hab : |sign (bits (n+1) (Classical.choice inferInstance) r.succ)| = 1 := by
        cases bits (n+1) (Classical.choice inferInstance) r.succ <;> norm_num [sign]
      rw [hab,one_mul] at hh
      exact hh.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hr.1.2 hN.le) hS.le)
    simpa only [hcard,scale] using hbalU.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKU hN.le) hS.le)
  · intro s t
    simpa only [hcard] using (hed s t).1.trans (mul_le_mul_of_nonneg_right hKM hEsc.le)
  · exact fun s t => (hed s t).2
  · intro s r
    have hm : (v*ζ/4)*Local.edgeScale N p ≤
        sign (bits (n+1) s r.succ)*∑ t, character r.castSucc t*y.realEdges s t := by
      calc
        _ = (v/2*ζ/2)*Local.edgeScale N p := by ring
        _ ≤ _ := hsp s r
    have hh := (mul_lt_mul_of_pos_right hKinv hEsc).trans_le hm
    simpa only [hcard] using Local.decision_of_strict_margin
      (bits (n+1) s r.castSucc) (bits (n+1) s r.succ) hh
  · intro s t
    simpa only [hcard,scale] using (htilt s t).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKC p.property.1.le) hS.le)

end MajorityDynamics.Idealized.CriticalDay
