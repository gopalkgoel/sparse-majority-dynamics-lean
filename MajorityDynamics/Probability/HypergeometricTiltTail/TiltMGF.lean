import MajorityDynamics.Probability.HypergeometricTiltTail.Basic

noncomputable section
open scoped BigOperators
namespace MajorityDynamics.Probability.HypergeometricTiltTail
open FixedSizeExponential

/-- Uniform bounds on squares give the exact cost per selected coordinate. -/
theorem subset_quadratic_bound {V : Type*} (A : Finset V) {k : ℕ}
    (hA : 0 < A.card) (a : V → ℝ) {W : ℝ} (ha : ∀ v ∈ A, (a v)^2 ≤ W) :
    ((k : ℝ) / A.card) * (∑ v ∈ A, (a v)^2) ≤ (k : ℝ) * W := by
  have hc : 0 < (A.card : ℝ) := by exact_mod_cast hA
  have hsum : (∑ v ∈ A, (a v)^2) ≤ (A.card : ℝ) * W := by
    calc
      _ ≤ ∑ _v ∈ A, W := Finset.sum_le_sum ha
      _ = _ := by simp
  calc
    _ ≤ ((k : ℝ) / A.card) * ((A.card : ℝ) * W) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by field_simp

/-- Two independent actual subset MGFs, retaining the exact linear mean. -/
theorem tiltExpectation_mgf {V : Type*} [DecidableEq V]
    {P S : Finset V} (hSP : S ⊆ P) {k l : ℕ}
    (hk : k < S.card) (hl : l < (P \ S).card)
    {p L : ℝ} (hp : 0 < p) (hL : 0 < L) (β : V → ℝ)
    {W : ℝ} (ha : ∀ v ∈ P, |tiltCoefficient p L β v| ≤ 1)
    (ha2 : ∀ v ∈ P, (tiltCoefficient p L β v)^2 ≤ W) :
    tiltExpectation P S k l p L β ≤
      mgfPrefactor k * mgfPrefactor l * Real.exp
        (((k : ℝ) / S.card) * (∑ v ∈ S, tiltCoefficient p L β v) +
          ((l : ℝ) / (P \ S).card) * (∑ v ∈ P \ S, tiltCoefficient p L β v) -
          tiltConstant P p L β + ((k : ℝ) + l) * W) := by
  let a := tiltCoefficient p L β
  have hS : 0 < S.card := (Nat.zero_le k).trans_lt hk
  have hC : 0 < (P \ S).card := (Nat.zero_le l).trans_lt hl
  have hkmgf := subset_average_mgf S hk a (fun v hv => ha v (hSP hv))
  have hlmgf := subset_average_mgf (P \ S) hl a
    (fun v hv => ha v (Finset.sdiff_subset hv))
  have hkq := subset_quadratic_bound (k := k) S hS a (fun v hv => ha2 v (hSP hv))
  have hlq := subset_quadratic_bound (k := l) (P \ S) hC a
    (fun v hv => ha2 v (Finset.sdiff_subset hv))
  have hln : 0 ≤ subsetAverage (P \ S) l (fun R => Real.exp (∑ v ∈ R, a v)) :=
    subsetAverage_nonneg _ _ _ (fun _ => (Real.exp_pos _).le)
  rw [tiltExpectation_product hSP k l hp hL]
  have hprod := mul_le_mul hkmgf hlmgf hln
    (mul_nonneg (mgfPrefactor_pos k).le (Real.exp_pos _).le)
  have hmul := mul_le_mul_of_nonneg_left hprod (Real.exp_pos (-tiltConstant P p L β)).le
  calc
    _ = Real.exp (-tiltConstant P p L β) *
        (subsetAverage S k (fun R => Real.exp (∑ v ∈ R, a v)) *
          subsetAverage (P \ S) l (fun R => Real.exp (∑ v ∈ R, a v))) := by ring
    _ ≤ _ := hmul
    _ = mgfPrefactor k * mgfPrefactor l * Real.exp
        (((k : ℝ) / S.card) * (∑ v ∈ S, a v) +
          ((l : ℝ) / (P \ S).card) * (∑ v ∈ P \ S, a v) -
          tiltConstant P p L β +
          (((k : ℝ) / S.card) * ∑ v ∈ S, (a v)^2 +
            ((l : ℝ) / (P \ S).card) * ∑ v ∈ P \ S, (a v)^2)) := by
      simp only [Real.exp_add, Real.exp_sub, Real.exp_neg]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mgfPrefactor_pos k).le (mgfPrefactor_pos l).le)
      apply Real.exp_le_exp.mpr
      dsimp [a] at *
      nlinarith

/-- A uniform absolute coefficient bound, including arbitrarily small draw sizes. -/
theorem tiltExpectation_mgf_of_abs {V : Type*} [DecidableEq V]
    {P S : Finset V} (hSP : S ⊆ P) {k l : ℕ}
    (hk : k < S.card) (hl : l < (P \ S).card)
    {p L : ℝ} (hp : 0 < p) (hL : 0 < L) (β : V → ℝ)
    {w : ℝ} (hw : w ≤ 1) (ha : ∀ v ∈ P, |tiltCoefficient p L β v| ≤ w) :
    tiltExpectation P S k l p L β ≤
      mgfPrefactor k * mgfPrefactor l * Real.exp
        (((k : ℝ) / S.card) * (∑ v ∈ S, tiltCoefficient p L β v) +
          ((l : ℝ) / (P \ S).card) * (∑ v ∈ P \ S, tiltCoefficient p L β v) -
          tiltConstant P p L β + ((k : ℝ) + l) * w^2) := by
  apply tiltExpectation_mgf hSP hk hl hp hL β
  · exact fun v hv => (ha v hv).trans hw
  · intro v hv
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _)
      ((abs_nonneg _).trans (ha v hv))).2 (ha v hv)

/-- The literal beta window controls the square of each selected coefficient. -/
theorem tiltCoefficient_sq_le {V : Type*} {p L g : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (hL : 0 < L) (hg : 0 ≤ g)
    (β : V → ℝ) {v : V} (hβ : |β v| ≤ g) :
    (tiltCoefficient p L β v)^2 ≤ 4 * g^2 / (p * L) := by
  have hb : (β v)^2 ≤ g^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hg).2 hβ
  have hc : (1 + p)^2 ≤ 4 := by nlinarith
  unfold tiltCoefficient
  rw [div_pow, Real.sq_sqrt (mul_pos hp hL).le, mul_pow]
  exact div_le_div_of_nonneg_right
    ((mul_le_mul_of_nonneg_right hc (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hb (by norm_num))) (mul_pos hp hL).le

/-- The upper-only draw window suffices for the beta-weight quadratic cost. -/
theorem tilt_quadratic_cost {p L N T g : ℝ} {k l : ℕ}
    (hp : 0 < p) (hL : 0 < L) (hT : 0 < T) (hLN : N / T ≤ L)
    (hkl : (k : ℝ) + l ≤ 2 * p * N) :
    ((k : ℝ) + l) * (4 * g^2 / (p * L)) ≤ 8 * T * g^2 := by
  have hNL : N / L ≤ T := (div_le_iff₀ hL).2 (by
    have hh := (div_le_iff₀ hT).1 hLN
    nlinarith)
  calc
    _ ≤ (2 * p * N) * (4 * g^2 / (p * L)) :=
      mul_le_mul_of_nonneg_right hkl (by positivity)
    _ = (8 * g^2) * (N / L) := by field_simp; ring
    _ ≤ (8 * g^2) * T := mul_le_mul_of_nonneg_left hNL (by positivity)
    _ = _ := by ring

/-- Beta-window form with the quadratic error already bounded uniformly. -/
theorem tiltExpectation_beta_mgf {V : Type*} [DecidableEq V]
    {P S : Finset V} (hSP : S ⊆ P) {k l : ℕ}
    (hk : k < S.card) (hl : l < (P \ S).card)
    {p L N T g : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hL : 0 < L)
    (hT : 0 < T) (hLN : N / T ≤ L) (hg : 0 ≤ g)
    (hkl : (k : ℝ) + l ≤ 2 * p * N) (β : V → ℝ)
    (hβ : ∀ v ∈ P, |β v| ≤ g)
    (ha : ∀ v ∈ P, |tiltCoefficient p L β v| ≤ 1) :
    tiltExpectation P S k l p L β ≤
      mgfPrefactor k * mgfPrefactor l * Real.exp
        (((k : ℝ) / S.card) * (∑ v ∈ S, tiltCoefficient p L β v) +
          ((l : ℝ) / (P \ S).card) * (∑ v ∈ P \ S, tiltCoefficient p L β v) -
          tiltConstant P p L β + 8 * T * g^2) := by
  apply (tiltExpectation_mgf hSP hk hl hp hL β ha
    (fun v hv => tiltCoefficient_sq_le hp hp1 hL hg β (hβ v hv))).trans
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (mgfPrefactor_pos k).le (mgfPrefactor_pos l).le)
  apply Real.exp_le_exp.mpr
  have hcost := tilt_quadratic_cost (g := g) hp hL hT hLN hkl
  linarith

/-- A polynomial prefactor bound valid even for zero draws. -/
theorem mgfPrefactor_le {k : ℕ} {N : ℝ} (hN : 1 ≤ N) (hk : (k : ℝ) ≤ N) :
    mgfPrefactor k ≤ (1 + 1 / centralAtomConstant) * N := by
  have hc := centralAtomConstant_pos
  have hN0 : 0 ≤ N := by linarith
  have hs : Real.sqrt (k : ℝ) ≤ N := by
    apply (Real.sqrt_le_left hN0).2
    nlinarith
  unfold mgfPrefactor
  apply max_le
  · nlinarith [div_pos zero_lt_one hc]
  · have hh := div_le_div_of_nonneg_right hs hc.le
    calc
      _ ≤ N / centralAtomConstant := hh
      _ ≤ (1 + 1 / centralAtomConstant) * N := by
        rw [add_mul, one_mul, one_div_mul_eq_div]
        linarith

end MajorityDynamics.Probability.HypergeometricTiltTail
