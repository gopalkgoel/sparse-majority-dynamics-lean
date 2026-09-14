import MajorityDynamics.Idealized.Process.EvolutionBounds
import MajorityDynamics.Idealized.Process.QuotientExpansion

/-! The full local-edge expansion and the subsequent floor correction in
Step 7 of Theorem 5.2. -/

noncomputable section
open scoped BigOperators

namespace MajorityDynamics.Idealized.Process
open Universal Local RowLimits Binomial.Approximation
variable {n : ℕ}

def meanErrorConstant (B K : ℝ) : ℝ := 2 * K * B + 2 * B ^ 3 + 1
def quotientErrorConstant (B K : ℝ) : ℝ :=
  2 * (4 * (B ^ 2 + B) ^ 2 + 5 * (B ^ 2 + B) * meanErrorConstant B K +
    meanErrorConstant B K ^ 2 + 3 * meanErrorConstant B K)
def edgeErrorConstant (B K : ℝ) : ℝ :=
  (1 + 2 * B) ^ 2 * quotientErrorConstant B K + (4 * B + 4 * B ^ 2) * (1 + B)

theorem normalized_edge_error {m z w δ : ℝ} (hz : 0 < z)
    (hm : |m - z * w| ≤ z * δ) : |m / z - w| ≤ δ := by
  have hid : m / z - w = (m - z * w) / z := by field_simp
  rw [hid, abs_div, abs_of_pos hz]
  exact (div_le_iff₀ hz).mpr (by simpa only [mul_comm] using hm)

theorem conditional_mean_relative_error_uniform {N p a z v m b ρ δ K B : ℝ}
    (hN : 0 < N) (hp : 0 < p) (ha : 0 < a) (ha2 : a ^ 2 = p * N)
    (hv : 0 < v) (hz : N * v / 2 ≤ z) (hclose : |z - N * v| ≤ N * ρ)
    (hK : 0 ≤ K) (hB : 1 ≤ B) (hvB : 1 / v ≤ B) (hb : |b| ≤ B)
    (hmean : |(m - p * z) / a - b| ≤ K * ρ) (hδ : ρ / a = δ) :
    |m / (p * z) - (1 + (b / v) / a)| ≤ meanErrorConstant B K * δ := by
  have hρ : 0 ≤ ρ := nonneg_of_mul_nonneg_right ((abs_nonneg _).trans hclose) hN
  have hδ0 : 0 ≤ δ := hδ ▸ div_nonneg hρ ha.le
  have hB0 : 0 ≤ B := by linarith
  have hbnd : 2 * K / v + 2 * B / v ^ 2 ≤ meanErrorConstant B K := by
    have hs : (1 / v) ^ 2 ≤ B ^ 2 := by
      simpa only [pow_two] using mul_le_mul hvB hvB (show 0 ≤ 1 / v by positivity) hB0
    have h₁ := mul_le_mul_of_nonneg_left hvB (show 0 ≤ 2 * K by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * B by positivity)
    dsimp [meanErrorConstant]
    convert (show 2 * K * (1 / v) + 2 * B * (1 / v) ^ 2 ≤
        2 * K * B + 2 * B ^ 3 + 1 by nlinarith) using 1
    ring
  calc
    _ ≤ (2 * K / v + 2 * B / v ^ 2) * ρ / a :=
      conditional_mean_relative_error hN hp ha ha2 hv hz hclose hK hb hmean
    _ = (2 * K / v + 2 * B / v ^ 2) * δ := by rw [← hδ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hbnd hδ0

/-- Pointwise quantitative edge bound. The hypotheses are explicit scalar
smallness conditions, all supplied uniformly by logarithmic domination. -/
theorem next_edges_quantitative (N : ℕ) (p : Binomial.Probability)
    (x : State n) (q : Local.Tilt n) (ρ δ K B : ℝ)
    (hN : 1 ≤ N) (hK : 0 ≤ K) (hB : 1 ≤ B)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 4)
    (ha : 1 ≤ scale N p) (hμsmall : B / scale N p ≤ 1 / 4)
    (hδeq : ρ / scale N p = δ) (hsq : (1 / scale N p) ^ 2 ≤ δ)
    (hinv : 1 / (N : ℝ) ≤ δ) (hround : 1 ≤ (N : ℝ) * ρ)
    (hsmall : (2 * K + 2) * ρ ≤ 1 / (2 * B))
    (hv : ∀ t, 1 / ν n t ≤ B) (hv' : ∀ u, 1 / ν (n + 1) u ≤ B)
    (hμ : ∀ s t, |μ n s t| ≤ B) (hμ' : ∀ u v, |μ (n + 1) u v| ≤ B)
    (hb : ∀ s b t, |branchMean s (ν n) (γ n s) b t| ≤ B)
    (hsize : ∀ s, |(x.sizes s : ℝ) - N * ν n s| ≤ N * ρ)
    (hedge : ∀ s t, |x.edges s t - (p : ℝ) * x.sizes s * x.sizes t *
      (1 + μ n s t / scale N p)| ≤ (p : ℝ) * x.sizes s * x.sizes t * δ)
    (hrow : RowAsymptotics N p x.sizes q (K * ρ)) :
    ∀ u v, |(nextState x q).edges u v - (p : ℝ) * (nextState x q).sizes u *
      (nextState x q).sizes v * (1 + μ (n + 1) u v / scale N p)| ≤
      (p : ℝ) * (nextState x q).sizes u * (nextState x q).sizes v *
        (edgeErrorConstant B K * δ) := by
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hp0 := p.property.1
  have hB0 : 0 < B := by linarith
  have ha0 : 0 < scale N p := by linarith
  have ha2 : scale N p ^ 2 = (p : ℝ) * N := Real.sq_sqrt (by positivity)
  have hρsmall : ρ ≤ 1 / (2 * B) := by
    have hh : ρ ≤ (2 * K + 2) * ρ := by nlinarith
    exact hh.trans hsmall
  have hvlo : ∀ t, 1 / B ≤ ν n t := by
    intro t
    exact (one_div_le (ν_positive n t) hB0).mp (hv t)
  have hvlo' : ∀ u, 1 / B ≤ ν (n + 1) u := by
    intro u
    exact (one_div_le (ν_positive (n + 1) u) hB0).mp (hv' u)
  have hslo : ∀ t, (N : ℝ) * ν n t / 2 ≤ x.sizes t := by
    intro t
    have hc := (abs_le.mp (hsize t)).1
    have hh : ρ ≤ ν n t / 2 := calc
      ρ ≤ 1 / (2 * B) := hρsmall
      _ = (1 / B) / 2 := by ring
      _ ≤ ν n t / 2 := div_le_div_of_nonneg_right (hvlo t) (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left hh hN0.le]
  have hspos : ∀ t, 0 < (x.sizes t : ℝ) := fun t =>
    (half_pos (mul_pos hN0 (ν_positive n t))).trans_le (hslo t)
  have hnext := next_sizes_quantitative N p x q ρ K hρ hρ1 hK hround hsize hrow
  have hnlo : ∀ u, (1 / (2 * B)) * (N : ℝ) ≤ (nextState x q).sizes u := by
    intro u
    have hh := (abs_le.mp (hnext u)).1
    have hvu : 2 * (1 / (2 * B)) ≤ ν (n + 1) u := by
      convert hvlo' u using 1
      ring
    have hbudget := mul_le_mul_of_nonneg_left hsmall hN0.le
    have hvl := mul_le_mul_of_nonneg_left hvu hN0.le
    nlinarith
  have hnpos : ∀ u, 0 < ((nextState x q).sizes u : ℝ) := fun u =>
    (by positivity : 0 < (1 / (2 * B)) * (N : ℝ)).trans_le (hnlo u)
  have hM0 : 0 ≤ meanErrorConstant B K := by unfold meanErrorConstant; positivity
  have hM1 : 1 ≤ meanErrorConstant B K := by
    have hh : 0 ≤ 2 * K * B + 2 * B ^ 3 := by positivity
    unfold meanErrorConstant
    linarith
  have hcoef : ∀ s b t, |branchMean s (ν n) (γ n s) b t / ν n t| ≤ B ^ 2 + B := by
    intro s b t
    rw [abs_div, abs_of_pos (ν_positive n t), div_eq_mul_inv]
    have hh := mul_le_mul (hb s b t) (by simpa only [one_div] using hv t)
      (inv_nonneg.mpr (ν_positive n t).le) hB0.le
    exact hh.trans (by nlinarith)
  have hmeans := fun s b t => conditional_mean_relative_error_uniform hN0 p.property.1 ha0 ha2
    (ν_positive n t) (hslo t) (hsize t) hK hB (hv t) (hb s b t) (hrow.child_mean s b t) hδeq
  have hnorm : ∀ s t, |x.edges s t / ((p : ℝ) * x.sizes s * x.sizes t) -
      (1 + μ n s t / scale N p)| ≤ δ := by
    intro s t
    exact normalized_edge_error (mul_pos (mul_pos hp0 (hspos s)) (hspos t)) (hedge s t)
  have hden : ∀ s t, 1 / 2 ≤ x.edges s t / ((p : ℝ) * x.sizes s * x.sizes t) := by
    intro s t
    have hz := (abs_le.mp (hnorm s t)).1
    have hmuabs : |μ n s t / scale N p| ≤ 1 / 4 := by
      rw [abs_div, abs_of_pos ha0]
      exact (div_le_div_of_nonneg_right (hμ s t) ha0.le).trans hμsmall
    have hmul := (abs_le.mp hmuabs).1
    linarith
  intro u v
  let s := parent u
  let t := parent v
  let e := branchMean s (ν n) (γ n s) (last u) t / ν n t
  let f := branchMean t (ν n) (γ n t) (last v) s / ν n s
  let z := x.edges s t / ((p : ℝ) * x.sizes s * x.sizes t)
  let a := childMean x.sizes q s (last u) t / ((p : ℝ) * x.sizes t)
  let b := childMean x.sizes q t (last v) s / ((p : ℝ) * x.sizes s)
  have hq := quotient_linear_error (h := 1 / scale N p) (δ := δ) (B := B ^ 2 + B)
    (K := meanErrorConstant B K) (e := e) (f := f) (m := μ n s t)
    (dx := a - (1 + e / scale N p)) (dy := b - (1 + f / scale N p))
    (dz := z - (1 + μ n s t / scale N p))
    (by positivity) ((div_le_one ha0).mpr ha) hδ (by linarith) hsq (by positivity) hM0
    (hcoef s (last u) t) (hcoef t (last v) s) ((hμ s t).trans (by nlinarith))
    (hmeans s (last u) t) (hmeans t (last v) s)
    ((hnorm s t).trans (le_mul_of_one_le_left hδ hM1)) (by
      have hid : 1 + μ n s t * (1 / scale N p) +
          (z - (1 + μ n s t / scale N p)) = z := by ring
      rw [hid]
      exact (hden s t).trans (le_abs_self z))
  have hq' : |a * b / z - (1 + μ (n + 1) u v / scale N p)| ≤
      quotientErrorConstant B K * δ := by
    have hxid : 1 + e * (1 / scale N p) + (a - (1 + e / scale N p)) = a := by ring
    have hyid : 1 + f * (1 / scale N p) + (b - (1 + f / scale N p)) = b := by ring
    have hzid : 1 + μ n s t * (1 / scale N p) + (z - (1 + μ n s t / scale N p)) = z := by ring
    rw [hxid, hyid, hzid] at hq
    have hμid : e + f - μ n s t = μ (n + 1) u v := (universal_edge_recursion u v).symm
    rw [hμid] at hq
    simpa only [quotientErrorConstant, div_eq_mul_inv, one_div, one_mul] using hq
  let U := templateSizes x.sizes q u
  let V := templateSizes x.sizes q v
  let u' : ℝ := (nextState x q).sizes u
  let v' : ℝ := (nextState x q).sizes v
  let R := U * V / (u' * v')
  have hu' : 0 < u' := hnpos u
  have hv' : 0 < v' := hnpos v
  have hfloor (w : History (n + 2)) :
      0 ≤ templateSizes x.sizes q w - ((nextState x q).sizes w : ℝ) ∧
        templateSizes x.sizes q w - ((nextState x q).sizes w : ℝ) ≤ 1 := by
    have hl := Nat.floor_le (templateSizes_nonneg x.sizes q w)
    have hh := Nat.lt_floor_add_one (templateSizes x.sizes q w)
    change 0 ≤ templateSizes x.sizes q w - (⌊templateSizes x.sizes q w⌋₊ : ℝ) ∧
      templateSizes x.sizes q w - (⌊templateSizes x.sizes q w⌋₊ : ℝ) ≤ 1
    constructor <;> linarith
  obtain ⟨hR0, hRupper, hRerror⟩ := rounded_product_ratio (by exact_mod_cast hN)
    (show 0 < 1 / (2 * B) by positivity) (hnlo u) (hnlo v) (hfloor u) (hfloor v)
  have hRup : R ≤ (1 + 2 * B) ^ 2 := by
    convert hRupper using 1
    field_simp
  have hRe : |R - 1| ≤ (4 * B + 4 * B ^ 2) * δ := by
    have hh : (2 / (1 / (2 * B)) + 1 / (1 / (2 * B)) ^ 2) / (N : ℝ) =
        (4 * B + 4 * B ^ 2) * (1 / N) := by field_simp; ring
    rw [hh] at hRerror
    exact hRerror.trans (mul_le_mul_of_nonneg_left hinv (by positivity))
  have htar : |1 + μ (n + 1) u v / scale N p| ≤ 1 + B := by
    calc
      _ ≤ |(1 : ℝ)| + |μ (n + 1) u v / scale N p| := abs_add_le _ _
      _ ≤ 1 + B := by
        rw [abs_one, abs_div, abs_of_pos ha0]
        exact add_le_add le_rfl (div_le_of_le_mul₀ ha0.le hB0.le
          ((hμ' u v).trans (le_mul_of_one_le_right hB0.le ha)))
  have hfinal := rounded_edge_error hR0 hRup hq' htar hRe hδ
    (show 0 ≤ quotientErrorConstant B K by unfold quotientErrorConstant; positivity)
    (by positivity) (by positivity)
  have hm0 : x.edges s t ≠ 0 := by
    have hz : 0 < z := by dsimp [z]; linarith [hden s t]
    exact (div_pos_iff.mp hz).elim (fun h => h.1.ne') (fun h => h.1.ne)
  have hid : (nextState x q).edges u v =
      ((p : ℝ) * u' * v') * (R * (a * b / z)) := by
    change templateEdges x.sizes x.edges q u v = _
    rw [templateEdges_relative_identity x.sizes x.edges q p p.property.1.ne' u v
      (hspos s).ne' (hspos t).ne' hm0]
    change (p : ℝ) * U * V * (a * b / z) =
      ((p : ℝ) * u' * v') * (U * V / (u' * v') * (a * b / z))
    field_simp [hu'.ne', hv'.ne']
  rw [hid, ← mul_sub, abs_mul, abs_of_pos (mul_pos (mul_pos p.property.1 hu') hv')]
  exact mul_le_mul_of_nonneg_left hfinal (mul_pos (mul_pos p.property.1 hu') hv').le

end MajorityDynamics.Idealized.Process
