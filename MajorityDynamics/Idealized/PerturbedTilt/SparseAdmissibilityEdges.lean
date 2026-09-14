import MajorityDynamics.Idealized.PerturbedTilt.AdmissibilityEdges
import MajorityDynamics.Idealized.PerturbedTilt.SparseGeometry

noncomputable section
open Filter Topology
open scoped BigOperators
namespace MajorityDynamics.Idealized.PerturbedTilt
open Universal LinearResponse
open Binomial.Approximation (SparseRange scale)
set_option maxHeartbeats 3000000

theorem product_error_sparse {a b x y H D : ℝ}
    (ha : |a| ≤ H) (hy : |y| ≤ H) (hax : |a - x| ≤ D) (hby : |b - y| ≤ D)
    (hH : 0 ≤ H) (hD : 0 ≤ D) : |a * b - x * y| ≤ 2 * H * D := by
  have h1 := mul_le_mul ha hby (abs_nonneg _) hH
  have h2 := mul_le_mul hax hy (abs_nonneg _) hD
  calc
    |a * b - x * y| = |a * (b - y) + (a - x) * y| := by congr 1; ring
    _ ≤ |a| * |b - y| + |a - x| * |y| := by simpa [abs_mul] using abs_add_le (a * (b-y)) ((a-x)*y)
    _ ≤ 2 * H * D := by nlinarith

theorem finite_bound_sparse {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ i, |f i| ≤ A := by
  classical
  have hsum : 0 ≤ ∑ i, |f i| := by positivity
  refine ⟨1 + ∑ i, |f i|, by linarith, ?_⟩
  intro i
  have := Finset.single_le_sum (fun j _ => abs_nonneg (f j)) (Finset.mem_univ i)
  linarith


theorem faithful_edge_bounds_sparse (θ T δ : ℝ) (hθlo : 1 / 2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hδ : 0 < δ) (n ell : ℕ)
    (D : ℕ) (hDlt : n + 1 < D) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ p : Binomial.Probability, SparseRange θ T N p → ResponseSmall θ N p n →
      ∀ a : Process.Data, Process.Specification N p D ell a →
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ η : History (n + 1) → ℤ, ∀ e : History (n + 1) → History (n + 1) → ℤ,
      FaithfulNumericalData N (p : ℝ) T δ τ a n η e →
      ∀ s t, |(e s t : ℝ) - (p : ℝ) * (η s : ℝ) * (η t : ℝ)| ≤ K * Local.edgeScale N p ∧
        0 < (e s t : ℝ) := by
  obtain ⟨A, hA, hν⟩ := finite_bound_sparse (ν n)
  obtain ⟨M, hM, hμ⟩ := finite_bound_sparse (fun st : History (n+1) × History (n+1) => μ n st.1 st.2)
  obtain ⟨E, hE, hε⟩ := finite_bound_sparse (fun s => ε n s / ν n s)
  obtain ⟨c, hc, hcν⟩ := RowLimits.finite_common_positive (ν n) (ν_positive n)
  let U := comparisonConstant n T
  let L := 4 * A^2 * (M + 1)
  let J := 4 * A^2 + L
  let K := 1 + L + T * (1 + 2 * E * J) + 8 * A * U
  have hT0 : 0 < T := by linarith
  have hU : 0 < U := hT0.trans_le (comparisonConstant_ge n hT0.le)
  have hL : 0 < L := by dsimp [L]; positivity
  have hJ : 0 < J := by dsimp [J]; positivity
  have hK : 1 ≤ K := by
    have : 0 ≤ L + T * (1 + 2 * E * J) + 8 * A * U := by positivity
    dsimp [K]
    linarith
  refine ⟨K, hK, ?_⟩
  filter_upwards [faithful_geometry_sparse θ T δ hθlo hθhi hT hδ n ell D hDlt,
    eventually_basic_sparse θ T hθlo hθhi hT,
    eventually_small_sparse θ T hθlo hθhi hT n ell,
    eventually_rpow_neg_le (sparseResponseRate θ) 1 (sparseResponseRate_pos hθhi) zero_lt_one,
    eventually_rpow_neg_le δ 1 hδ zero_lt_one,
    RowLimits.density_scale_lower_power_sparse θ T (32 * K / c^2 + 1) 0 hθhi hT0 (by positivity)]
    with N hgeo hbasic hsmall hpow hδpow hscale
  intro p hp hsub a ha τ hτ hτT η e hf s t
  obtain ⟨hη, hcast, hclose, hg⟩ := hgeo p hp hsub a ha τ hτ hτT η e hf
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr hbasic.1
  have hp0 := p.property.1
  let S := Real.sqrt ((p : ℝ) * N)
  let B := betaScale N (p : ℝ) n
  let P := (p : ℝ) * (N : ℝ)^2
  let Q := P / S
  have hS : 0 < S := by dsimp [S]; positivity
  have hS1 : 1 ≤ S := (hbasic.2.2 p hp).1
  have hB : 0 ≤ B := by dsimp [B, betaScale]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have hQ : 0 < Q := div_pos hP hS
  have hlog : 1 ≤ Real.log (N : ℝ)^ell := one_le_pow₀ (by linarith [hbasic.2.1])
  have hlogS : Real.log (N : ℝ)^ell / S ≤ 1 := (hsmall p hp hsub).2.2.1.trans hpow
  have hBS : B * S ≤ 1 := by
    have hh := (hsmall p hp hsub).2.2.2
    have hh' := mul_le_mul_of_nonneg_left hlog (mul_nonneg hB hS.le)
    dsimp [B, S] at *
    nlinarith
  have hBP : B * P ≤ Q := (le_div_iff₀ hS).mpr (by nlinarith [mul_le_mul_of_nonneg_right hBS hP.le])
  have hQP : Q ≤ P := (div_le_self hP.le hS1)
  have hsiz (u) : |(η u : ℝ) - ((a.state n).sizes u : ℝ)| ≤ U * N * B := by
    have hid : sizeScale N (p : ℝ) n = (N : ℝ) * B := by
      dsimp [sizeScale, B, betaScale]
      have hs := Real.sq_sqrt hN.le
      field_simp
      nlinarith
    simpa only [hid, mul_assoc] using hclose u
  have hru (u) : 0 ≤ ((a.state n).sizes u : ℝ) ∧ ((a.state n).sizes u : ℝ) ≤ 2*A*N := by
    refine ⟨Nat.cast_nonneg _, ?_⟩
    have hv := (le_abs_self (ν n u)).trans (hν u)
    nlinarith [hg.ref_upper u]
  have hsu (u) : 0 ≤ (η u : ℝ) ∧ (η u : ℝ) ≤ 4*A*N := by
    refine ⟨by exact_mod_cast (hη u).le, ?_⟩
    have hh := hg.sizes_upper u
    rw [hcast u] at hh
    have hv := (le_abs_self (ν n u)).trans (hν u)
    nlinarith
  have hab : ((a.state n).sizes s : ℝ) * ((a.state n).sizes t : ℝ) ≤ 4*A^2*(N : ℝ)^2 := by
    have := mul_le_mul (hru s).2 (hru t).2 (hru t).1 (by positivity : 0 ≤ 2*A*N)
    nlinarith
  have hmean := (ha.estimates n (Nat.lt_of_succ_lt hDlt)).edges s t
  have hmean' : |(a.state n).edges s t - (p : ℝ) * (a.state n).sizes s * (a.state n).sizes t| ≤ L * Q := by
    have hrem : Real.log (N : ℝ)^ell / ((p : ℝ)*N) ≤ 1/S := by
      have hs : S^2 = (p : ℝ)*N := Real.sq_sqrt (by positivity)
      apply (div_le_iff₀ (mul_pos hp0 hN)).mpr
      have hh := (div_le_iff₀ hS).mp hlogS
      rw [← hs]
      nlinarith [one_div_mul_cancel hS.ne']
    have hμS : |μ n s t / S| ≤ M/S := by
      rw [abs_div, abs_of_pos hS]
      exact div_le_div_of_nonneg_right (hμ (s,t)) hS.le
    have htri := abs_sub_le ((a.state n).edges s t)
      ((p : ℝ) * (a.state n).sizes s * (a.state n).sizes t * (1 + μ n s t/S))
      ((p : ℝ) * (a.state n).sizes s * (a.state n).sizes t)
    have hid : (p : ℝ) * (a.state n).sizes s * (a.state n).sizes t * (1 + μ n s t/S) -
        (p : ℝ) * (a.state n).sizes s * (a.state n).sizes t =
        (p : ℝ) * (a.state n).sizes s * (a.state n).sizes t * (μ n s t/S) := by ring
    rw [hid, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (p : ℝ) * (a.state n).sizes s * (a.state n).sizes t)] at htri
    have h1 := mul_le_mul_of_nonneg_left hrem (by positivity : 0 ≤ (p : ℝ) * (a.state n).sizes s * (a.state n).sizes t)
    have h2 := mul_le_mul_of_nonneg_left hμS (by positivity : 0 ≤ (p : ℝ) * (a.state n).sizes s * (a.state n).sizes t)
    have h3 := mul_le_mul_of_nonneg_left hab (show 0 ≤ (p : ℝ)*(M+1)/S by positivity)
    dsimp [L, Q, P, S] at htri hmean h1 h2 h3 ⊢
    simp only [div_eq_mul_inv] at htri hmean h1 h2 h3 ⊢
    nlinarith only [htri, hmean, h1, h2, h3]
  have hm : |(a.state n).edges s t| ≤ J * P := by
    have hh := abs_sub_le ((a.state n).edges s t) ((p : ℝ)*(a.state n).sizes s*(a.state n).sizes t) 0
    simp only [sub_zero, abs_of_nonneg (by positivity : 0 ≤ (p : ℝ)*(a.state n).sizes s*(a.state n).sizes t)] at hh
    have h1 := mul_le_mul_of_nonneg_left hab hp0.le
    have h2 := mul_le_mul_of_nonneg_left hQP hL.le
    dsimp [J, P] at *
    nlinarith
  have he : |(e s t : ℝ) - (a.state n).edges s t| ≤ T * (1 + 2*E*J) * Q := by
    have hτ0 : 0 ≤ τ := ((inv_pos.mpr hT0).trans_le hτ).le
    have hr : |ε n s / ν n s + ε n t / ν n t| ≤ 2*E :=
      (abs_add_le _ _).trans (by linarith [hε s, hε t])
    have htri := abs_sub_le (e s t : ℝ)
      ((a.state n).edges s t * (1 + τ*B*(ε n s/ν n s+ε n t/ν n t))) ((a.state n).edges s t)
    have hid : (a.state n).edges s t * (1 + τ*B*(ε n s/ν n s+ε n t/ν n t)) - (a.state n).edges s t =
      (a.state n).edges s t * τ*B*(ε n s/ν n s+ε n t/ν n t) := by ring
    rw [hid, abs_mul, abs_mul, abs_mul, abs_of_nonneg hτ0, abs_of_nonneg hB] at htri
    have h1 := mul_le_mul hm hτT hτ0 (by positivity : 0 ≤ J*P)
    have h2 := mul_le_mul (mul_le_mul_of_nonneg_right h1 hB) hr (abs_nonneg _) (by positivity : 0 ≤ J*P*T*B)
    have h3 := mul_le_mul_of_nonneg_left hδpow (show 0 ≤ T*B*P by positivity)
    have h4 := mul_le_mul_of_nonneg_left hBP (show 0 ≤ T*(1+2*E*J) by positivity)
    have hfe := hf.edges s t
    dsimp [B, P] at *
    nlinarith
  have hprod : |(p : ℝ)*(a.state n).sizes s*(a.state n).sizes t - (p : ℝ)*(η s : ℝ)*(η t : ℝ)| ≤ 8*A*U*Q := by
    have herr := product_error_sparse
      (show |((a.state n).sizes s : ℝ)| ≤ 4*A*N by rw [abs_of_nonneg (hru s).1]; nlinarith [(hru s).2])
      (show |(η t : ℝ)| ≤ 4*A*N by rw [abs_of_nonneg (hsu t).1]; exact (hsu t).2)
      (show |((a.state n).sizes s : ℝ) - (η s : ℝ)| ≤ U*N*B by simpa [abs_sub_comm] using hsiz s)
      (show |((a.state n).sizes t : ℝ) - (η t : ℝ)| ≤ U*N*B by simpa [abs_sub_comm] using hsiz t)
      (by positivity) (by positivity)
    have hh := mul_le_mul_of_nonneg_left herr hp0.le
    have hh2 := mul_le_mul_of_nonneg_left hBP (show 0 ≤ 8*A*U by positivity)
    rw [show (p : ℝ)*(a.state n).sizes s*(a.state n).sizes t - (p : ℝ)*(η s : ℝ)*(η t : ℝ) =
      (p : ℝ)*(((a.state n).sizes s : ℝ)*((a.state n).sizes t : ℝ)-(η s : ℝ)*(η t : ℝ)) by ring,
      abs_mul, abs_of_pos hp0]
    dsimp [P] at *
    nlinarith
  have hbound : |(e s t : ℝ) - (p : ℝ)*(η s : ℝ)*(η t : ℝ)| ≤ K*Q := by
    have h1 := abs_sub_le (e s t : ℝ) ((a.state n).edges s t) ((p : ℝ)*(a.state n).sizes s*(a.state n).sizes t)
    have h2 := abs_sub_le (e s t : ℝ) ((p : ℝ)*(a.state n).sizes s*(a.state n).sizes t) ((p : ℝ)*(η s : ℝ)*(η t : ℝ))
    dsimp [K]
    linarith
  refine ⟨by simpa only [Q, P, S, Local.edgeScale, mul_comm (p : ℝ) ((N : ℝ)^2)] using hbound, ?_⟩
  have hlo (u) : c*N/4 ≤ (η u : ℝ) := by
    have hh := hg.sizes_lower u
    rw [hcast u] at hh
    nlinarith [hcν u]
  have hprodlo := mul_le_mul (hlo s) (hlo t) (by positivity : 0 ≤ c*N/4) (hsu s).1
  have hscale' : 32*K/c^2 + 1 ≤ S := by simpa [scale, S] using hscale p hp
  have hsmallK : K / S < c^2/16 := by
    apply (div_lt_iff₀ hS).mpr
    have hcc : 0 < c^2 := sq_pos_of_pos hc
    have hh := mul_le_mul_of_nonneg_left hscale' hcc.le
    field_simp at hh
    nlinarith
  have hh := mul_lt_mul_of_pos_right hsmallK hP
  have hh2 := mul_le_mul_of_nonneg_left hprodlo hp0.le
  have hh3 := (abs_le.mp hbound).1
  dsimp [Q, P] at hh hh3
  simp only [div_eq_mul_inv] at hh hh3
  nlinarith only [hh, hh2, hh3]

end MajorityDynamics.Idealized.PerturbedTilt

