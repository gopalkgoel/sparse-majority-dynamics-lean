import MajorityDynamics.Probability.NeighborhoodBulk.ResidualData

noncomputable section
open Filter
open scoped Classical
namespace MajorityDynamics.Probability.NeighborhoodBulk
open FixedDegreeSampling
open MajorityDynamics.Combinatorics.DegreeRatios
open MajorityDynamics.Literature.DegreeEnumeration

def CenteredControl {V : Type*} (d : V → ℕ) (μ x L : ℝ) : Prop :=
  |μ - x| ≤ Real.sqrt x * L ∧ x / 2 ≤ μ ∧
    ∀ i, |(d i : ℝ) - μ| ≤ 2 * (Real.sqrt x * L)

theorem natural_degree_room (n d : ℕ) (p L : ℝ) (hn : 4 ≤ n)
    (hp : 0 < p) (hp16 : p ≤ 1 / 16) (hL : 1 ≤ L)
    (hs : 2 * L ≤ Real.sqrt (p * n)) (hd : |(d : ℝ) - p * n| ≤ Real.sqrt (p * n) * L) :
    2 ≤ d ∧ d ≤ n - 2 := by
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : 0 ≤ p * n := by positivity
  have hsq := Real.sq_sqrt hx
  have hs0 := Real.sqrt_nonneg (p * n)
  have hdev : Real.sqrt (p * n) * L ≤ p * n / 2 := by
    have hh := mul_le_mul_of_nonneg_left hs hs0
    nlinarith
  have hx4 : 4 ≤ p * n := by nlinarith
  have hpN := mul_le_mul_of_nonneg_right hp16 (by positivity : (0 : ℝ) ≤ n)
  constructor
  · have h : (2 : ℝ) ≤ d := by linarith [(abs_le.mp hd).1]
    exact_mod_cast h
  · have h : (d : ℝ) ≤ (n : ℝ) - 2 := by linarith [(abs_le.mp hd).2]
    have h' : (d : ℝ) ≤ (n - 2 : ℕ) := by simpa only [Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_ofNat] using h
    exact_mod_cast h'

theorem deletion_centered_bounds {V : Type*} [Fintype V] [Nonempty V]
    (d : V → ℝ) (x μ L : ℝ) (hx : 0 < x) (hL : 1 ≤ L)
    (hs : 4 * L ≤ Real.sqrt x) (hpow : 8 * L ≤ x ^ (7 / 12 - 1 / 2 : ℝ))
    (hsum : ∑ i, d i = Fintype.card V * μ)
    (hd : ∀ i, |d i - x| ≤ Real.sqrt x * L + 1) :
    |μ - x| ≤ Real.sqrt x * (2 * L) ∧ x / 2 ≤ μ ∧
      (∀ i, |d i - μ| ≤ 2 * (Real.sqrt x * (2 * L))) ∧
      ∀ i, |d i - μ| ≤ μ ^ (7 / 12 : ℝ) := by
  have hs0 := Real.sqrt_nonneg x
  have hB : Real.sqrt x * L + 1 ≤ Real.sqrt x * (2 * L) := by nlinarith
  have hc := centered_deviation_bound d x μ (Real.sqrt x * (2 * L)) hsum
    (fun i => (hd i).trans hB)
  have hav := average_ge_half hx.le hc.1 (by linarith : 2 * (2 * L) ≤ Real.sqrt x)
  refine ⟨hc.1, hav, hc.2, fun i => ?_⟩
  calc
    _ ≤ 2 * (Real.sqrt x * (2 * L)) := hc.2 i
    _ ≤ (x / 2) ^ (7 / 12 : ℝ) := sqrt_log_le_half_rpow hx (by linarith) (by norm_num)
      (by nlinarith : 4 * (2 * L) ≤ x ^ (7 / 12 - 1 / 2 : ℝ))
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hav (by norm_num)

theorem eventually_graph_degree_room (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, DensityWindow θ T n p →
      ∀ (m : ℤ) (d : Fin n → ℤ), GraphInput T n p m d →
        ∀ i, 2 ≤ (d i).toNat ∧ (d i).toNat ≤ n - 2 := by
  filter_upwards [eventually_large_parameters θ T hθlo hθhi hT,
    eventually_ge_atTop (4 : ℕ),
    eventually_density_log_le_rpow θ T 2 (1 / 2) hθhi (by linarith)
      (by norm_num) (by norm_num)] with n hlarge hn hsmall
  intro p hp m d hd i
  have hl := hlarge p hp
  have hx : 0 < p * n := mul_pos hl.2.2.1 (by exact_mod_cast (by omega : 0 < n))
  have hs : 2 * Real.log n ≤ Real.sqrt (p * n) := by simpa only [Real.sqrt_eq_rpow] using hsmall p hp
  apply natural_degree_room n (d i).toNat p (Real.log n) hn hl.2.2.1 hl.2.2.2.1 hl.2.1 hs
  have he : ((d i).toNat : ℝ) = (d i : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (hd.1 i).1
  rw [he]
  exact (standardizedDegree_bound_iff p n (d i) (Real.log n) hx).mp (hd.2.2.2 i)

theorem eventually_graph_residual_regular (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, DensityWindow θ T n p →
      ∀ (m : ℤ) (d : Fin n → ℤ), GraphInput T n p m d →
        ∀ (v : Fin n) (S : Finset (Fin n)), v ∉ S → S.card = (d v).toNat →
          graphAdmissible (fun i => (d i).toNat) v S ∧
            GraphSourceData (7 / 12) (n - 1) (m.toNat - (d v).toNat)
              (graphResidualFin (fun i => (d i).toNat) v S) ∧
            CenteredControl (graphResidualFin (fun i => (d i).toNat) v S)
              (graphAverage (n - 1) (m.toNat - (d v).toNat)) (p * n) (2 * Real.log n) := by
  filter_upwards [eventually_large_parameters θ T hθlo hθhi hT,
    eventually_ge_atTop (3 : ℕ), eventually_graph_degree_room θ T hθlo hθhi hT,
    eventually_density_log_le_rpow θ T 4 (1 / 2) hθhi (by linarith) (by norm_num) (by norm_num),
    eventually_density_log_le_rpow θ T 8 (7 / 12 - 1 / 2) hθhi (by linarith) (by norm_num)
      (by norm_num)] with n hlarge hn hroom hsmall hspread
  intro p hp m d hd v S hv hS
  have hl := hlarge p hp
  have hx : 0 < p * n := mul_pos hl.2.2.1 (by exact_mod_cast (by omega : 0 < n))
  have hR : graphAdmissible (fun i => (d i).toNat) v S :=
    ⟨hv, hS, fun i _ => (show 1 ≤ 2 by omega).trans (hroom p hp m d hd i).1⟩
  have hs := graphResidualFin_sum (fun i => (d i).toNat) v S hR m.toNat (graph_input_nat_sum hd).2
  have hdev : ∀ i, |((d i).toNat : ℝ) - p * n| ≤ Real.sqrt (p * n) * Real.log n := by
    intro i
    have he : ((d i).toNat : ℝ) = (d i : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (hd.1 i).1
    rw [he]
    exact (standardizedDegree_bound_iff p n (d i) (Real.log n) hx).mp (hd.2.2.2 i)
  have hdev' := graphResidualFin_deviation (fun i => (d i).toNat) v S hR
    (p * n) (Real.sqrt (p * n) * Real.log n) hdev
  have : Nonempty (Fin (n - 1)) := Fin.pos_iff_nonempty.mp (by omega)
  have hc := deletion_centered_bounds
    (fun i => (graphResidualFin (fun j => (d j).toNat) v S i : ℝ)) (p * n)
    (graphAverage (n - 1) (m.toNat - (d v).toNat)) (Real.log n) hx hl.2.1
    (by simpa only [Real.sqrt_eq_rpow] using hsmall p hp) (hspread p hp) ?_ hdev'
  · refine ⟨hR, ⟨?_, hs, hc.2.2.2⟩, hc.1, hc.2.1, hc.2.2.1⟩
    intro i
    have hi := (hroom p hp m d hd ((remainingEquiv v).symm i)).2
    change (d ((remainingEquiv v).symm i)).toNat - _ ≤ n - 1 - 1
    omega
  · simp only [Fintype.card_fin, graphAverage]
    have hN : 0 < n - 1 := by omega
    rw [mul_div_cancel₀ _ (by exact_mod_cast hN.ne' : ((n - 1 : ℕ) : ℝ) ≠ 0)]
    exact_mod_cast hs

theorem eventually_graph_residual_source (θ T : ℝ)
    (hθlo : 1 / 2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, DensityWindow θ T n p →
      ∀ (m : ℤ) (d : Fin n → ℤ), GraphInput T n p m d →
        ∀ (v : Fin n) (S : Finset (Fin n)), v ∉ S → S.card = (d v).toNat →
          graphAdmissible (fun i => (d i).toNat) v S ∧
            GraphSourceData (7 / 12) (n - 1) (m.toNat - (d v).toNat)
              (graphResidualFin (fun i => (d i).toNat) v S) := by
  filter_upwards [eventually_graph_residual_regular θ T hθlo hθhi hT] with n hn
  intro p hp m d hd v S hv hS
  exact ⟨(hn p hp m d hd v S hv hS).1, (hn p hp m d hd v S hv hS).2.1⟩

end MajorityDynamics.Probability.NeighborhoodBulk
