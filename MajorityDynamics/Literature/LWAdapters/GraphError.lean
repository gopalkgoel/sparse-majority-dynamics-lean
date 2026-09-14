import MajorityDynamics.Literature.LWAdapters.GraphEnumeration
import MajorityDynamics.Literature.LWFormal.Final16
import MajorityDynamics.Literature.EdgeProbabilities.Basic

noncomputable section
open scoped BigOperators
namespace MajorityDynamics.Literature.LWAdapters

theorem corrected_graph_error {n m : ℕ} {α C θ : ℝ} (d : Fin n → ℕ)
    (hd : LW.InD α n m d) (hα : α < 3/5)
    (hn : (4:ℝ) ≤ n) (hD : 1 ≤ (2*m/n : ℝ))
    (hDn : (2*m/n : ℝ) ≤ (n:ℝ)/4) (hC : 0 ≤ C)
    (hθ : |θ| ≤ C*LW.err16 α n (2*m/n)) (a b : Fin n) :
    |LW.edgeMain n m d a b * (LW.edgeBracket n m d a b + θ) -
      EdgeProbabilities.graphApproximation n m (d a) (d b)| ≤
        (8*(8+C)) * ((2*m/n : ℝ)/(n:ℝ)^2) := by
  let D : ℝ := 2*m/n
  let x : ℝ := D^α
  let Δ : ℝ := (d a : ℝ)+d b-2*D
  have hn0 : (0:ℝ) < n := by linarith
  have hD0 : 0 < D := by dsimp [D]; linarith
  have hnm1 : (0:ℝ) < n-1 := by linarith
  have hden : 0 < (n:ℝ)-1-D := by dsimp [D]; linarith
  have hx0 : 0 ≤ x := Real.rpow_nonneg hD0.le _
  have hxD : x ≤ D := by
    calc
      _ ≤ D^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hD (by linarith)
      _ = D := Real.rpow_one _
  have hx3 : x^3 ≤ D^2 := by
    calc
      _ = D^(α*3) := by rw [Real.rpow_mul hD0.le]; norm_num [x]
      _ ≤ D^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hD (by linarith)
      _ = D^2 := Real.rpow_two _
  have hδ : |Δ| ≤ 2*x := by
    have ha := hd.2 a
    have hb := hd.2 b
    calc
      _ = |((d a : ℝ)-D)+((d b : ℝ)-D)| := by congr 1; dsimp [Δ]; ring
      _ ≤ |(d a : ℝ)-D|+|(d b : ℝ)-D| := abs_add_le _ _
      _ ≤ 2*x := by dsimp [D,x] at *; linarith
  have hav := average_eq d hd.1
  have hv0 : 0 ≤ LW.var d := by unfold LW.var; positivity
  have hv : LW.var d ≤ x^2 := by
    unfold LW.var
    rw [hav]
    apply (div_le_iff₀ hn0).mpr
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      sq_le_sq' (abs_le.mp (hd.2 i)).1 (abs_le.mp (hd.2 i)).2)
    simpa [x,D,DegreeEnumeration.graphAverage,mul_comm] using hh
  have hδv : |Δ| *LW.var d ≤ 2*D^2 := by
    have hh := mul_le_mul hδ hv hv0 (by positivity : 0 ≤ 2*x)
    nlinarith [hx3]
  have hδD : |Δ| ≤ 2*D := hδ.trans (by nlinarith)
  have ht1 : |Δ*((n:ℝ)-1)*LW.var d / (D^2*n*((n:ℝ)-1-D))| ≤ 4/(n:ℝ) := by
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hnm1.le, abs_of_nonneg hv0,
      abs_of_pos (by positivity : 0 < D^2*n*((n:ℝ)-1-D))]
    apply (div_le_div_iff₀ (by positivity : 0 < D^2*n*((n:ℝ)-1-D)) hn0).mpr
    have hh := mul_le_mul_of_nonneg_right hδv (by positivity : 0 ≤ ((n:ℝ)-1)*n)
    have hscale : (n:ℝ) ≤ 2*((n:ℝ)-1-D) := by dsimp [D]; linarith
    have hhh := mul_le_mul_of_nonneg_left hscale (by positivity : 0 ≤ 2*D^2*n)
    nlinarith
  have ht2 : |Δ/(D*((n:ℝ)-1))| ≤ 4/(n:ℝ) := by
    rw [abs_div, abs_of_pos (mul_pos hD0 hnm1)]
    apply (div_le_div_iff₀ (mul_pos hD0 hnm1) hn0).mpr
    have hh := mul_le_mul_of_nonneg_right hδD hn0.le
    have hh' := mul_le_mul_of_nonneg_left (by linarith : (n:ℝ) ≤ 2*((n:ℝ)-1)) hD0.le
    nlinarith
  have ht : |θ| ≤ C/(n:ℝ) := by
    apply hθ.trans
    have hp : D^(4*α-3) ≤ 1 := by
      calc
        _ ≤ D^(0:ℝ) := Real.rpow_le_rpow_of_exponent_le hD (by linarith)
        _ = 1 := Real.rpow_zero _
    exact (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hp hn0.le) hC).trans_eq (by ring)
  have hbr : |LW.edgeBracket n m d a b + θ - LW.edgeBracket0 n m d a b| ≤ (8+C)/(n:ℝ) := by
    calc
      _ = |(Δ*((n:ℝ)-1)*LW.var d/(D^2*n*((n:ℝ)-1-D)) + Δ/(D*((n:ℝ)-1))) + θ| := by
        congr 1; dsimp [LW.edgeBracket,Δ,D]; ring
      _ ≤ |Δ*((n:ℝ)-1)*LW.var d/(D^2*n*((n:ℝ)-1-D))| + |Δ/(D*((n:ℝ)-1))| + |θ| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ (8+C)/(n:ℝ) := (add_le_add (add_le_add ht1 ht2) ht).trans_eq (by ring)
  have ha : (d a : ℝ) ≤ 2*D := by have hh := (abs_le.mp (hd.2 a)).2; dsimp [D,x] at *; linarith
  have hb : (d b : ℝ) ≤ 2*D := by have hh := (abs_le.mp (hd.2 b)).2; dsimp [D,x] at *; linarith
  have hp0 : 0 ≤ LW.edgeMain n m d a b := by unfold LW.edgeMain; positivity
  have hp : LW.edgeMain n m d a b ≤ 8*D/n := by
    change (d a : ℝ)*d b/(D*((n:ℝ)-1)) ≤ _
    apply (div_le_div_iff₀ (mul_pos hD0 hnm1) hn0).mpr
    have hh := mul_le_mul ha hb (Nat.cast_nonneg _) (by positivity : 0 ≤ 2*D)
    have hh' := mul_le_mul_of_nonneg_right hh hn0.le
    have hnn := mul_le_mul_of_nonneg_left (by linarith : (n:ℝ) ≤ 2*((n:ℝ)-1)) (by positivity : 0 ≤ 4*D^2)
    nlinarith
  have heq : EdgeProbabilities.graphApproximation n m (d a) (d b) =
      LW.edgeMain n m d a b * LW.edgeBracket0 n m d a b := rfl
  rw [heq, ← mul_sub, abs_mul, abs_of_nonneg hp0]
  calc
    _ ≤ (8*D/n)*((8+C)/n) := mul_le_mul hp hbr (abs_nonneg _) (by positivity)
    _ = _ := by dsimp [D]; ring

end MajorityDynamics.Literature.LWAdapters
