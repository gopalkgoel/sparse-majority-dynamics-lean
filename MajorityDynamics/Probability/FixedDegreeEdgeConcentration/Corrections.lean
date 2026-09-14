import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Regime

noncomputable section
open scoped BigOperators
namespace MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Numerics

theorem variance_le_window_sq {V : Type*} [Fintype V] {d : V → ℕ} {D r : ℝ}
    (hcard : 0 < Fintype.card V) (_hr : 0 ≤ r) (hd : ∀ v, |(d v:ℝ)-D| ≤ r) :
    0 ≤ Literature.EdgeProbabilities.degreeVariance d D ∧
      Literature.EdgeProbabilities.degreeVariance d D ≤ r^2 := by
  have hc : (0:ℝ) < Fintype.card V := by exact_mod_cast hcard
  unfold Literature.EdgeProbabilities.degreeVariance
  constructor
  · positivity
  · apply (div_le_iff₀ hc).mpr
    calc
      _ ≤ ∑ _v : V, r^2 := Finset.sum_le_sum (fun v _ => (sq_abs ((d v:ℝ)-D)) ▸
        (pow_le_pow_left₀ (abs_nonneg _) (hd v) 2))
      _ = _ := by simp [mul_comm]

/-- The source graph correction, retaining both exact `n-1` denominators. -/
theorem graph_correction {n D a b w r ε K : ℝ}
    (hn : 2 ≤ n) (hD : 0 < D) (hden : n/2 ≤ n-1-D)
    (hw : 0 ≤ w) (hweight : a*b/(D*n) = w)
    (ha : |a-D| ≤ r) (hb : |b-D| ≤ r) (hr : 0 ≤ r)
    (hK : 0 ≤ K) (hε : 0 ≤ ε) (hsize : 1/n ≤ ε)
    (hspread : r^2 ≤ K*ε*D*n) :
    |a*b/(D*(n-1))*(1-(a-D)*(b-D)/(D*(n-1-D)))-w|
      ≤ (2+4*K)*ε*w := by
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n-1 := by linarith
  have hd0 : 0 < n-1-D := by linarith
  have hprod : |(a-D)*(b-D)| ≤ r^2 := by
    rw [abs_mul]
    simpa [pow_two] using mul_le_mul ha hb (abs_nonneg _) hr
  have hq : |(a-D)*(b-D)/(D*(n-1-D))| ≤ 2*K*ε := by
    rw [abs_div, abs_of_pos (mul_pos hD hd0)]
    apply (div_le_iff₀ (mul_pos hD hd0)).mpr
    have hh := mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ 2*K*ε*D)
    nlinarith [hprod.trans hspread]
  have hratio : n/(n-1) ≤ 2 := by apply (div_le_iff₀ hn1).mpr; linarith
  have herr : 1/(n-1) ≤ 2*ε := by
    have hh : 1/(n-1) ≤ 2/n := by
      apply (div_le_div_iff₀ hn1 hn0).mpr
      linarith
    exact hh.trans (by simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hsize (show (0:ℝ) ≤ 2 by norm_num))
  have heq : a*b/(D*(n-1))*(1-(a-D)*(b-D)/(D*(n-1-D)))-w =
      w/(n-1)-w*(n/(n-1))*((a-D)*(b-D)/(D*(n-1-D))) := by
    rw [← hweight]
    field_simp
    ring
  rw [heq]
  calc
    _ ≤ |w/(n-1)| + |w*(n/(n-1))*((a-D)*(b-D)/(D*(n-1-D)))| := abs_sub _ _
    _ = w/(n-1) + w*(n/(n-1))*|(a-D)*(b-D)/(D*(n-1-D))| := by
      rw [abs_of_nonneg (by positivity), abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ w*(2*ε) + (w*2)*(2*K*ε) := by
      have h₁ := mul_le_mul_of_nonneg_left herr hw
      have h₂ := mul_le_mul (mul_le_mul_of_nonneg_left hratio hw) hq
        (abs_nonneg _) (by positivity : 0 ≤ w*2)
      simpa [div_eq_mul_inv, mul_assoc] using add_le_add h₁ h₂
    _ = _ := by ring

/-- The two empirical variance corrections in the bipartite source are both included. -/
theorem bipartite_correction {a b s t m ell n va vb r : ℝ}
    (hs : 0 < s) (ht : 0 < t)
    (hm : 0 < m-t*s) (he : 0 < ell-t) (hn : 0 < n-s)
    (hr : 0 ≤ r) (ha : |a-s| ≤ r) (hb : |b-t| ≤ r)
    (hva : 0 ≤ va) (hvau : va ≤ r^2) (hvb : 0 ≤ vb) (hvbu : vb ≤ r^2) :
    |(1-(a-s)*(b-t)/(m-t*s)+(a-s)*vb/(t*s*(ell-t))+
        (b-t)*va/(t*s*(n-s)))-1| ≤
      r^2/(m-t*s) + r^3/(t*s*(ell-t)) + r^3/(t*s*(n-s)) := by
  have h₁ : |(a-s)*(b-t)/(m-t*s)| ≤ r^2/(m-t*s) := by
    rw [abs_div, abs_of_pos hm, abs_mul]
    exact div_le_div_of_nonneg_right (by simpa [pow_two] using mul_le_mul ha hb (abs_nonneg _) hr) hm.le
  have h₂ : |(a-s)*vb/(t*s*(ell-t))| ≤ r^3/(t*s*(ell-t)) := by
    rw [abs_div, abs_of_pos (mul_pos (mul_pos ht hs) he), abs_mul, abs_of_nonneg hvb]
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc
      _ ≤ r*r^2 := mul_le_mul ha hvbu hvb hr
      _ = _ := by ring
  have h₃ : |(b-t)*va/(t*s*(n-s))| ≤ r^3/(t*s*(n-s)) := by
    rw [abs_div, abs_of_pos (mul_pos (mul_pos ht hs) hn), abs_mul, abs_of_nonneg hva]
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc
      _ ≤ r*r^2 := mul_le_mul hb hvau hva hr
      _ = _ := by ring
  have heq : (1-(a-s)*(b-t)/(m-t*s)+(a-s)*vb/(t*s*(ell-t))+
      (b-t)*va/(t*s*(n-s)))-1 =
      -(a-s)*(b-t)/(m-t*s)+(a-s)*vb/(t*s*(ell-t))+(b-t)*va/(t*s*(n-s)) := by ring
  rw [heq]
  calc
    _ ≤ |-(a-s)*(b-t)/(m-t*s)+(a-s)*vb/(t*s*(ell-t))| +
        |(b-t)*va/(t*s*(n-s))| := abs_add_le _ _
    _ ≤ (|-(a-s)*(b-t)/(m-t*s)|+|(a-s)*vb/(t*s*(ell-t))|)+
        |(b-t)*va/(t*s*(n-s))| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ _ := by rw [neg_mul, neg_div, abs_neg]; linarith

/-- The exact exponent identity used by the original `4/7` spread. -/
theorem spread_power_identity {x : ℝ} (hx : 0 < x) :
    (x^((4:ℝ)/7))^2 = x^((1:ℝ)/7)*x := by
  calc
    _ = x^((8:ℝ)/7) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
    _ = x^((1:ℝ)/7+1) := by congr 1; norm_num
    _ = _ := by rw [Real.rpow_add hx, Real.rpow_one]

/-- A variance correction is controlled by the square spread when the spread
is at most the other side's mean. -/
theorem variance_correction_bound {r s t ell m : ℝ}
    (_hr : 0 ≤ r) (hs : 0 < s) (ht : 0 < t) (hm : 0 < m)
    (hmean : s*ell = m) (hden : ell/2 ≤ ell-t) (hrt : r ≤ t) :
    r^3/(t*s*(ell-t)) ≤ 2*r^2/m := by
  have hell : 0 < ell := by nlinarith
  have hd : 0 < t*s*(ell-t) := mul_pos (mul_pos ht hs) (by linarith)
  apply (div_le_div_iff₀ hd hm).2
  have h₁ := mul_le_mul_of_nonneg_left hden (mul_nonneg ht.le hs.le)
  have h₂ := mul_le_mul_of_nonneg_left hrt (mul_nonneg (sq_nonneg r) hm.le)
  have h₃ := mul_le_mul_of_nonneg_left h₁ (sq_nonneg r)
  have heq : t*s*(ell/2) = t*m/2 := by rw [← hmean]; ring
  rw [heq] at h₃
  nlinarith

/-- All three bipartite corrections, including both empirical variances, are
bounded by six times the square spread divided by the actual total. -/
theorem bipartite_correction_simple {a b s t m ell n va vb r : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hm : 0 < m)
    (hms : s*ell=m) (hmt : t*n=m)
    (hdm : m/2 ≤ m-t*s) (hde : ell/2 ≤ ell-t) (hdn : n/2 ≤ n-s)
    (hr : 0 ≤ r) (hrs : r ≤ s) (hrt : r ≤ t)
    (ha : |a-s| ≤ r) (hb : |b-t| ≤ r)
    (hva : 0 ≤ va) (hvau : va ≤ r^2) (hvb : 0 ≤ vb) (hvbu : vb ≤ r^2) :
    |(1-(a-s)*(b-t)/(m-t*s)+(a-s)*vb/(t*s*(ell-t))+
        (b-t)*va/(t*s*(n-s)))-1| ≤ 6*r^2/m := by
  have he : 0 < ell := by nlinarith
  have hn : 0 < n := by nlinarith
  have hmain := bipartite_correction (m:=m) (ell:=ell) (n:=n) hs ht (by linarith) (by linarith) (by linarith)
    hr ha hb hva hvau hvb hvbu
  have h₁ : r^2/(m-t*s) ≤ 2*r^2/m := by
    apply (div_le_div_iff₀ (by linarith) hm).2
    nlinarith [mul_le_mul_of_nonneg_left hdm (sq_nonneg r)]
  have h₂ := variance_correction_bound hr hs ht hm hms hde hrt
  have h₃ := variance_correction_bound hr ht hs hm hmt hdn hrs
  rw [mul_comm s t] at h₃
  exact hmain.trans ((add_le_add (add_le_add h₁ h₂) h₃).trans_eq (by ring))

/-- The source's `-5/3` bracket error is at most the reciprocal smaller
population once both actual average degrees exceed one. -/
theorem bipartite_error_reciprocal (ell n m : ℕ)
    (hell : 0 < ell) (hn : 0 < n)
    (hs : 1 ≤ Literature.EdgeProbabilities.leftAverage ell m)
    (ht : 1 ≤ Literature.EdgeProbabilities.rightAverage n m) :
    Literature.EdgeProbabilities.bipartiteErrorScale ell n m ((7:ℝ)/12) ≤
      1 / min (ell : ℝ) n := by
  open Literature.EdgeProbabilities in
  have hmin : 1 ≤ min (leftAverage ell m) (rightAverage n m) := le_min hs ht
  have hellR : 0 < (ell : ℝ) := by exact_mod_cast hell
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmR : 0 < (m : ℝ) := by
    have := (le_div_iff₀ hellR).1 hs
    linarith
  unfold Literature.EdgeProbabilities.bipartiteErrorScale
  have hpow : (min (Literature.EdgeProbabilities.leftAverage ell m)
      (Literature.EdgeProbabilities.rightAverage n m)) ^ (4*((7:ℝ)/12)-4) ≤
      (min (Literature.EdgeProbabilities.leftAverage ell m)
        (Literature.EdgeProbabilities.rightAverage n m))⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hmin (by norm_num)
  apply (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hpow hmR.le) (by positivity : 0 ≤ (((n:ℝ)*ell)⁻¹))).trans
  rcases le_total (ell : ℝ) (n : ℝ) with hle | hle
  · rw [min_eq_left hle]
    have hmeans : Literature.EdgeProbabilities.rightAverage n m ≤
        Literature.EdgeProbabilities.leftAverage ell m := by
      unfold Literature.EdgeProbabilities.rightAverage Literature.EdgeProbabilities.leftAverage
      exact div_le_div_of_nonneg_left hmR.le hellR hle
    rw [min_eq_right hmeans]
    unfold Literature.EdgeProbabilities.rightAverage
    field_simp
    norm_num
  · rw [min_eq_right hle]
    have hmeans : Literature.EdgeProbabilities.leftAverage ell m ≤
        Literature.EdgeProbabilities.rightAverage n m := by
      unfold Literature.EdgeProbabilities.rightAverage Literature.EdgeProbabilities.leftAverage
      exact div_le_div_of_nonneg_left hmR.le hnR hle
    rw [min_eq_left hmeans]
    unfold Literature.EdgeProbabilities.leftAverage
    field_simp
    norm_num

end MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Numerics
