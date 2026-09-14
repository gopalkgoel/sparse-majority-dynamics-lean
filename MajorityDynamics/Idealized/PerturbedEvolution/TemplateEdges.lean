import MajorityDynamics.Idealized.Process.EvolutionAlgebra
import MajorityDynamics.Idealized.Process.QuotientExpansion

noncomputable section
namespace MajorityDynamics.Idealized.PerturbedEvolution
open Universal

/-- Multiplication propagates absolute errors with explicit bounded factors. -/
theorem product_error {x y x₀ y₀ E F B D : ℝ}
    (hx : |x - x₀| ≤ E) (hy : |y - y₀| ≤ F)
    (hb : |x| ≤ B) (hd : |y₀| ≤ D) :
    |x * y - x₀ * y₀| ≤ B * F + E * D := by
  have hE : 0 ≤ E := (abs_nonneg _).trans hx
  calc
    _ = |x * (y - y₀) + (x - x₀) * y₀| := by congr 1; ring
    _ ≤ |x| * |y - y₀| + |x - x₀| * |y₀| := by
      simpa only [abs_mul] using abs_add_le (x * (y - y₀)) ((x - x₀) * y₀)
    _ ≤ _ := add_le_add (mul_le_mul hb hy (abs_nonneg _) ((abs_nonneg _).trans hb))
      (mul_le_mul hx hd (abs_nonneg _) hE)

/-- Relative changes in two child means and the parent edge denominator give
an explicit error in the multiplicative correction to the size product. -/
theorem mean_edge_factor_error {x y z E : ℝ}
    (hE : 0 ≤ E) (hE1 : E ≤ 1)
    (hx : |x - 1| ≤ E) (hy : |y - 1| ≤ E)
    (hz : |z - 1| ≤ E) (hzlow : 1 / 2 ≤ |z|) :
    |x * y / z - 1| ≤ 8 * E := by
  have hb : |x| ≤ 2 := by
    have h := abs_add_le (x - 1) 1
    norm_num at h
    have : |x| ≤ |x - 1| + 1 := by simpa using h
    linarith
  have hp := product_error hx hy hb (show |(1 : ℝ)| ≤ 1 by norm_num)
  have hnum : |x * y - z| ≤ 4 * E := by
    have ht := abs_sub_le (x * y) 1 z
    rw [abs_sub_comm 1 z] at ht
    norm_num at hp
    linarith
  have hz0 : z ≠ 0 := abs_pos.mp (by linarith)
  rw [div_sub_one hz0, abs_div]
  calc
    _ ≤ (4 * E) / (1 / 2) := div_le_div₀ (by positivity) hnum (by norm_num) hzlow
    _ = _ := by ring

/-- Expansion of the two size factors, retaining the exact first-order
coefficient and making the quadratic error explicit. -/
theorem size_product_error {x y a b h d K B : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hsq : h ^ 2 ≤ d) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (ha : |a| ≤ B) (hb : |b| ≤ B)
    (hx : |x - (1 + a * h)| ≤ K * d)
    (hy : |y - (1 + b * h)| ≤ K * d) :
    |x * y - (1 + (a + b) * h)| ≤
      2 * (4 * B ^ 2 + 5 * B * K + K ^ 2 + 3 * K) * d := by
  have he := Process.quotient_linear_error hh hh1 hd hd1 hsq hB hK ha hb
    (show |(0 : ℝ)| ≤ B by simpa using hB) hx hy
    (show |(0 : ℝ)| ≤ K * d by simpa using mul_nonneg hK hd)
    (show 1 / 2 ≤ |1 + (0 : ℝ) * h + 0| by norm_num)
  simpa only [zero_mul, add_zero, div_one, sub_zero, add_sub_cancel] using he

/-- Assembly of the five scalar factors in Appendix E.5 Step 5. -/
theorem edge_product_error {x y a b r h d K B E : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hsq : h ^ 2 ≤ d) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (ha : |a| ≤ B) (hb : |b| ≤ B)
    (hx : |x - (1 + a * h)| ≤ K * d)
    (hy : |y - (1 + b * h)| ≤ K * d)
    (hr : |r - 1| ≤ E) (hrb : |r| ≤ 2) :
    |r * (x * y) - (1 + (a + b) * h)| ≤
      4 * (4 * B ^ 2 + 5 * B * K + K ^ 2 + 3 * K) * d +
      E * (1 + 2 * B) := by
  have hp := size_product_error hh hh1 hd hd1 hsq hK hB ha hb hx hy
  have ht : |1 + (a + b) * h| ≤ 1 + 2 * B := by
    calc
      _ ≤ |(1 : ℝ)| + |(a + b) * h| := abs_add_le _ _
      _ = 1 + |a + b| * h := by rw [abs_mul, abs_of_nonneg hh]; norm_num
      _ ≤ 1 + (|a| + |b|) * h := by gcongr; exact abs_add_le _ _
      _ ≤ 1 + (B + B) * 1 := by gcongr
      _ = _ := by ring
  have he := product_error hr hp hrb ht
  convert he using 1 <;> ring

/-- The actual local template relative to the reference template. No floor
operation is made on either template size in this identity. -/
theorem templateEdges_comparison_identity {n : ℕ}
    (sizes ref : Local.Sizes n) (e e₀ : Local.EdgeCounts n)
    (q q₀ : Local.Tilt n) (u v : History (n + 2))
    (hu : Local.templateSizes ref q₀ u ≠ 0)
    (hv : Local.templateSizes ref q₀ v ≠ 0)
    (ha : Process.childMean ref q₀ (parent u) (last u) (parent v) ≠ 0)
    (hb : Process.childMean ref q₀ (parent v) (last v) (parent u) ≠ 0)
    (hm : e₀ (parent u) (parent v) ≠ 0) :
    Local.templateEdges sizes e q u v =
      Local.templateEdges ref e₀ q₀ u v *
      (Local.templateSizes sizes q u / Local.templateSizes ref q₀ u) *
      (Local.templateSizes sizes q v / Local.templateSizes ref q₀ v) *
      ((Process.childMean sizes q (parent u) (last u) (parent v) /
        Process.childMean ref q₀ (parent u) (last u) (parent v)) *
       (Process.childMean sizes q (parent v) (last v) (parent u) /
        Process.childMean ref q₀ (parent v) (last v) (parent u)) /
       (e (parent u) (parent v) / e₀ (parent u) (parent v))) := by
  simp only [Local.templateEdges, Process.templateHalfEdges_eq_size_mul_childMean]
  by_cases he : e (parent u) (parent v) = 0
  · simp [he]
  · field_simp

/-- A lower bound on the reference converts an absolute mean estimate to the
relative estimate appearing in `templateEdges_comparison_identity`. -/
theorem relative_mean_error {m m₀ L C t : ℝ}
    (hL : 0 < L) (hm₀ : L ≤ m₀) (ht : 0 ≤ t)
    (hC : 0 ≤ C) (herr : |m - m₀| ≤ C * t * L) :
    |m / m₀ - 1| ≤ C * t := by
  have hpos : 0 < m₀ := hL.trans_le hm₀
  rw [div_sub_one hpos.ne', abs_div, abs_of_pos hpos]
  apply (div_le_iff₀ hpos).mpr
  exact herr.trans (mul_le_mul_of_nonneg_left hm₀ (mul_nonneg hC ht))

/-- Convert the additive next-size response to its multiplicative form.
The second term records the error in replacing the reference size by `N*v`. -/
theorem size_ratio_response {x z N v τ h e E ρ B : ℝ}
    (hN : 0 < N) (hv : 0 < v) (hz : N * v / 2 ≤ z)
    (hclose : |z - N * v| ≤ N * ρ)
    (hτ : 0 ≤ τ) (hh : 0 ≤ h) (he : |e| ≤ B)
    (herr : |x - z - τ * N * h * e| ≤ N * E) :
    |x / z - (1 + τ * h * (e / v))| ≤
      (2 / v) * E + (2 * ρ / v ^ 2) * (τ * h * B) := by
  obtain ⟨hzpos, hrec, hrecerr⟩ := Process.reciprocal_size_error hN hv hz hclose
  have hE : 0 ≤ E := nonneg_of_mul_nonneg_right ((abs_nonneg _).trans herr) hN
  have hρ : 0 ≤ ρ := nonneg_of_mul_nonneg_right ((abs_nonneg _).trans hclose) hN
  have hdiv : |(x - z - τ * N * h * e) / N| ≤ E := by
    rw [abs_div, abs_of_pos hN]
    exact (div_le_iff₀ hN).mpr (by simpa [mul_comm] using herr)
  have heq : x / z - (1 + τ * h * (e / v)) =
      (N / z) * ((x - z - τ * N * h * e) / N) +
      (N / z - 1 / v) * (τ * h * e) := by field_simp; ring
  rw [heq]
  calc
    _ ≤ |N / z| * |(x - z - τ * N * h * e) / N| +
        |N / z - 1 / v| * |τ * h * e| := by
      simpa only [abs_mul] using abs_add_le
        ((N / z) * ((x - z - τ * N * h * e) / N))
        ((N / z - 1 / v) * (τ * h * e))
    _ ≤ _ := by
      apply add_le_add
      · apply mul_le_mul _ hdiv (abs_nonneg _) (by positivity)
        simpa only [abs_of_pos (div_pos hN hzpos)] using hrec
      · apply mul_le_mul hrecerr _ (abs_nonneg _) (by positivity)
        simpa only [abs_mul, abs_of_nonneg hτ, abs_of_nonneg hh] using
          mul_le_mul_of_nonneg_left he (mul_nonneg hτ hh)

/-- Pointwise quantitative Step 5 for the literal local edge template. The
hypotheses are the size-ratio response and the three relative errors supplied
by F2 and the conditional-mean response. -/
theorem templateEdges_error_of_relative_bounds {n : ℕ}
    (sizes ref : Local.Sizes n) (e e₀ : Local.EdgeCounts n)
    (q q₀ : Local.Tilt n) (u v : History (n + 2))
    (a b h d K B J E W : ℝ)
    (hu : Local.templateSizes ref q₀ u ≠ 0)
    (hv : Local.templateSizes ref q₀ v ≠ 0)
    (ha₀ : Process.childMean ref q₀ (parent u) (last u) (parent v) ≠ 0)
    (hb₀ : Process.childMean ref q₀ (parent v) (last v) (parent u) ≠ 0)
    (hm₀ : e₀ (parent u) (parent v) ≠ 0)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hsq : h ^ 2 ≤ d) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (ha : |a| ≤ B) (hb : |b| ≤ B)
    (hx : |Local.templateSizes sizes q u / Local.templateSizes ref q₀ u -
      (1 + a * h)| ≤ K * d)
    (hy : |Local.templateSizes sizes q v / Local.templateSizes ref q₀ v -
      (1 + b * h)| ≤ K * d)
    (hE : 0 ≤ E) (hE1 : E ≤ 1 / 8) (hEd : E ≤ J * d)
    (hma : |Process.childMean sizes q (parent u) (last u) (parent v) /
      Process.childMean ref q₀ (parent u) (last u) (parent v) - 1| ≤ E)
    (hmb : |Process.childMean sizes q (parent v) (last v) (parent u) /
      Process.childMean ref q₀ (parent v) (last v) (parent u) - 1| ≤ E)
    (hme : |e (parent u) (parent v) / e₀ (parent u) (parent v) - 1| ≤ E)
    (hW : |Local.templateEdges ref e₀ q₀ u v| ≤ W) :
    |Local.templateEdges sizes e q u v - Local.templateEdges ref e₀ q₀ u v *
      (1 + (a + b) * h)| ≤
      W * (4 * (4 * B ^ 2 + 5 * B * K + K ^ 2 + 3 * K) +
        8 * J * (1 + 2 * B)) * d := by
  let r := (Process.childMean sizes q (parent u) (last u) (parent v) /
      Process.childMean ref q₀ (parent u) (last u) (parent v)) *
    (Process.childMean sizes q (parent v) (last v) (parent u) /
      Process.childMean ref q₀ (parent v) (last v) (parent u)) /
    (e (parent u) (parent v) / e₀ (parent u) (parent v))
  have hden : 1 / 2 ≤ |e (parent u) (parent v) / e₀ (parent u) (parent v)| := by
    have ht := abs_sub_le (1 : ℝ)
      (e (parent u) (parent v) / e₀ (parent u) (parent v)) 0
    rw [sub_zero, sub_zero, abs_sub_comm 1] at ht
    norm_num at ht
    linarith
  have hr : |r - 1| ≤ 8 * E := mean_edge_factor_error hE (by linarith) hma hmb hme hden
  have hrb : |r| ≤ 2 := by
    have ht := abs_sub_le r 1 0
    norm_num at ht
    linarith
  have hp := edge_product_error hh hh1 hd hd1 hsq hK hB ha hb hx hy hr hrb
  have hW0 : 0 ≤ W := (abs_nonneg _).trans hW
  have hJd : 0 ≤ J * d := hE.trans hEd
  have hconst : 0 ≤ 4 * (4 * B ^ 2 + 5 * B * K + K ^ 2 + 3 * K) * d +
      8 * E * (1 + 2 * B) := by positivity
  have hbound : |r *
      (Local.templateSizes sizes q u / Local.templateSizes ref q₀ u *
       (Local.templateSizes sizes q v / Local.templateSizes ref q₀ v)) -
      (1 + (a + b) * h)| ≤
      (4 * (4 * B ^ 2 + 5 * B * K + K ^ 2 + 3 * K) +
       8 * J * (1 + 2 * B)) * d := by
    apply hp.trans
    have ht := mul_le_mul_of_nonneg_right hEd (show 0 ≤ 8 * (1 + 2 * B) by positivity)
    nlinarith only [ht]
  rw [templateEdges_comparison_identity sizes ref e e₀ q q₀ u v hu hv ha₀ hb₀ hm₀]
  have hid : Local.templateEdges ref e₀ q₀ u v *
      (Local.templateSizes sizes q u / Local.templateSizes ref q₀ u) *
      (Local.templateSizes sizes q v / Local.templateSizes ref q₀ v) * r -
      Local.templateEdges ref e₀ q₀ u v * (1 + (a + b) * h) =
      Local.templateEdges ref e₀ q₀ u v * (r *
        (Local.templateSizes sizes q u / Local.templateSizes ref q₀ u *
        (Local.templateSizes sizes q v / Local.templateSizes ref q₀ v)) -
        (1 + (a + b) * h)) := by ring
  change |Local.templateEdges ref e₀ q₀ u v *
      (Local.templateSizes sizes q u / Local.templateSizes ref q₀ u) *
      (Local.templateSizes sizes q v / Local.templateSizes ref q₀ v) * r - _| ≤ _
  rw [hid, abs_mul]
  exact (mul_le_mul hW hbound (abs_nonneg _) hW0).trans_eq (by ring)

/-- F2 yields the relative error of the parent edge denominator. -/
theorem parent_edge_relative_error {m m₀ P c τ b f T r B : ℝ}
    (hP : 0 < P) (hc : 0 < c) (hm : c * P ≤ m₀)
    (hτ : 0 ≤ τ) (hτT : τ ≤ T) (hb : 0 ≤ b)
    (_hr : 0 ≤ r) (hr1 : r ≤ 1) (hf : |f| ≤ B)
    (hT : 0 ≤ T) (_hB : 0 ≤ B)
    (herr : |m - m₀ * (1 + τ * b * f)| ≤ T * b * r * P) :
    |m / m₀ - 1| ≤ (T * B + T / c) * b := by
  have hmpos : 0 < m₀ := (mul_pos hc hP).trans_le hm
  have hrem : |(m - m₀ * (1 + τ * b * f)) / m₀| ≤ (T / c) * b := by
    rw [abs_div, abs_of_pos hmpos]
    apply (div_le_iff₀ hmpos).mpr
    apply herr.trans
    have h1 := mul_le_mul_of_nonneg_left hr1 (show 0 ≤ T * b * P by positivity)
    have h2 := mul_le_mul_of_nonneg_left hm (show 0 ≤ T / c * b by positivity)
    have hid : T / c * b * (c * P) = T * b * P := by field_simp
    rw [hid] at h2
    nlinarith only [h1, h2]
  have hlead : |τ * b * f| ≤ T * B * b := by
    rw [abs_mul, abs_mul, abs_of_nonneg hτ, abs_of_nonneg hb]
    have h := mul_le_mul (mul_le_mul_of_nonneg_right hτT hb) hf (abs_nonneg _) (by positivity)
    nlinarith only [h]
  have hid : m / m₀ - 1 = (m - m₀ * (1 + τ * b * f)) / m₀ + τ * b * f := by
    field_simp; ring
  rw [hid]
  exact (abs_add_le _ _).trans ((add_le_add hrem hlead).trans_eq (by ring))

end MajorityDynamics.Idealized.PerturbedEvolution
