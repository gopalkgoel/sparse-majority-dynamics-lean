import MajorityDynamics.GraphProcess.GoodArrays.Basic

noncomputable section
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.GoodArrays
open Universal
variable {V : Type*} [Fintype V] {n : ℕ}

theorem separated_of_admissible {y : Local.CoarseData V n} {q : Local.Tilt n}
    {T φ p : ℝ} (h : Local.CoreAdmissible y q T φ p) : Separated y T p :=
  h.separation

theorem window_bound_sqrt {T p : ℝ} (hT : 1 < T) (N : ℕ) :
    window n T p N ≤ Real.sqrt (p*N) := by
  have hh : (1 : ℝ) ≤ labelCount n := by exact_mod_cast labelCount_pos n
  have hd : 1 ≤ 100*T*(labelCount n : ℝ) := by nlinarith
  exact (div_le_iff₀ (by positivity : 0 < 100*T*(labelCount n : ℝ))).2
    (by nlinarith [Real.sqrt_nonneg (p*N)])

theorem e0_regular {y : Local.CoarseData V n} {T p : ℝ}
    (hT : 1 < T) (hReg : Regime y T p) {d : RowArray.Ambient y.part}
    (hd : d ∈ E0 y T p) : RowArray.Regular p d := by
  have hw := (Finset.mem_filter.mp hd).2.2
  intro v t
  have he := hw (y.part v) t v (by simp)
  have hc := hReg.center (y.part v) t
  have ht := abs_sub_le (RowArray.values d v t : ℝ)
    (EnumerationBounds.avg y (y.part v) t) (p*(y.sizes t : ℝ))
  have hs := window_bound_sqrt (n := n) (p := p) hT (Fintype.card V)
  have hr := hReg.regular
  change |(RowArray.values d v t : ℝ) - p*(y.sizes t : ℝ)| ≤ _
  nlinarith

theorem e0_gamma_one {y : Local.CoarseData V n} {T p : ℝ}
    (hT : 1 < T) (hReg : Regime y T p) {d : RowArray.Ambient y.part}
    (hd : d ∈ E0 y T p) : RowArray.Gamma y.part y.edge 1 p d := by
  have hw := (Finset.mem_filter.mp hd).2.2
  have hs := window_bound_sqrt (n := n) (p := p) hT (Fintype.card V)
  have hpN : 0 ≤ p * Fintype.card V := le_of_lt (mul_pos hReg.density_pos hReg.card_pos)
  have hsq := Real.sq_sqrt hpN
  intro s t
  have he : ∀ v ∈ History.block y.part s,
      ((RowArray.values d v t : ℝ) - EnumerationBounds.avg y s t)^2 ≤
        p * Fintype.card V := by
    intro v hv
    have h := (hw s t v hv).trans hs
    nlinarith [sq_abs ((RowArray.values d v t : ℝ) - EnumerationBounds.avg y s t),
      abs_nonneg ((RowArray.values d v t : ℝ) - EnumerationBounds.avg y s t),
      Real.sqrt_nonneg (p*Fintype.card V)]
  have hsum := Finset.sum_le_sum he
  simp only [Finset.sum_const, nsmul_eq_mul, History.block_card_partSizes] at hsum
  have hsize : (y.sizes s : ℝ) ≤ Fintype.card V := by exact_mod_cast y.sizes_le_card s
  have htotal : (∑ v ∈ History.block y.part s,
      ((RowArray.values d v t : ℝ) - EnumerationBounds.avg y s t)^2) ≤
      p*(Fintype.card V : ℝ)^2 := by
    calc
      _ ≤ (y.sizes s : ℝ) * (p*Fintype.card V) := hsum
      _ ≤ (Fintype.card V : ℝ) * (p*Fintype.card V) := mul_le_mul_of_nonneg_right hsize hpN
      _ = _ := by ring
  change (1/(p*(Fintype.card V : ℝ)^2)) *
    (∑ v ∈ History.block y.part s,
      ((RowArray.values d v t : ℝ) - EnumerationBounds.avg y s t)^2) ≤ 1
  rw [one_div, ← div_eq_inv_mul]
  exact (div_le_one (mul_pos hReg.density_pos (sq_pos_of_pos hReg.card_pos))).2 htotal

theorem e0_gamma_mono {y : Local.CoarseData V n} {T p C : ℝ}
    (hT : 1 < T) (hReg : Regime y T p) (hC : 1 ≤ C)
    {d : RowArray.Ambient y.part} (hd : d ∈ E0 y T p) :
    RowArray.Gamma y.part y.edge C p d :=
  fun s t => (e0_gamma_one hT hReg hd s t).trans hC

private theorem edge_scale_eq {y : Local.CoarseData V n} {T p : ℝ}
    (hReg : Regime y T p) : Local.edgeScale (Fintype.card V) p =
      (Fintype.card V : ℝ)*Real.sqrt (p*Fintype.card V) := by
  have hpN := mul_pos hReg.density_pos hReg.card_pos
  have hs := Real.sqrt_pos.2 hpN
  unfold Local.edgeScale
  apply (div_eq_iff (ne_of_gt hs)).2
  nlinarith [Real.sq_sqrt hpN.le]

private theorem window_margin {y : Local.CoarseData V n} {T p : ℝ}
    (hT : 1 < T) (hReg : Regime y T p) (s : History (n+1)) :
    (labelCount n : ℝ)*window n T p (Fintype.card V) <
      (T⁻¹ * Local.edgeScale (Fintype.card V) p)/(y.sizes s : ℝ) := by
  have hT0 : 0 < T := by linarith
  have hh : (0 : ℝ) < labelCount n := by exact_mod_cast labelCount_pos n
  have hs := Real.sqrt_pos.2 (mul_pos hReg.density_pos hReg.card_pos)
  have hsize : (y.sizes s : ℝ) ≤ Fintype.card V := by exact_mod_cast y.sizes_le_card s
  rw [edge_scale_eq hReg]
  have he : (labelCount n : ℝ)*window n T p (Fintype.card V) =
      Real.sqrt (p*Fintype.card V)/(100*T) := by
    unfold window
    field_simp
  rw [he]
  apply (lt_div_iff₀ (hReg.size_pos s)).2
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ (show 0 < 100*T by positivity)).2
  have heq : T⁻¹ * ((Fintype.card V : ℝ) * Real.sqrt (p*Fintype.card V)) * (100*T) =
      100 * Fintype.card V * Real.sqrt (p*Fintype.card V) := by field_simp
  rw [heq]
  nlinarith [mul_pos hReg.card_pos hs]

theorem e0_history {y : Local.CoarseData V n} {T p : ℝ}
    (hT : 1 < T) (hReg : Regime y T p) (hSep : Separated y T p)
    {d : RowArray.Ambient y.part} (hd : d ∈ E0 y T p) :
    d ∈ RowArray.history y.part := by
  have hw := (Finset.mem_filter.mp hd).2.2
  apply (RowArray.history_iff_blocks y.part d).2
  intro s v hv r
  let z := ∑ t, character r.castSucc t * y.realEdges s t
  let x := imbalance r.castSucc (RowArray.realRow d v)
  have herr : |x - z/(y.sizes s : ℝ)| ≤
      (labelCount n : ℝ)*window n T p (Fintype.card V) := by
    have he : x-z/(y.sizes s : ℝ) = ∑ t,
        character r.castSucc t * ((RowArray.values d v t : ℝ) - EnumerationBounds.avg y s t) := by
      dsimp [x, z, imbalance, EnumerationBounds.avg, Local.CoarseData.realEdges]
      simp only [RowArray.realRow_apply, Finset.sum_div, mul_sub, mul_div_assoc,
        Finset.sum_sub_distrib]
    rw [he]
    calc
      _ ≤ ∑ t, |character r.castSucc t *
          ((RowArray.values d v t : ℝ)-EnumerationBounds.avg y s t)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t : History (n+1), window n T p (Fintype.card V) := by
        apply Finset.sum_le_sum
        intro t _
        have hc : |character r.castSucc t| = 1 := by
          unfold character sign
          split <;> norm_num
        simpa only [abs_mul, hc, one_mul] using hw s t v hv
      _ = _ := by simp [labelCount]
  have hm := window_margin hT hReg s
  have he := abs_lt.mp (herr.trans_lt hm)
  have hsep := hSep s r
  have hsize := hReg.size_pos s
  change decision _ _ x
  left
  change decision _ _ (z - sign _ * _) at hsep
  rcases hsep with hsep | ⟨hsep, _⟩ <;>
    cases hb : bits (n+1) s r.succ <;> simp only [hb, sign_false, sign_true, one_mul,
      neg_one_mul, sub_neg_eq_add] at *
  · have hz := (div_le_div_of_nonneg_right (le_of_lt hsep) hsize.le)
    simp only [sub_div, zero_div] at hz
    linarith
  · have hz := (div_le_div_of_nonneg_right (le_of_lt hsep) hsize.le)
    simp only [neg_div, add_div, zero_div] at hz
    linarith
  · have hz := congrArg (fun a : ℝ => a/(y.sizes s : ℝ)) hsep
    simp only [sub_div, zero_div] at hz
    linarith
  · have hz := congrArg (fun a : ℝ => a/(y.sizes s : ℝ)) hsep
    simp only [add_div, zero_div] at hz
    linarith

end MajorityDynamics.GraphProcess.GoodArrays
