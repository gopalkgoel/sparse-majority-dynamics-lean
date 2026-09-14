import MajorityDynamics.GraphProcess.AutomaticGraphicality.Bounds

noncomputable section
namespace MajorityDynamics.GraphProcess.EnumerationBounds

 theorem size_estimates {N T a : ℝ} (hT : 1 < T) (hN : 2*T ≤ N)
    (ha : N/T ≤ a) : 2 ≤ a ∧ N/(2*T) ≤ a-1 := by
  have hT0 : 0 < T := by linarith
  have hna := (div_le_iff₀ hT0).mp ha
  constructor
  · nlinarith
  · apply (div_le_iff₀ (by positivity : 0 < 2*T)).mpr
    nlinarith

 theorem count_upper {N T p a b m : ℝ} (hN : 0 < N) (hT : 1 < T)
    (hp : 0 < p) (hx : 4*T^6 ≤ p*N) (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (haN : a ≤ N) (hbN : b ≤ N)
    (hm : |m-p*a*b| ≤ T*N^2*p/Real.sqrt (p*N)) : m ≤ 2*p*N^2 := by
  have hT0 : 0 < T := by linarith
  have hs0 : 0 < Real.sqrt (p*N) := Real.sqrt_pos.mpr (mul_pos hp hN)
  have hs : T ≤ Real.sqrt (p*N) := by
    have hsquare := Real.sq_sqrt (mul_pos hp hN).le
    have hT3 : T ≤ T^3 := by nlinarith [sq_nonneg (T-1)]
    have hT30 : 0 ≤ T^3 := by positivity
    nlinarith [sq_nonneg (Real.sqrt (p*N)-2*T^3)]
  have he : T*N^2*p/Real.sqrt (p*N) ≤ p*N^2 := by
    apply (div_le_iff₀ hs0).mpr
    have h := mul_le_mul_of_nonneg_left hs (show 0 ≤ p*N^2 by positivity)
    nlinarith [h]
  have hab : a*b ≤ N^2 := by nlinarith [mul_le_mul haN hbN hb hN.le]
  have hcenter := mul_le_mul_of_nonneg_left hab hp.le
  have hm' := (abs_le.mp hm).2
  nlinarith

 theorem pair_estimates {N T p a b m : ℝ} (hN : 0 < N) (hT : 1 < T)
    (hp : 0 < p) (hx : 4*T^6 ≤ p*N)
    (ha : N/T ≤ a) (hb : N/T ≤ b) (haN : a ≤ N) (hbN : b ≤ N)
    (hm : |m-p*a*b| ≤ T*N^2*p/Real.sqrt (p*N)) :
    p*N/(2*T^2) ≤ m/a ∧ m/a ≤ 2*T*p*N ∧
    |m/a-p*b| ≤ T^2*Real.sqrt (p*N) ∧
    p/(2*T^2) ≤ m/(a*b) ∧ m/(a*b) ≤ 4*T^2*p := by
  have hT0 : 0 < T := by linarith
  have ha0 : 0 < a := (div_pos hN hT0).trans_le ha
  have hb0 : 0 < b := (div_pos hN hT0).trans_le hb
  have hlow := AutomaticGraphicality.count_lower hN hT hp hx ha hb hm
  have hupp := count_upper hN hT hp hx ha0.le hb0.le haN hbN hm
  have hna := (div_le_iff₀ hT0).mp ha
  have hnb := (div_le_iff₀ hT0).mp hb
  have havgLow : p*N/(2*T^2) ≤ m/a := by
    apply (le_div_iff₀ ha0).mpr
    have h := mul_le_mul_of_nonneg_left haN (show 0 ≤ p*N/(2*T^2) by positivity)
    calc
      p*N/(2*T^2)*a ≤ p*N/(2*T^2)*N := h
      _ = p*N^2/(2*T^2) := by ring
      _ ≤ m := hlow
  have havgUp : m/a ≤ 2*T*p*N := by
    apply (div_le_iff₀ ha0).mpr
    have h := mul_le_mul_of_nonneg_left hna (show 0 ≤ 2*p*N by positivity)
    nlinarith [h]
  have hcenter : |m/a-p*b| ≤ T^2*Real.sqrt (p*N) := by
    have hs0 : 0 < Real.sqrt (p*N) := Real.sqrt_pos.mpr (mul_pos hp hN)
    have hs2 := Real.sq_sqrt (mul_pos hp hN).le
    rw [show m/a-p*b = (m-p*a*b)/a by field_simp, abs_div, abs_of_pos ha0]
    apply (div_le_iff₀ ha0).mpr
    apply hm.trans
    apply (div_le_iff₀ hs0).mpr
    have h := mul_le_mul_of_nonneg_left hna (show 0 ≤ T*p*N by positivity)
    calc
      T*N^2*p ≤ T^2*(p*N)*a := by nlinarith [h]
      _ = T^2*Real.sqrt (p*N)*a*Real.sqrt (p*N) := by
        rw [show T^2*Real.sqrt (p*N)*a*Real.sqrt (p*N) = T^2*(Real.sqrt (p*N))^2*a by ring, hs2]
  have hcrossLow : p/(2*T^2) ≤ m/(a*b) := by
    apply (le_div_iff₀ (mul_pos ha0 hb0)).mpr
    have hab : a*b ≤ N^2 := by nlinarith [mul_le_mul haN hbN hb0.le hN.le]
    calc
      p/(2*T^2)*(a*b) ≤ p/(2*T^2)*N^2 := mul_le_mul_of_nonneg_left hab (by positivity)
      _ = p*N^2/(2*T^2) := by ring
      _ ≤ m := hlow
  have hcrossUp : m/(a*b) ≤ 4*T^2*p := by
    apply (div_le_iff₀ (mul_pos ha0 hb0)).mpr
    have hprod := mul_le_mul hna hnb hN.le (by positivity : 0 ≤ a*T)
    have h := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 2*p by positivity)
    have hpos : 0 ≤ T^2*p*(a*b) := by positivity
    nlinarith [h]
  exact ⟨havgLow, havgUp, hcenter, hcrossLow, hcrossUp⟩

 theorem internal_estimates {N T p a m : ℝ} (hN : 0 < N) (hT : 1 < T)
    (hp : 0 < p) (hx : 4*T^6 ≤ p*N) (hNsize : 2*T ≤ N)
    (ha : N/T ≤ a) (haN : a ≤ N)
    (hm : |m-p*a*a| ≤ T*N^2*p/Real.sqrt (p*N)) :
    p/(2*T^2) ≤ (m/a)/(a-1) ∧ (m/a)/(a-1) ≤ 4*T^2*p := by
  have hT0 : 0 < T := by linarith
  have hz := size_estimates hT hNsize ha
  have hap : 0 < a-1 := by linarith [hz.1]
  have he := pair_estimates hN hT hp hx ha ha haN haN hm
  constructor
  · apply (le_div_iff₀ hap).mpr
    calc
      p/(2*T^2)*(a-1) ≤ p/(2*T^2)*N := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = p*N/(2*T^2) := by ring
      _ ≤ m/a := he.1
  · apply (div_le_iff₀ hap).mpr
    have h := (div_le_iff₀ (by positivity : 0 < 2*T)).mp hz.2
    have h' := mul_le_mul_of_nonneg_left h (show 0 ≤ 2*T*p by positivity)
    nlinarith [he.2.1, h']

end MajorityDynamics.GraphProcess.EnumerationBounds
