import MajorityDynamics.Probability.HypergeometricTiltTail.Hypergeom
import MajorityDynamics.Probability.HypergeometricTiltTail.NumericData

noncomputable section
namespace MajorityDynamics.Probability.HypergeometricTiltTail
open FixedSizeExponential

/-- The literal hypergeometric factor has a quadratic tail uniformly throughout
the original degree window, including zero and extreme feasible target counts. -/
theorem hypergeomMass_regime_tail {N M H : ℕ} {p T h : ℝ} {d t : ℤ}
    (hT : 1 < T) (r : Numerics.Regime N p T)
    (hMlo : (N : ℝ)-1 ≤ M) (hMhi : (M : ℝ) ≤ N) (hHM : H ≤ M)
    (hhlo : (N : ℝ)/T ≤ h) (hhhi : h ≤ N-(N : ℝ)/T)
    (hH : |(H : ℝ)-h| ≤ 1)
    (hd : |(d : ℝ)-p*N| ≤ Real.sqrt (p*N)*Real.log (N : ℝ))
    (ht0 : 0 ≤ t) (htd : t ≤ d)
    (htau : (Real.log (N : ℝ))^100 ≤ |((t : ℝ)-p*h)/Real.sqrt (p*h)|) :
    hypergeomMass M H d.toNat t.toNat ≤
      (1+1/centralAtomConstant)*(N : ℝ) *
        Real.exp (-(((t : ℝ)-p*h)/Real.sqrt (p*h))^2/(32*T)) := by
  obtain ⟨hN0,_,_,hH0,_,_,hd0,hdM,hdhi⟩ :=
    Numerics.basic_bounds (L := h) hT r hMlo hMhi hhlo hhhi hH hhlo hd
  have hM0 : 0 < (M : ℝ) := hd0.trans hdM
  have hHnat : 0 < H := by exact_mod_cast hH0
  have hdInt0 : 0 < d := by exact_mod_cast hd0
  have hdcast : (d.toNat : ℝ) = d := by exact_mod_cast Int.toNat_of_nonneg hdInt0.le
  have htcast : (t.toNat : ℝ) = t := by exact_mod_cast Int.toNat_of_nonneg ht0
  have hdNat0 : 0 < d.toNat := by exact_mod_cast (show 0 < (d.toNat : ℝ) by simpa [hdcast] using hd0)
  have hdNatM : d.toNat < M := by exact_mod_cast (show (d.toNat : ℝ) < M by simpa [hdcast] using hdM)
  have htNatd : t.toNat ≤ d.toNat := Int.toNat_le_toNat htd
  have hHMreal : (H : ℝ) ≤ M := by exact_mod_cast hHM
  have hμ := Numerics.hypergeometric_bounds (x := p*N)
    (mul_pos r.p_pos hN0) hM0 hH0 hHMreal hd0 (by simpa [mul_assoc] using hdhi)
    (show 0 ≤ (t : ℝ) by exact_mod_cast ht0)
    (show (t : ℝ) ≤ d by exact_mod_cast htd)
  have hdev := Numerics.deviation_conversion hT r hN0 hM0 hMlo hMhi hH0.le
    hHMreal hhlo hH hd htau
  have hexp := Numerics.tail_exponent (x := p*N)
    (τ := ((t : ℝ)-p*h)/Real.sqrt (p*h)) hT (mul_pos r.p_pos hN0)
    rfl r.p_pos hN0 hhlo (abs_nonneg _) hμ.1 hμ.2.1 hμ.2.2 hdev
  have hbound := hypergeomMass_chernoff hHM hdNat0 hdNatM htNatd hHnat
  rw [hdcast,htcast] at hbound
  have hcent : (H : ℝ)*((d : ℝ)/M) = ((d : ℝ)/M)*H := mul_comm _ _
  rw [hcent] at hbound
  have he : Real.exp (-|(t : ℝ)-((d : ℝ)/M)*H|^2 /
      (2*(((d : ℝ)/M)*H)+2*|(t : ℝ)-((d : ℝ)/M)*H|/3)) ≤
      Real.exp (-(((t : ℝ)-p*h)/Real.sqrt (p*h))^2/(32*T)) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_div] using neg_le_neg hexp
  have hN1 : 1 ≤ (N : ℝ) := by linarith [r.N_large]
  have hdsqrt : Real.sqrt (d : ℝ) ≤ N := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · exact hN0.le
    · have hdn : (d : ℝ) ≤ N := hdM.le.trans hMhi
      nlinarith
  have hpref : Real.sqrt (d : ℝ)/centralAtomConstant ≤
      (1+1/centralAtomConstant)*(N : ℝ) := by
    have hc := centralAtomConstant_pos
    have hs := div_le_div_of_nonneg_right hdsqrt hc.le
    have heq : (N : ℝ)/centralAtomConstant = (1/centralAtomConstant)*(N : ℝ) := by ring
    rw [heq] at hs
    nlinarith
  have hc := centralAtomConstant_pos
  exact hbound.trans (mul_le_mul hpref he (Real.exp_pos _).le (by positivity))

end MajorityDynamics.Probability.HypergeometricTiltTail
