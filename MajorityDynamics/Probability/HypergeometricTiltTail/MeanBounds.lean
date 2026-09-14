import MajorityDynamics.Probability.FixedSizeExponential.Basic

noncomputable section
namespace MajorityDynamics.Probability.HypergeometricTiltTail

/-- A single stratum's deterministic mean, before normalization. -/
theorem tilt_component_mean_le {p H k b g : ℝ}
    (hp : 0 ≤ p) (hH : 0 < H) (hk : 0 ≤ k) (_hg : 0 ≤ g)
    (hb : |b| ≤ H*g) :
    ((1+p)*k/H-p)*b ≤ (|k-p*H|+p*k)*g := by
  have hbg : |b/H| ≤ g := by
    rw [abs_div, abs_of_pos hH]
    exact (div_le_iff₀ hH).2 (by nlinarith)
  have hid : ((1+p)*k/H-p)*b = ((k-p*H)+p*k)*(b/H) := by
    field_simp
    ring
  rw [hid]
  calc
    _ ≤ |((k-p*H)+p*k)*(b/H)| := le_abs_self _
    _ = |(k-p*H)+p*k| *|b/H| := abs_mul _ _
    _ ≤ (|k-p*H|+p*k)*g := by
      apply mul_le_mul _ hbg (abs_nonneg _) (by positivity)
      simpa only [abs_of_nonneg (mul_nonneg hp hk)] using abs_add_le (k-p*H) (p*k)

/-- Deterministic cancellation in the mean of the two complementary strata. -/
theorem pair_tilt_numerator_le {N p M H h d t b₁ b₂ g : ℝ}
    (hp : 0 ≤ p) (hH : 0 < H) (hHc : 0 < M-H)
    (ht : 0 ≤ t) (htd : t ≤ d) (hg : 0 ≤ g)
    (hMH : |M-N| ≤ 1) (hHh : |H-h| ≤ 1)
    (hb₁ : |b₁| ≤ H*g) (hb₂ : |b₂| ≤ (M-H)*g) :
    ((1+p)*t/H-p)*b₁ + ((1+p)*(d-t)/(M-H)-p)*b₂ ≤
      (2*|t-p*h| + |d-p*N| + 3*p + p*d)*g := by
  have hfirst : |t-p*H| ≤ |t-p*h|+p := by
    calc
      _ = |(t-p*h)+p*(h-H)| := by congr 1; ring
      _ ≤ |t-p*h|+|p*(h-H)| := abs_add_le _ _
      _ ≤ |t-p*h|+p := by
        rw [abs_mul, abs_of_nonneg hp, abs_sub_comm h H]
        nlinarith
  have hsecond : |d-t-p*(M-H)| ≤ |d-p*N|+|t-p*H|+p := by
    calc
      _ = |((d-p*N)-(t-p*H))+p*(N-M)| := by congr 1; ring
      _ ≤ |(d-p*N)-(t-p*H)|+|p*(N-M)| := abs_add_le _ _
      _ ≤ |d-p*N|+|t-p*H|+p := by
        have hab := abs_sub (d-p*N) (t-p*H)
        rw [abs_mul, abs_of_nonneg hp, abs_sub_comm N M]
        nlinarith
  have h₁ := tilt_component_mean_le hp hH ht hg hb₁
  have h₂ := tilt_component_mean_le hp hHc (sub_nonneg.mpr htd) hg hb₂
  have hsum : |t-p*H| + p*t + (|d-t-p*(M-H)|+p*(d-t)) ≤
      2*|t-p*h|+|d-p*N|+3*p+p*d := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_right hsum hg
  nlinarith

/-- The literal two-stratum tilt mean has only a linear normalized-deviation
cost. All hypotheses are deterministic numerical inputs; no tail estimate is
assumed. The population may differ from the ambient size by one. -/
theorem pair_tilt_mean_bound {N p T g M H h L d t b₁ b₂ : ℝ}
    (hT : 1 ≤ T) (hN : 0 < N) (hp : 0 < p) (hp1 : p ≤ 1)
    (hp2N : p^2*N ≤ 1) (hpN : 1 ≤ p*N) (hg : 1 ≤ g)
    (hMN : |M-N| ≤ 1) (hHh : |H-h| ≤ 1)
    (hh : 0 < h) (hhN : h ≤ N) (hH : 0 < H) (hHc : 0 < M-H)
    (hL : N/T ≤ L) (ht : 0 ≤ t) (htd : t ≤ d) (hd : d ≤ 2*p*N)
    (hdev : |d-p*N| ≤ Real.sqrt (p*N)*g)
    (hb₁ : |b₁| ≤ H*g) (hb₂ : |b₂| ≤ (M-H)*g) :
    ((1+p)*t/H-p)*b₁/Real.sqrt (p*L) +
      ((1+p)*(d-t)/(M-H)-p)*b₂/Real.sqrt (p*L) ≤
      20*T*(|(t-p*h)/Real.sqrt (p*h)| *g+g^2) := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hL0 : 0 < L := lt_of_lt_of_le (div_pos hN hT0) hL
  have hz : 0 < Real.sqrt (p*L) := Real.sqrt_pos.mpr (mul_pos hp hL0)
  have hs : 0 ≤ Real.sqrt (p*N) := Real.sqrt_nonneg _
  have hsq := Real.sq_sqrt (mul_pos hp hN).le
  have hzsq := Real.sq_sqrt (mul_pos hp hL0).le
  have hs1 : 1 ≤ Real.sqrt (p*N) := by nlinarith only [hs, hsq, hpN]
  have hNTL : N ≤ L*T := (div_le_iff₀ hT0).1 hL
  have hcomp : Real.sqrt (p*N) ≤ T*Real.sqrt (p*L) := by
    have hpcomp : p*N ≤ T*(p*L) := by nlinarith only [mul_le_mul_of_nonneg_left hNTL hp.le]
    have hTcomp : T*(p*L) ≤ T^2*(p*L) := by
      have := mul_nonneg (show 0 ≤ T*(T-1) by positivity) (mul_pos hp hL0).le
      nlinarith only [this]
    have htz : 0 ≤ T*Real.sqrt (p*L) := by positivity
    nlinarith only [hs, htz, hpcomp, hTcomp, hsq, mul_le_mul_of_nonneg_left (le_of_eq hzsq) (sq_nonneg T), mul_le_mul_of_nonneg_left (le_of_eq hzsq.symm) (sq_nonneg T)]
  have hsmall : Real.sqrt (p*h) ≤ Real.sqrt (p*N) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hhN hp.le)
  have hhroot : 0 < Real.sqrt (p*h) := Real.sqrt_pos.mpr (mul_pos hp hh)
  have hnormalize : |t-p*h| = |(t-p*h)/Real.sqrt (p*h)| *Real.sqrt (p*h) := by
    rw [abs_div, abs_of_pos hhroot, div_mul_cancel₀ _ hhroot.ne']
  have hdiff : |t-p*h| ≤ |(t-p*h)/Real.sqrt (p*h)| *Real.sqrt (p*N) := by
    rw [hnormalize]
    exact mul_le_mul_of_nonneg_left hsmall (abs_nonneg _)
  have hpd : p*d ≤ 2 := by
    have hm := mul_le_mul_of_nonneg_left hd hp.le
    nlinarith only [hm, hp2N]
  have hnum := pair_tilt_numerator_le hp.le hH hHc ht htd (by linarith : 0 ≤ g)
    hMN hHh hb₁ hb₂
  have hnum₂ : 2*|t-p*h|+|d-p*N|+3*p+p*d ≤
      (2*|(t-p*h)/Real.sqrt (p*h)|+g+5)*Real.sqrt (p*N) := by
    nlinarith only [hdiff, hdev, hp1, hpd, hs1]
  have hfactor : 0 ≤ (2*|(t-p*h)/Real.sqrt (p*h)|+g+5)*g := by positivity
  have habs : 0 ≤ |(t-p*h)/Real.sqrt (p*h)| := abs_nonneg _
  have hpoly : (2*|(t-p*h)/Real.sqrt (p*h)|+g+5)*g ≤
      20*(|(t-p*h)/Real.sqrt (p*h)| *g+g^2) := by
    have hag : 0 ≤ |(t-p*h)/Real.sqrt (p*h)| *g := by positivity
    have hgg : g ≤ g^2 := by nlinarith only [hg]
    nlinarith only [hag, hgg, sq_nonneg g]
  rw [← add_div]
  apply (div_le_iff₀ hz).2
  calc
    _ ≤ (2*|t-p*h|+|d-p*N|+3*p+p*d)*g := hnum
    _ ≤ ((2*|(t-p*h)/Real.sqrt (p*h)|+g+5)*g)*Real.sqrt (p*N) := by
      nlinarith only [mul_le_mul_of_nonneg_right hnum₂ (show 0 ≤ g by linarith)]
    _ ≤ ((2*|(t-p*h)/Real.sqrt (p*h)|+g+5)*g)*(T*Real.sqrt (p*L)) :=
      mul_le_mul_of_nonneg_left hcomp hfactor
    _ ≤ 20*T*(|(t-p*h)/Real.sqrt (p*h)| *g+g^2)*Real.sqrt (p*L) := by
      nlinarith only [mul_le_mul_of_nonneg_right hpoly (show 0 ≤ T*Real.sqrt (p*L) by positivity)]

end MajorityDynamics.Probability.HypergeometricTiltTail
