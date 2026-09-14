import MajorityDynamics.GraphProcess.EnumerationBounds.Asymptotics
import MajorityDynamics.GraphProcess.RowConcentration.Asymptotics

noncomputable section
open Filter Set
open scoped Topology
namespace MajorityDynamics.GraphProcess.KernelInputs.Numerics

def parameter (T φ : ℝ) : ℝ := 2*T^3 + 4*T/φ

theorem parameter_bounds {T φ : ℝ} (hT : 1 < T) (hφ : 0 < φ) (_hφ1 : φ < 1/2) :
    1 < parameter T φ ∧ T^2 ≤ parameter T φ ∧
      2*T^3 ≤ parameter T φ ∧ 2*T/φ ≤ parameter T φ := by
  have hT0 : 0 < T := by linarith
  have hpow : T^2 ≤ T^3 := by nlinarith [sq_nonneg (T-1)]
  have hd : 0 < 2*T/φ := by positivity
  have hd4 : 0 < 4*T/φ := by positivity
  have heq : 4*T/φ = 2*(2*T/φ) := by ring
  have hT2 : 1 < T^2 := by nlinarith
  dsimp [parameter]
  constructor
  · nlinarith [sq_nonneg (T-1)]
  constructor
  · nlinarith
  constructor
  · linarith
  · nlinarith

/-- Any fixed logarithmic power is smaller than a positive expected-degree power,
with a threshold uniform over the original density interval. -/
theorem eventually_log_degree {θ T a b C : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hb : 0 < b) (hC : 0 < C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-θ) →
      (Real.log (N:ℝ))^a ≤ C*(p*N)^b := by
  have hT0 : 0 < T := by linarith
  have he : 0 < (1-θ)*b := mul_pos (by linarith) hb
  have hc : 0 < C*(T⁻¹)^b := by positivity
  have ht := (isLittleO_log_rpow_rpow_atTop a he).tendsto_div_nhds_zero
  have hnat : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  obtain ⟨N₁,h₁⟩ := eventually_atTop.mp
    ((ht.comp hnat).eventually (eventually_lt_nhds hc))
  obtain ⟨N₂,h₂⟩ := EnumerationBounds.eventually_window hθlo hθhi hT
    (L:=1) zero_lt_one (U:=1) zero_lt_one (M:=1) zero_lt_one
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN p hlo hhi
  have hw := h₂ N ((le_max_right _ _).trans hN) p hlo hhi
  have hl := h₁ N ((le_max_left _ _).trans hN)
  have hlow : T⁻¹*(N:ℝ)^(1-θ) ≤ p*N := by
    have hh := (mul_lt_mul_of_pos_right hlo hw.1).le
    have heq : T⁻¹*(N:ℝ)^(1-θ) = T⁻¹*(N:ℝ)^(-θ)*(N:ℝ) := by
      rw [mul_assoc]
      congr 1
      calc
        _ = (N:ℝ)^(-θ+1) := by congr 1; ring
        _ = (N:ℝ)^(-θ)*(N:ℝ)^(1:ℝ) := Real.rpow_add hw.1 _ _
        _ = _ := by rw [Real.rpow_one]
    rwa [heq]
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ T⁻¹*(N:ℝ)^(1-θ)) hlow hb.le
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hw.1.le] at hpow
  have hl' := (div_lt_iff₀ (Real.rpow_pos_of_pos hw.1 _)).mp hl
  exact hl'.le.trans (by nlinarith [mul_le_mul_of_nonneg_left hpow hC.le])

/-- Logarithm and finite size preparation, independent of the varying density. -/
theorem eventually_size_log {T φ Cf : ℝ} (hT : 1 < T) (hφ : 0 < φ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      2*T ≤ (N:ℝ) ∧ 1 ≤ Real.log (N:ℝ) ∧
      Cf*Real.sqrt (N:ℝ)*Real.log (N:ℝ) ≤ φ*N/(2*T) ∧
      2*Real.log T ≤ Real.log (N:ℝ) ∧
      2*Real.sqrt T*(Real.log (N:ℝ))^((2:ℝ)/3) ≤ Real.log (N:ℝ) := by
  have hT0 : 0 < T := by linarith
  have hnat : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog := Real.tendsto_log_atTop.comp hnat
  have ht : Tendsto (fun N : ℕ => Cf*Real.log (N:ℝ)/Real.sqrt (N:ℝ)) atTop (𝓝 0) := by
    have hh := (isLittleO_log_rpow_rpow_atTop (1:ℝ) (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero
    simpa [Real.rpow_one, Real.sqrt_eq_rpow, mul_div_assoc] using (hh.comp hnat).const_mul Cf
  obtain ⟨X,_,hX⟩ := EnumerationBounds.eventually_mul_rpow_le
    (a:=(2:ℝ)/3) (b:=1) (A:=2*Real.sqrt T) (B:=1) (by norm_num) zero_lt_one
  obtain ⟨N₀,h₀⟩ := eventually_atTop.mp
    ((hnat.eventually_ge_atTop (2*T)).and
      ((hlog.eventually_ge_atTop (max 1 (max (2*Real.log T) X))).and
        (ht.eventually (eventually_lt_nhds (by positivity : (0:ℝ)<φ/(2*T))))))
  refine ⟨N₀, ?_⟩
  intro N hN
  obtain ⟨hsize,hlogs,hsmall⟩ := h₀ N hN
  have hN0 : 0 < (N:ℝ) := by linarith
  have hs0 : 0 < Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hN0
  refine ⟨hsize,(le_max_left _ _).trans hlogs,?_,
    ((le_max_left _ _).trans (le_max_right _ _)).trans hlogs,?_⟩
  · have hh := (div_lt_iff₀ hs0).mp hsmall
    have hh' := mul_le_mul_of_nonneg_right hh.le hs0.le
    calc
      Cf*Real.sqrt (N:ℝ)*Real.log (N:ℝ) = (Cf*Real.log (N:ℝ))*Real.sqrt (N:ℝ) := by ring
      _ ≤ (φ/(2*T)*Real.sqrt (N:ℝ))*Real.sqrt (N:ℝ) := hh'
      _ = φ*N/(2*T) := by rw [mul_assoc, ← sq, Real.sq_sqrt hN0.le]; ring
  · simpa using hX (Real.log (N:ℝ))
      (((le_max_right _ _).trans (le_max_right _ _)).trans hlogs)

theorem block_log {N T r : ℝ} (hT : 1 < T) (hN : 2*T ≤ N)
    (hr : N/T ≤ r) (hrN : r ≤ N) (hlog : 2*Real.log T ≤ Real.log N) :
    2 ≤ r ∧ Real.log N/2 ≤ Real.log r ∧ Real.log r ≤ Real.log N := by
  have hT0 : 0 < T := by linarith
  have hN0 : 0 < N := by linarith
  have hr2 : 2 ≤ r := by have := (div_le_iff₀ hT0).mp hr; nlinarith
  have hlo := Real.log_le_log (show 0 < N/T by positivity) hr
  rw [Real.log_div hN0.ne' hT0.ne'] at hlo
  exact ⟨hr2, by linarith, Real.log_le_log (by linarith) hrN⟩

theorem relative_sizes {N T φ r ell w : ℝ} (hT : 1 < T)
    (hφ : 0 < φ) (hφ1 : φ < 1/2) (hN : 0 < N)
    (hr : N/T ≤ r) (hrN : r ≤ N) (hell : N/T ≤ ell) (hellN : ell ≤ N)
    (hw : φ*N/(2*T) ≤ w) :
    (parameter T φ)⁻¹*r ≤ ell ∧ ell ≤ parameter T φ*r ∧
      (parameter T φ)⁻¹*r ≤ w := by
  have hT0 : 0 < T := by linarith
  have hu := parameter_bounds hT hφ hφ1
  have hu0 : 0 < parameter T φ := by linarith [hu.1]
  have hUT : T ≤ parameter T φ := by nlinarith [sq_nonneg (T-1),hu.2.1]
  have hr0 : 0 < r := (div_pos hN hT0).trans_le hr
  have hNT := (div_le_iff₀ hT0).mp hr
  have hET := (div_le_iff₀ hT0).mp hell
  have he0 : 0 < ell := (div_pos hN hT0).trans_le hell
  constructor
  · rw [inv_mul_eq_div]
    apply (div_le_iff₀ hu0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hUT he0.le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hUT hr0.le]
  · rw [inv_mul_eq_div]
    apply (div_le_iff₀ hu0).mpr
    have hw0 : 0 ≤ w := (by positivity : 0 ≤ φ*N/(2*T)).trans hw
    have huφ := (div_le_iff₀ hφ).mp hu.2.2.2
    have hww := (div_le_iff₀ (by positivity : 0 < 2*T)).mp hw
    have hh := mul_le_mul_of_nonneg_left hw hu0.le
    have hdiv : N ≤ parameter T φ*(φ*N/(2*T)) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (by positivity : 0 < 2*T)).mpr
      nlinarith [mul_le_mul_of_nonneg_right huφ hN.le]
    simpa [mul_comm] using hrN.trans (hdiv.trans hh)

theorem relative_density {θ N T φ r p : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hφ : 0 < φ) (hφ1 : φ < 1/2) (hN : 0 < N)
    (hr : N/T ≤ r) (hrN : r ≤ N)
    (hlo : T⁻¹*N^(-θ) < p) (hhi : p < T*N^(-θ)) :
    (parameter T φ)⁻¹*r^(-θ) < p ∧ p < parameter T φ*r^(-θ) := by
  have hT0 : 0 < T := by linarith
  have hu := parameter_bounds hT hφ hφ1
  have hu0 : 0 < parameter T φ := by linarith [hu.1]
  have hr0 : 0 < r := (div_pos hN hT0).trans_le hr
  have hpow0 : 0 < r^(-θ) := Real.rpow_pos_of_pos hr0 _
  have hNT : N ≤ T*r := by nlinarith [(div_le_iff₀ hT0).mp hr]
  have hmon := Real.rpow_le_rpow_of_nonpos hN hNT (by linarith : -θ ≤ 0)
  rw [Real.mul_rpow hT0.le hr0.le] at hmon
  have hTp : T⁻¹ ≤ T^(-θ) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hT.le (by linarith)
  have hinv : (parameter T φ)⁻¹ ≤ T⁻¹*T⁻¹ := by
    have hh := one_div_le_one_div_of_le (by positivity : 0 < T^2) hu.2.1
    simpa [pow_two, one_div, mul_inv] using hh
  constructor
  · apply lt_of_le_of_lt ?_ hlo
    calc
      _ ≤ (T⁻¹*T⁻¹)*r^(-θ) := mul_le_mul_of_nonneg_right hinv hpow0.le
      _ ≤ T⁻¹*(T^(-θ)*r^(-θ)) := by
        have hh := mul_le_mul_of_nonneg_right hTp hpow0.le
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hT0.le)
      _ ≤ _ := mul_le_mul_of_nonneg_left hmon (inv_nonneg.mpr hT0.le)
  · apply hhi.trans_le
    have hm := Real.rpow_le_rpow_of_nonpos hr0 hrN (by linarith : -θ ≤ 0)
    have hUT : T ≤ parameter T φ := by nlinarith [sq_nonneg (T-1),hu.2.1]
    exact (mul_le_mul_of_nonneg_left hm hT0.le).trans
      (mul_le_mul_of_nonneg_right hUT hpow0.le)


/-- Numerical preparation discharged uniformly from the original window. -/
structure Regime (N : ℕ) (p θ T φ Cf : ℝ) : Prop where
  N_pos : 0 < (N:ℝ)
  p_pos : 0 < p
  p_lt_one : p < 1
  size_large : 2*T ≤ (N:ℝ)
  log_large : 1 ≤ Real.log (N:ℝ)
  size_error : Cf*Real.sqrt (N:ℝ)*Real.log (N:ℝ) ≤ φ*N/(2*T)
  block_size : ∀ r : ℝ, (N:ℝ)/T ≤ r → r ≤ N → 2 ≤ r
  density : ∀ r : ℝ, (N:ℝ)/T ≤ r → r ≤ N →
    (parameter T φ)⁻¹*r^(-θ) < p ∧ p < parameter T φ*r^(-θ)
  degree_window : ∀ r : ℝ, (N:ℝ)/T ≤ r → r ≤ N →
    Real.sqrt (p*N)*(Real.log (N:ℝ))^((2:ℝ)/3) ≤ (p*r)^((4:ℝ)/7)
  log_window : ∀ r ell : ℝ, (N:ℝ)/T ≤ r → r ≤ N →
    (N:ℝ)/T ≤ ell → ell ≤ N →
    Real.sqrt (p*N)*(Real.log (N:ℝ))^((2:ℝ)/3) ≤ Real.sqrt (p*ell)*Real.log r
  growth : ∀ r : ℝ, (N:ℝ)/T ≤ r → r ≤ N →
    (Real.log r)^100 ≤ (p*N)^((1:ℝ)/14)


theorem degree_window_of_log {N T p r : ℝ} (hN : 0 < N) (hT : 0 < T)
    (hp : 0 < p) (hr : N/T ≤ r)
    (hl : (Real.log N)^((2:ℝ)/3) ≤ T^(-(4:ℝ)/7)*(p*N)^((1:ℝ)/14)) :
    Real.sqrt (p*N)*(Real.log N)^((2:ℝ)/3) ≤ (p*r)^((4:ℝ)/7) := by
  have hx : 0 < p*N := mul_pos hp hN
  have hy : p*N/T ≤ p*r := by
    simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left hr hp.le
  calc
    _ ≤ Real.sqrt (p*N)*(T^(-(4:ℝ)/7)*(p*N)^((1:ℝ)/14)) :=
      mul_le_mul_of_nonneg_left hl (Real.sqrt_nonneg _)
    _ = (p*N/T)^((4:ℝ)/7) := by
      rw [Real.div_rpow hx.le hT.le, Real.sqrt_eq_rpow, neg_div, Real.rpow_neg hT.le]
      rw [show (p*N)^((1:ℝ)/2)*((T^((4:ℝ)/7))⁻¹*(p*N)^((1:ℝ)/14)) =
        ((p*N)^((1:ℝ)/2)*(p*N)^((1:ℝ)/14))/(T^((4:ℝ)/7)) by ring]
      rw [← Real.rpow_add hx]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hy (by norm_num)

theorem log_window_of_log {N T p r ell : ℝ} (hN : 0 < N) (hT : 0 < T)
    (hp : 0 < p) (hell : N/T ≤ ell)
    (hlog : Real.log N/2 ≤ Real.log r) (hlogN : 0 ≤ Real.log N)
    (hl : 2*Real.sqrt T*(Real.log N)^((2:ℝ)/3) ≤ Real.log N) :
    Real.sqrt (p*N)*(Real.log N)^((2:ℝ)/3) ≤ Real.sqrt (p*ell)*Real.log r := by
  have he0 : 0 < ell := (div_pos hN hT).trans_le hell
  have hNE := (div_le_iff₀ hT).mp hell
  have hs : Real.sqrt (p*N) ≤ Real.sqrt (p*ell)*Real.sqrt T := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ p*ell)]
    apply Real.sqrt_le_sqrt
    nlinarith [mul_le_mul_of_nonneg_left hNE hp.le]
  calc
    _ ≤ (Real.sqrt (p*ell)*Real.sqrt T)*(Real.log N)^((2:ℝ)/3) :=
      mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hlogN _)
    _ = Real.sqrt (p*ell)*(Real.sqrt T*(Real.log N)^((2:ℝ)/3)) := by ring
    _ ≤ Real.sqrt (p*ell)*(Real.log N/2) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg _)

theorem uniform_regime {θ T φ Cf : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hφ : 0 < φ) (hφ1 : φ < 1/2) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-θ) → Regime N p θ T φ Cf := by
  have hT0 : 0 < T := by linarith
  obtain ⟨N₁,h₁⟩ := eventually_size_log (Cf:=Cf) hT hφ
  obtain ⟨N₂,h₂⟩ := eventually_log_degree (a:=(2:ℝ)/3) (b:=(1:ℝ)/14)
    (C:=T^(-(4:ℝ)/7)) hθlo hθhi hT (by norm_num) (by positivity)
  obtain ⟨N₃,h₃⟩ := eventually_log_degree (a:=100) (b:=(1:ℝ)/14)
    (C:=1) hθlo hθhi hT (by norm_num) zero_lt_one
  obtain ⟨N₄,h₄⟩ := EnumerationBounds.eventually_window hθlo hθhi hT
    (L:=1) zero_lt_one (U:=1/2) (by norm_num) (M:=1) zero_lt_one
  refine ⟨max (max N₁ N₂) (max N₃ N₄), ?_⟩
  intro N hN p hlo hhi
  have hn1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hn2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hn3 : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hn4 : N₄ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hs := h₁ N hn1
  have hd := h₂ N hn2 p hlo hhi
  have hg := h₃ N hn3 p hlo hhi
  have hw := h₄ N hn4 p hlo hhi
  have hbl := fun r hr hrN => block_log hT hs.1 (r:=r) hr hrN hs.2.2.2.1
  refine ⟨hw.1,hw.2.1,by linarith [hw.2.2.2.2],hs.1,hs.2.1,hs.2.2.1,
    fun r hr hrN => (hbl r hr hrN).1,
    fun r hr hrN => relative_density hθlo hθhi hT hφ hφ1 hw.1 hr hrN hlo hhi,
    fun r hr _ => degree_window_of_log hw.1 hT0 hw.2.1 hr hd,
    fun r ell hr hrN hell _ => log_window_of_log hw.1 hT0 hw.2.1 hell
      (hbl r hr hrN).2.1 (by linarith [hs.2.1]) hs.2.2.2.2,?_⟩
  intro r hr hrN
  have hb := hbl r hr hrN
  have hrlog : 0 ≤ Real.log r := Real.log_nonneg (by linarith [hb.1])
  have hm := pow_le_pow_left₀ hrlog hb.2.2 100
  exact hm.trans (by simpa [Real.rpow_natCast] using hg)


/-- The literal conservative vertex/child/value union factor is absorbed by
stretched-exponential decay, uniformly over the original density window. -/
theorem union_absorption (n : ℕ) {θ T c A : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hc : 0 < c)
    (_hA : 0 < A) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-θ) →
      (N:ℝ)*2^(n+2)*(N+1)*Real.exp (-c*(p*N)^((1:ℝ)/7)) ≤ (N:ℝ)^(-A) := by
  obtain ⟨N₁,h₁⟩ := eventually_log_degree (a:=2) (b:=(1:ℝ)/7)
    (C:=c) hθlo hθhi hT (by norm_num) hc
  obtain ⟨N₂,h₂⟩ := RowConcentration.eventually_log_tail
    (C:=(2:ℝ)^(n+3)) (c:=1) (r:=2) (b:=2) (A:=A)
    (by positivity) zero_lt_one (by norm_num)
  refine ⟨max (max N₁ N₂) 1, ?_⟩
  intro N hN p hlo hhi
  have hn1 : N₁ ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hn2 : N₂ ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hn : 1 ≤ N := (le_max_right _ _).trans hN
  have hnR : (1:ℝ) ≤ N := by exact_mod_cast hn
  have hlog := h₁ N hn1 p hlo hhi
  have htail := h₂ N hn2
  have he : Real.exp (-c*(p*N)^((1:ℝ)/7)) ≤ Real.exp (-(Real.log (N:ℝ))^(2:ℝ)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hfactor : (N:ℝ)*2^(n+2)*(N+1) ≤ (2:ℝ)^(n+3)*(N:ℝ)^2 := by
    have hpw : (2:ℝ)^(n+3) = 2*(2:ℝ)^(n+2) := by
      calc
        _ = (2:ℝ)^((n+2)+1) := by congr 1
        _ = (2:ℝ)^(n+2)*2 := pow_succ _ _
        _ = _ := by ring
    rw [hpw]
    have hp : 0 ≤ (2:ℝ)^(n+2) := by positivity
    nlinarith [mul_nonneg hp (show 0 ≤ (N:ℝ)^2-N by nlinarith)]
  calc
    _ ≤ ((2:ℝ)^(n+3)*(N:ℝ)^2)*Real.exp (-(Real.log (N:ℝ))^(2:ℝ)) :=
      mul_le_mul hfactor he (Real.exp_nonneg _) (by positivity)
    _ ≤ _ := by simpa [Real.rpow_two] using htail

end MajorityDynamics.GraphProcess.KernelInputs.Numerics

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.Numerics.uniform_regime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.Numerics.uniform_regime

/-- info: 'MajorityDynamics.GraphProcess.KernelInputs.Numerics.union_absorption' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.KernelInputs.Numerics.union_absorption
