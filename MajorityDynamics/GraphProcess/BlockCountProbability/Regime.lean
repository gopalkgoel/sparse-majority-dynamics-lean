import MajorityDynamics.GraphProcess.EnumerationBounds.Preparation

noncomputable section
namespace MajorityDynamics.GraphProcess.BlockCountProbability
open Universal

def lossConstant (T : ℝ) : ℝ := 8*T^2*(T+1)^2

def CountRegime (N p D : ℝ) (L K : ℕ) : Prop :=
  0 < K ∧ K < L ∧ (K : ℝ) ≤ N^2 ∧
    ((K : ℝ)-(L : ℝ)*p)^2/((L : ℝ)*p*(1-p)) ≤ D*N

theorem lossConstant_pos {T : ℝ} (hT : 1 < T) : 0 < lossConstant T := by
  unfold lossConstant
  positivity

set_option maxHeartbeats 800000 in
theorem loss_bound {N T p L K : ℝ}
    (hN : 0 < N) (hT : 1 < T) (hp : 0 < p) (hps : p ≤ 1/2)
    (hL : N^2/(4*T^2) ≤ L)
    (hdev : |K-L*p| ≤ (T+1)*N*Real.sqrt (p*N)) :
    (K-L*p)^2/(L*p*(1-p)) ≤ lossConstant T*N := by
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < L := (div_pos (sq_pos_of_pos hN) (by positivity)).trans_le hL
  have hden : 0 < L*p*(1-p) := mul_pos (mul_pos hL0 hp) (by linarith)
  have hs2 := Real.sq_sqrt (mul_pos hp hN).le
  have hd2 : (K-L*p)^2 ≤ (T+1)^2*N^2*(p*N) := by
    have hh := sq_le_sq₀ (abs_nonneg (K-L*p))
      (show 0 ≤ (T+1)*N*Real.sqrt (p*N) by positivity) |>.2 hdev
    rw [sq_abs] at hh
    calc
      (K-L*p)^2 ≤ ((T+1)*N*Real.sqrt (p*N))^2 := hh
      _ = (T+1)^2*N^2*(p*N) := by rw [mul_pow, mul_pow, hs2]
  apply (div_le_iff₀ hden).mpr
  have hLL := (div_le_iff₀ (by positivity : 0 < 4*T^2)).mp hL
  have hh := mul_le_mul_of_nonneg_right hLL
    (show 0 ≤ (T+1)^2*N*p by positivity)
  have hh' := mul_le_mul_of_nonneg_left
    (show 1/2 ≤ 1-p by linarith)
    (show 0 ≤ 8*T^2*(T+1)^2*N*L*p by positivity)
  unfold lossConstant
  nlinarith only [hd2, hh, hh']

theorem error_identity {N T p : ℝ} (hN : 0 < N) (hp : 0 < p) :
    T*N^2*p/Real.sqrt (p*N) = T*N*Real.sqrt (p*N) := by
  have hs : 0 < Real.sqrt (p*N) := Real.sqrt_pos.mpr (mul_pos hp hN)
  apply (div_eq_iff hs.ne').mpr
  have hh := Real.sq_sqrt (mul_pos hp hN).le
  calc
    T*N^2*p = T*N*(p*N) := by ring
    _ = T*N*(Real.sqrt (p*N))^2 := by rw [hh]
    _ = _ := by ring

set_option maxHeartbeats 800000 in
theorem cross_real_bounds {N T p a b m : ℝ}
    (hN : 0 < N) (hT : 1 < T) (hp : 0 < p)
    (hx : 4*T^6 ≤ p*N) (hps : p ≤ 1/(8*T^2))
    (ha : N/T ≤ a) (hb : N/T ≤ b) (haN : a ≤ N) (hbN : b ≤ N)
    (hm : |m-p*a*b| ≤ T*N^2*p/Real.sqrt (p*N)) :
    0 < m ∧ m < a*b ∧ m ≤ N^2 ∧
      (m-(a*b)*p)^2/((a*b)*p*(1-p)) ≤ lossConstant T*N := by
  have hT0 : 0 < T := by linarith
  have ha0 : 0 < a := (div_pos hN hT0).trans_le ha
  have hb0 : 0 < b := (div_pos hN hT0).trans_le hb
  have hab0 := mul_pos ha0 hb0
  have he := EnumerationBounds.pair_estimates hN hT hp hx ha hb haN hbN hm
  have hsmall := (le_div_iff₀ (by positivity : 0 < 8*T^2)).mp hps
  have hT2 : 1 < T^2 := by nlinarith
  have hp2 : p ≤ 1/2 := by nlinarith
  have hlo : 0 < m/(a*b) := (div_pos hp (by positivity)).trans_le he.2.2.2.1
  have hm0 : 0 < m := (div_pos_iff_of_pos_right hab0).mp hlo
  have hhi : m/(a*b) ≤ 1/2 := by nlinarith [he.2.2.2.2]
  have hmab : m ≤ (a*b)/2 := by
    have hh := (div_le_iff₀ hab0).mp hhi
    linarith
  have hab : a*b ≤ N^2 := by nlinarith [mul_le_mul haN hbN hb0.le hN.le]
  have hna := (div_le_iff₀ hT0).mp ha
  have hnb := (div_le_iff₀ hT0).mp hb
  have hprod := mul_le_mul hna hnb hN.le (by positivity : 0 ≤ a*T)
  have hL : N^2/(4*T^2) ≤ a*b := by
    apply (div_le_iff₀ (by positivity : 0 < 4*T^2)).mpr
    nlinarith [mul_nonneg (show 0 ≤ a*b by positivity) (sq_nonneg T)]
  have hdev : |m-(a*b)*p| ≤ (T+1)*N*Real.sqrt (p*N) := by
    have hh := hm
    rw [error_identity hN hp] at hh
    calc
      |m-(a*b)*p| = |m-p*a*b| := by congr 1; ring
      _ ≤ T*N*Real.sqrt (p*N) := hh
      _ ≤ (T+1)*N*Real.sqrt (p*N) := by
        nlinarith [mul_nonneg hN.le (Real.sqrt_nonneg (p*N))]
  exact ⟨hm0, by linarith, by linarith, loss_bound hN hT hp hp2 hL hdev⟩

set_option maxHeartbeats 1200000 in
theorem internal_real_bounds {N T p a m : ℝ}
    (hN : 0 < N) (hT : 1 < T) (hp : 0 < p)
    (hx1 : 1 ≤ p*N) (hx : 4*T^6 ≤ p*N) (hps : p ≤ 1/(8*T^2))
    (hNs : 2*T ≤ N) (ha : N/T ≤ a) (haN : a ≤ N)
    (hm : |m-p*a*a| ≤ T*N^2*p/Real.sqrt (p*N)) :
    0 < m/2 ∧ m/2 < a*(a-1)/2 ∧ m/2 ≤ N^2 ∧
      (m/2-(a*(a-1)/2)*p)^2/((a*(a-1)/2)*p*(1-p)) ≤ lossConstant T*N := by
  have hT0 : 0 < T := by linarith
  have ha0 : 0 < a := (div_pos hN hT0).trans_le ha
  have hsize := EnumerationBounds.size_estimates hT hNs ha
  have ham : 0 < a-1 := by linarith [hsize.1]
  have hab0 := mul_pos ha0 ham
  have he := EnumerationBounds.internal_estimates hN hT hp hx hNs ha haN hm
  have hsmall := (le_div_iff₀ (by positivity : 0 < 8*T^2)).mp hps
  have hT2 : 1 < T^2 := by nlinarith
  have hp2 : p ≤ 1/2 := by nlinarith
  have hlo : 0 < (m/a)/(a-1) := (div_pos hp (by positivity)).trans_le he.1
  have hm0 : 0 < m := by
    have hh := (div_pos_iff_of_pos_right ham).mp hlo
    exact (div_pos_iff_of_pos_right ha0).mp hh
  have hhi : (m/a)/(a-1) ≤ 1/2 := by nlinarith [he.2]
  have hmab : m ≤ a*(a-1)/2 := by
    have hh := (div_le_iff₀ ham).mp hhi
    have hh' := (div_le_iff₀ ha0).mp hh
    nlinarith only [hh']
  have haa : a*a ≤ N^2 := by nlinarith [mul_le_mul haN haN ha0.le hN.le]
  have hna := (div_le_iff₀ hT0).mp ha
  have hnb := (div_le_iff₀ (by positivity : 0 < 2*T)).mp hsize.2
  have hprod := mul_le_mul hna hnb hN.le (by positivity : 0 ≤ a*T)
  have hL : N^2/(4*T^2) ≤ a*(a-1)/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 4*T^2)).mpr
    nlinarith only [hprod]
  have hs : 1 ≤ Real.sqrt (p*N) := by
    have hh := Real.sq_sqrt (mul_pos hp hN).le
    have hh0 := Real.sqrt_nonneg (p*N)
    nlinarith
  have hloop : |p*a/2| ≤ N*Real.sqrt (p*N)/2 := by
    rw [abs_of_nonneg (by positivity)]
    have hh := mul_le_mul_of_nonneg_left haN hp.le
    have hh' := mul_le_mul_of_nonneg_left (show p ≤ Real.sqrt (p*N) by linarith) hN.le
    nlinarith only [hh, hh']
  have hdev : |m/2-(a*(a-1)/2)*p| ≤ (T+1)*N*Real.sqrt (p*N) := by
    have hh := hm
    rw [error_identity hN hp] at hh
    calc
      |m/2-(a*(a-1)/2)*p| = |(m-p*a*a)/2+p*a/2| := by congr 1; ring
      _ ≤ |(m-p*a*a)/2|+|p*a/2| := abs_add_le _ _
      _ ≤ T*N*Real.sqrt (p*N)/2+N*Real.sqrt (p*N)/2 := by
        rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
        exact add_le_add (div_le_div_of_nonneg_right hh (by norm_num)) hloop
      _ ≤ (T+1)*N*Real.sqrt (p*N) := by
        nlinarith [mul_nonneg hN.le (Real.sqrt_nonneg (p*N))]
  exact ⟨by positivity, by nlinarith only [hmab, hab0], by nlinarith only [hmab, haa, ha0],
    loss_bound hN hT hp hp2 hL hdev⟩

theorem half_toNat_real {m : ℤ} (hm : 0 ≤ m) (heven : Even m) :
    ((m/2).toNat : ℝ) = (m : ℝ)/2 := by
  obtain ⟨k, hk⟩ := heven
  have hdiv : m/2 = k := by omega
  have hk0 : 0 ≤ k := by omega
  have hh : (2:ℤ)*((m/2).toNat : ℤ) = m := by
    rw [hdiv, Int.toNat_of_nonneg hk0]
    omega
  have hh' : (2:ℝ)*((m/2).toNat : ℝ) = (m : ℝ) := by exact_mod_cast hh
  linarith

variable {V : Type*} [Fintype V] {n : ℕ}

theorem finite_regime (y : Local.CoarseData V n) {T p : ℝ}
    (hN : 0 < (Fintype.card V : ℝ)) (hT : 1 < T) (hp : 0 < p)
    (hx1 : 1 ≤ p*Fintype.card V) (hx : 4*T^6 ≤ p*Fintype.card V)
    (hps : p ≤ 1/(8*T^2)) (hNs : 2*T ≤ (Fintype.card V : ℝ))
    (hsizes : ∀ s, (Fintype.card V : ℝ)/T ≤ (y.sizes s : ℝ))
    (hcounts : ∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
      T*(Fintype.card V : ℝ)^2*p/Real.sqrt (p*Fintype.card V)) :
    (∀ s, CountRegime (Fintype.card V) p (lossConstant T)
      ((y.sizes s).choose 2) ((y.edge s s/2).toNat)) ∧
    (∀ s t, s ≠ t → CountRegime (Fintype.card V) p (lossConstant T)
      (y.sizes s*y.sizes t) ((y.edge s t).toNat)) := by
  have hup : ∀ s, (y.sizes s : ℝ) ≤ Fintype.card V := by
    intro s
    exact_mod_cast y.sizes_le_card s
  constructor
  · intro s
    have hh := internal_real_bounds hN hT hp hx1 hx hps hNs (hsizes s) (hup s)
      (hcounts s s)
    have hc : (((y.sizes s).choose 2 : ℕ) : ℝ) =
        (y.sizes s : ℝ)*((y.sizes s : ℝ)-1)/2 := by rw [Nat.cast_choose_two]
    have hk := half_toNat_real (y.edge_nonneg s s) (y.edge_even s)
    rw [← hk, ← hc] at hh
    exact ⟨by exact_mod_cast hh.1, by exact_mod_cast hh.2.1, hh.2.2⟩
  · intro s t _hst
    have hh := cross_real_bounds hN hT hp hx hps (hsizes s) (hsizes t)
      (hup s) (hup t) (hcounts s t)
    have hk : ((y.edge s t).toNat : ℝ) = (y.edge s t : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (y.edge_nonneg s t)
    rw [← hk, ← Nat.cast_mul] at hh
    exact ⟨by exact_mod_cast hh.1, by exact_mod_cast hh.2.1, hh.2.2⟩

universe u

theorem uniform_regime {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ y : Local.CoarseData V n,
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
      1 ≤ (N : ℝ) ∧ 0 < p ∧ p < 1 ∧
      (∀ s, CountRegime N p (lossConstant T)
        ((y.sizes s).choose 2) ((y.edge s s/2).toNat)) ∧
      (∀ s t, s ≠ t → CountRegime N p (lossConstant T)
        (y.sizes s*y.sizes t) ((y.edge s t).toNat)) := by
  obtain ⟨N₀, h₀⟩ := EnumerationBounds.eventually_window hθlo hθhi hT
    (L := max 1 (4*T^6)) (U := 1/(8*T^2)) (M := 2*T)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (by positivity) (by positivity)
  refine ⟨N₀, ?_⟩
  intro N hNN V inst hcard p hlo hhi y hsizes hcounts
  obtain ⟨hN, hp, hNs, hx, hps⟩ := h₀ N hNN p hlo hhi
  have hx1 : 1 ≤ p*N := (le_max_left _ _).trans hx
  have hxT : 4*T^6 ≤ p*N := (le_max_right _ _).trans hx
  have hsmall := (le_div_iff₀ (by positivity : 0 < 8*T^2)).mp hps
  have hp1 : p < 1 := by
    have hT2 : 1 < T^2 := by nlinarith
    nlinarith
  subst N
  exact ⟨by linarith, hp, hp1,
    finite_regime y hN hT hp hx1 hxT hps hNs hsizes hcounts⟩

end MajorityDynamics.GraphProcess.BlockCountProbability
