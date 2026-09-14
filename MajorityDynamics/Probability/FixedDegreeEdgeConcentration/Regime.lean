import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Numerics
import MajorityDynamics.Literature.EdgeProbabilities.Basic
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Basic
import Mathlib.Tactic

noncomputable section
universe u v
open scoped BigOperators
namespace MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Numerics

/-- Averaging the actual degree windows controls the actual source average. -/
theorem average_window {V : Type*} [Fintype V] {d : V → ℝ} {c r : ℝ}
    (hcard : 0 < Fintype.card V) (hd : ∀ v, |d v-c| ≤ r) :
    |(∑ v, d v)/(Fintype.card V)-c| ≤ r := by
  have hc : (0:ℝ) < Fintype.card V := by exact_mod_cast hcard
  have hsum : |∑ v, (d v-c)| ≤ (Fintype.card V:ℝ)*r := by
    calc
      _ ≤ ∑ v, |d v-c| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v : V, r := Finset.sum_le_sum (fun v _ => hd v)
      _ = _ := by simp
  rw [Finset.sum_sub_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  rw [show (∑ v, d v)/(Fintype.card V)-c =
    ((∑ v, d v)-(Fintype.card V:ℝ)*c)/(Fintype.card V) by field_simp,
    abs_div, abs_of_pos hc]
  exact (div_le_iff₀ hc).mpr (by simpa [mul_comm] using hsum)

theorem centered_window {V : Type*} [Fintype V] {d : V → ℝ} {c r : ℝ}
    (hcard : 0 < Fintype.card V) (hd : ∀ v, |d v-c| ≤ r) (v : V) :
    |d v-(∑ w, d w)/(Fintype.card V)| ≤ 2*r := by
  have havg := average_window hcard hd
  calc
    _ ≤ |d v-c| + |c-(∑ w, d w)/(Fintype.card V)| := abs_sub_le _ _ _
    _ = |d v-c| + |(∑ w, d w)/(Fintype.card V)-c| := by rw [abs_sub_comm c]
    _ ≤ 2*r := by linarith [hd v]

/-- Deleting a vertex decrements each remaining degree by zero or one. -/
theorem decrement_window {d c r : ℝ} {d' : ℝ}
    (hd : |d-c| ≤ r) (hlo : d-1 ≤ d') (hhi : d' ≤ d) :
    |d'-c| ≤ r+1 := by
  rw [abs_le] at hd ⊢
  constructor <;> linarith

/-- Natural subtraction with the actual feasibility hypothesis preserves the decrement bound. -/
theorem nat_decrement_window {d k : ℕ} {c r : ℝ}
    (hk : k ≤ 1) (hkd : k ≤ d) (hd : |(d:ℝ)-c| ≤ r) :
    |((d-k:ℕ):ℝ)-c| ≤ r+1 := by
  rw [Nat.cast_sub hkd]
  have hkR : (k:ℝ) ≤ 1 := by exact_mod_cast hk
  exact decrement_window hd (by linarith) (by have := Nat.cast_nonneg (α:=ℝ) k; linarith)

/-- The source spread follows from the original degree window and a lower average bound. -/
theorem source_spread {V : Type*} [Fintype V] {d : V → ℝ} {c r D : ℝ}
    (hcard : 0 < Fintype.card V) (hd : ∀ v, |d v-c| ≤ r)
    (hD : D = (∑ v, d v)/(Fintype.card V)) (hgap : 2*r ≤ D^((7:ℝ)/12)) :
    ∀ v, |d v-D| ≤ D^((7:ℝ)/12) := by
  intro v
  rw [hD] at hgap ⊢
  exact (centered_window hcard hd v).trans hgap

/-- Original and one-vertex residual windows satisfy the source's `7/12` spread,
 uniformly in all actual average degrees. -/
theorem eventually_average_regime {θ T A K : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hK : 0 < K) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-θ) →
      ∀ c D : ℝ, p*N/K ≤ c → |D-c| ≤ A*(p*N)^((4:ℝ)/7)+1 →
      A*(p*N)^((4:ℝ)/7)+1 ≤ p*N/(2*K) ∧ p*N/(2*K) ≤ D ∧
        2*(A*(p*N)^((4:ℝ)/7)+1) ≤ D^((7:ℝ)/12) := by
  obtain ⟨X₁,hX₁,h₁⟩ := GraphProcess.EnumerationBounds.eventually_mul_rpow_le
    (a:=(4:ℝ)/7) (b:=1) (A:=A) (B:=1/(4*K)) (by norm_num) (by positivity)
  obtain ⟨X₂,hX₂,h₂⟩ := GraphProcess.EnumerationBounds.eventually_mul_rpow_le
    (a:=0) (b:=1) (A:=1) (B:=1/(4*K)) (by norm_num) (by positivity)
  obtain ⟨N₁,hN₁⟩ := GraphProcess.EnumerationBounds.eventually_window
    hθlo hθhi hT (L:=max X₁ X₂) (hX₁.trans_le (le_max_left _ _))
    (U:=1) zero_lt_one (M:=1) zero_lt_one
  obtain ⟨N₂,hN₂⟩ := eventually_degree_gap hθlo hθhi hT (A:=2*A) (B:=2)
    (K:=2*K) (by positivity)
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN p hlo hhi c D hc hD
  have hw := hN₁ N ((le_max_left _ _).trans hN) p hlo hhi
  have hg := hN₂ N ((le_max_right _ _).trans hN) p hlo hhi
  have ha := h₁ (p*N) ((le_max_left _ _).trans hw.2.2.2.1)
  have hb := h₂ (p*N) ((le_max_right _ _).trans hw.2.2.2.1)
  simp only [Real.rpow_one, Real.rpow_zero, mul_one] at ha hb
  have hr : A*(p*N)^((4:ℝ)/7)+1 ≤ p*N/(2*K) := by
    calc
      _ ≤ 1/(4*K)*(p*N)+1/(4*K)*(p*N) := add_le_add ha hb
      _ = _ := by ring
  have hlow : p*N/(2*K) ≤ D := by
    have h := (abs_le.mp hD).1
    have heq : p*N/K = 2*(p*N/(2*K)) := by ring
    linarith
  refine ⟨hr, hlow, ?_⟩
  have hp0 := hw.2.1
  have hmono := Real.rpow_le_rpow (by positivity : 0 ≤ p*N/(2*K)) hlow
    (by norm_num : (0:ℝ) ≤ 7/12)
  exact (by nlinarith : 2*(A*(p*N)^((4:ℝ)/7)+1) ≤ (p*N/(2*K))^((7:ℝ)/12)).trans hmono

/-- A reusable original-window source preparation, uniform over the carrier and every degree. -/
theorem eventually_finite_average {θ T A K : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hK : 1 ≤ K) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-θ) →
      ∀ (V : Type*) [Fintype V], 0 < Fintype.card V → ∀ (d : V → ℝ) (c : ℝ),
        p*N/K ≤ c → c ≤ K*(p*N) →
        (∀ v, |d v-c| ≤ A*(p*N)^((4:ℝ)/7)+1) →
        let D := (∑ v, d v)/(Fintype.card V)
        p*N/(2*K) ≤ D ∧ D ≤ 2*K*(p*N) ∧
        (∀ v, |d v-D| ≤ D^((7:ℝ)/12)) := by
  have hK0 : 0 < K := by linarith
  obtain ⟨N₁,h₁⟩ := eventually_average_regime hθlo hθhi hT (A:=A) hK0
  obtain ⟨N₂,h₂⟩ := GraphProcess.EnumerationBounds.eventually_window
    hθlo hθhi hT (L:=1) zero_lt_one (U:=1) zero_lt_one (M:=1) zero_lt_one
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN p hlo hhi V _ hcard d c hcl hcu hd
  have hw := h₂ N ((le_max_right _ _).trans hN) p hlo hhi
  have hav := average_window hcard hd
  have hh := h₁ N ((le_max_left _ _).trans hN) p hlo hhi c _ hcl hav
  have hx : 0 ≤ p*N := (mul_pos hw.2.1 hw.1).le
  have hsmall : p*N/(2*K) ≤ p*N := by
    apply (div_le_iff₀ (by positivity : 0 < 2*K)).mpr
    nlinarith
  have hupper : (∑ v, d v)/(Fintype.card V) ≤ 2*K*(p*N) := by
    have ha := (abs_le.mp hav).2
    have hkx := mul_le_mul_of_nonneg_right hK hx
    nlinarith [hh.1]
  exact ⟨hh.2.1,hupper,fun v => (centered_window hcard hd v).trans hh.2.2⟩

open Literature.EdgeProbabilities

theorem graphWindow_average {V : Type*} [Fintype V] {N n m : ℕ} {p K A : ℝ}
    {d : V → ℕ} (hw : GraphWindow N n m p K A d) (hn : 0 < n) :
    |graphAverage n m-p*N| ≤ A*(p*N)^((4:ℝ)/7)+1 := by
  have hc : 0 < Fintype.card V := by rw [hw.card]; exact hn
  have hh := average_window hc hw.degree_window
  have hs : (∑ v, (d v:ℝ)) = 2*(m:ℝ) := by exact_mod_cast hw.total
  simpa [hw.card,hs,graphAverage] using hh

theorem bipartiteWindow_averages {L R : Type*} [Fintype L] [Fintype R]
    {N ell n m : ℕ} {p K A : ℝ} {a : L → ℕ} {b : R → ℕ}
    (hw : BipartiteWindow N ell n m p K A a b) (he : 0 < ell) (hn : 0 < n) :
    |leftAverage ell m-p*n| ≤ A*(p*N)^((4:ℝ)/7)+1 ∧
      |rightAverage n m-p*ell| ≤ A*(p*N)^((4:ℝ)/7)+1 := by
  have hl := average_window (show 0 < Fintype.card L by rw [hw.card_left]; exact he) hw.degree_left
  have hr := average_window (show 0 < Fintype.card R by rw [hw.card_right]; exact hn) hw.degree_right
  have hsl : (∑ v, (a v:ℝ)) = (m:ℝ) := by exact_mod_cast hw.total_left
  have hsr : (∑ v, (b v:ℝ)) = (m:ℝ) := by exact_mod_cast hw.total_right
  exact ⟨by simpa [hw.card_left,hsl,leftAverage] using hl,
    by simpa [hw.card_right,hsr,rightAverage] using hr⟩

/-- The original and residual graph windows satisfy every finite source condition. -/
theorem eventually_graphWindow {θ T A K : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hK : 1 ≤ K) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ, DensityWindow θ T p N →
      ∀ (V : Type*) [Fintype V] (n m : ℕ) (d : V → ℕ),
        GraphWindow N n m p K A d →
        GraphConditions n m ((7:ℝ)/12) d ∧
        p*N/(2*K) ≤ graphAverage n m ∧ graphAverage n m ≤ 2*K*(p*N) := by
  obtain ⟨N₁,h₁⟩ := eventually_finite_average hθlo hθhi hT (A:=A) hK
  obtain ⟨N₂,h₂⟩ := GraphProcess.EnumerationBounds.eventually_window
    hθlo hθhi hT (L:=1) zero_lt_one (U:=1) zero_lt_one (M:=1) zero_lt_one
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN p hp V _ n m d hw
  have hn := h₂ N ((le_max_right _ _).trans hN) p hp.1 hp.2
  have hK0 : 0 < K := by linarith
  have hn0 : (0:ℝ) < n := (div_pos hn.1 hK0).trans_le hw.size_lower
  have hcard : 0 < Fintype.card V := by rw [hw.card]; exact_mod_cast hn0
  have hxl : p*N/K ≤ p*N := by
    apply (div_le_iff₀ hK0).mpr
    nlinarith [mul_le_mul_of_nonneg_right hK (mul_pos hn.2.1 hn.1).le]
  have hxu : p*N ≤ K*(p*N) := by nlinarith [mul_le_mul_of_nonneg_right hK (mul_pos hn.2.1 hn.1).le]
  have hh := h₁ N ((le_max_left _ _).trans hN) p hp.1 hp.2 V hcard
    (fun v => (d v:ℝ)) (p*N) hxl hxu hw.degree_window
  have hs : (∑ v, (d v:ℝ)) = 2*(m:ℝ) := by exact_mod_cast hw.total
  simp only [hs,hw.card] at hh
  change p*N/(2*K) ≤ graphAverage n m ∧ graphAverage n m ≤ 2*K*(p*N) ∧
    (∀ v, |(d v:ℝ)-graphAverage n m| ≤ (graphAverage n m)^((7:ℝ)/12)) at hh
  exact ⟨⟨hw.card,hw.bounded,hw.total,hh.2.2,hw.realized⟩,hh.1,hh.2.1⟩

/-- The bipartite source uses the actual two averages, with a common original error scale. -/
theorem eventually_bipartiteWindow {θ T A K : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hK : 1 ≤ K) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ, DensityWindow θ T p N →
      ∀ (L : Type u) (R : Type v) [Fintype L] [Fintype R] (ell n m : ℕ) (a : L → ℕ) (b : R → ℕ),
        BipartiteWindow N ell n m p K A a b →
        BipartiteConditions ell n m ((7:ℝ)/12) a b ∧
        p*N/(2*K) ≤ leftAverage ell m ∧ leftAverage ell m ≤ 2*K*(p*N) ∧
        p*N/(2*K) ≤ rightAverage n m ∧ rightAverage n m ≤ 2*K*(p*N) := by
  obtain ⟨N₁,h₁⟩ := eventually_finite_average.{u} hθlo hθhi hT (A:=A) hK
  obtain ⟨N₁R,h₁R⟩ := eventually_finite_average.{v} hθlo hθhi hT (A:=A) hK
  obtain ⟨N₂,h₂⟩ := GraphProcess.EnumerationBounds.eventually_window
    hθlo hθhi hT (L:=1) zero_lt_one (U:=1) zero_lt_one (M:=1) zero_lt_one
  refine ⟨max N₁ (max N₁R N₂), ?_⟩
  intro N hN p hp L R _ _ ell n m a b hw
  have hz := h₂ N (((le_max_right _ _).trans (le_max_right _ _)).trans hN) p hp.1 hp.2
  have hK0 : 0 < K := by linarith
  have he0 : (0:ℝ) < ell := (div_pos hz.1 hK0).trans_le hw.size_left_lower
  have hn0 : (0:ℝ) < n := (div_pos hz.1 hK0).trans_le hw.size_right_lower
  have hcl : 0 < Fintype.card L := by rw [hw.card_left]; exact_mod_cast he0
  have hcr : 0 < Fintype.card R := by rw [hw.card_right]; exact_mod_cast hn0
  have hnl : p*N/K ≤ p*n := by simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left hw.size_right_lower hz.2.1.le
  have hnu : p*n ≤ K*(p*N) := by nlinarith [mul_le_mul_of_nonneg_left hw.size_right_upper hz.2.1.le]
  have hel : p*N/K ≤ p*ell := by simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left hw.size_left_lower hz.2.1.le
  have heu : p*ell ≤ K*(p*N) := by nlinarith [mul_le_mul_of_nonneg_left hw.size_left_upper hz.2.1.le]
  have hl := h₁ N ((le_max_left _ _).trans hN) p hp.1 hp.2 L hcl
    (fun v => (a v:ℝ)) (p*n) hnl hnu hw.degree_left
  have hr := h₁R N (((le_max_left _ _).trans (le_max_right _ _)).trans hN) p hp.1 hp.2 R hcr
    (fun v => (b v:ℝ)) (p*ell) hel heu hw.degree_right
  have hsl : (∑ v, (a v:ℝ)) = (m:ℝ) := by exact_mod_cast hw.total_left
  have hsr : (∑ v, (b v:ℝ)) = (m:ℝ) := by exact_mod_cast hw.total_right
  simp only [hsl,hw.card_left] at hl
  simp only [hsr,hw.card_right] at hr
  exact ⟨⟨hw.card_left,hw.card_right,hw.bounded_left,hw.bounded_right,hw.total_left,
    hw.total_right,hl.2.2,hr.2.2,hw.realized⟩,hl.1,hl.2.1,hr.1,hr.2.1⟩

end MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Numerics
