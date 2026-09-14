import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Regime
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.SparseNumerics
noncomputable section
universe u v
open scoped BigOperators
namespace MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Numerics
open Literature.EdgeProbabilities
theorem eventually_average_regime_sparse {θ T A K : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T)
    (hK : 0 < K) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-(1/2:ℝ)) →
      ∀ c D : ℝ, p*N/K ≤ c → |D-c| ≤ A*(p*N)^((4:ℝ)/7)+1 →
      A*(p*N)^((4:ℝ)/7)+1 ≤ p*N/(2*K) ∧ p*N/(2*K) ≤ D ∧
        2*(A*(p*N)^((4:ℝ)/7)+1) ≤ D^((7:ℝ)/12) := by
  obtain ⟨X₁,hX₁,h₁⟩ := GraphProcess.EnumerationBounds.eventually_mul_rpow_le
    (a:=(4:ℝ)/7) (b:=1) (A:=A) (B:=1/(4*K)) (by norm_num) (by positivity)
  obtain ⟨X₂,hX₂,h₂⟩ := GraphProcess.EnumerationBounds.eventually_mul_rpow_le
    (a:=0) (b:=1) (A:=1) (B:=1/(4*K)) (by norm_num) (by positivity)
  obtain ⟨N₁,hN₁⟩ := GraphProcess.EnumerationBounds.eventually_band_window (η:=(1/2:ℝ)) (by norm_num) hθhi hT (L:=max X₁ X₂) (hX₁.trans_le (le_max_left _ _))
    (U:=1) zero_lt_one (M:=1) zero_lt_one
  obtain ⟨N₂,hN₂⟩ := eventually_degree_gap_sparse hθlo hθhi hT (A:=2*A) (B:=2)
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

theorem eventually_finite_average_sparse {θ T A K : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hK : 1 ≤ K) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-(1/2:ℝ)) →
      ∀ (V : Type*) [Fintype V], 0 < Fintype.card V → ∀ (d : V → ℝ) (c : ℝ),
        p*N/K ≤ c → c ≤ K*(p*N) →
        (∀ v, |d v-c| ≤ A*(p*N)^((4:ℝ)/7)+1) →
        let D := (∑ v, d v)/(Fintype.card V)
        p*N/(2*K) ≤ D ∧ D ≤ 2*K*(p*N) ∧
        (∀ v, |d v-D| ≤ D^((7:ℝ)/12)) := by
  have hK0 : 0 < K := by linarith
  obtain ⟨N₁,h₁⟩ := eventually_average_regime_sparse hθlo hθhi hT (A:=A) hK0
  obtain ⟨N₂,h₂⟩ := GraphProcess.EnumerationBounds.eventually_band_window (η:=(1/2:ℝ)) (by norm_num) hθhi hT (L:=1) zero_lt_one (U:=1) zero_lt_one (M:=1) zero_lt_one
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

theorem eventually_graphWindow_sparse {θ T A K : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hK : 1 ≤ K) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ, SparseDensityWindow θ T p N →
      ∀ (V : Type*) [Fintype V] (n m : ℕ) (d : V → ℕ),
        GraphWindow N n m p K A d →
        GraphConditions n m ((7:ℝ)/12) d ∧
        p*N/(2*K) ≤ graphAverage n m ∧ graphAverage n m ≤ 2*K*(p*N) := by
  obtain ⟨N₁,h₁⟩ := eventually_finite_average_sparse hθlo hθhi hT (A:=A) hK
  obtain ⟨N₂,h₂⟩ := GraphProcess.EnumerationBounds.eventually_band_window (η:=(1/2:ℝ)) (by norm_num) hθhi hT (L:=1) zero_lt_one (U:=1) zero_lt_one (M:=1) zero_lt_one
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

theorem eventually_bipartiteWindow_sparse {θ T A K : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hK : 1 ≤ K) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ, SparseDensityWindow θ T p N →
      ∀ (L : Type u) (R : Type v) [Fintype L] [Fintype R] (ell n m : ℕ) (a : L → ℕ) (b : R → ℕ),
        BipartiteWindow N ell n m p K A a b →
        BipartiteConditions ell n m ((7:ℝ)/12) a b ∧
        p*N/(2*K) ≤ leftAverage ell m ∧ leftAverage ell m ≤ 2*K*(p*N) ∧
        p*N/(2*K) ≤ rightAverage n m ∧ rightAverage n m ≤ 2*K*(p*N) := by
  obtain ⟨N₁,h₁⟩ := eventually_finite_average_sparse.{u} hθlo hθhi hT (A:=A) hK
  obtain ⟨N₁R,h₁R⟩ := eventually_finite_average_sparse.{v} hθlo hθhi hT (A:=A) hK
  obtain ⟨N₂,h₂⟩ := GraphProcess.EnumerationBounds.eventually_band_window (η:=(1/2:ℝ)) (by norm_num) hθhi hT (L:=1) zero_lt_one (U:=1) zero_lt_one (M:=1) zero_lt_one
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
