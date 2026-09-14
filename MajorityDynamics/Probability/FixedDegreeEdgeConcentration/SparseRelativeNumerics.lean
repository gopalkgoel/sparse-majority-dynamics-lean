import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.RelativeNumerics
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.SparseRegime
noncomputable section
open scoped BigOperators
namespace MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Numerics
open Literature.EdgeProbabilities
structure SparseRelativeData (N p K A : ℝ) : Prop where
  N_pos : 0 < N
  p_pos : 0 < p
  N_large : 4*K ≤ N
  degree_one : 1 ≤ p*N
  degree_large : 2*K ≤ p*N
  sparse : p ≤ 1/(16*K^2)
  radius_small : relativeRadius A (p*N) ≤ p*N/(4*K)
  log_degree : ∀ n : ℝ, 0 < n → n ≤ K*N → Real.log n ≤ p*N

theorem eventually_relativeData_sparse {θ T K A : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hK : 1 ≤ K) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ, SparseDensityWindow θ T p N → SparseRelativeData N p K A := by
  have hK0 : 0 < K := by linarith
  obtain ⟨X,hX,hpow⟩ := GraphProcess.EnumerationBounds.eventually_mul_rpow_le
    (a:=(4:ℝ)/7) (b:=1) (A:=2*(|A|+1)) (B:=1/(4*K)) (by norm_num) (by positivity)
  obtain ⟨N₁,h₁⟩ := GraphProcess.EnumerationBounds.eventually_band_window (η:=(1/2:ℝ)) (by norm_num) hθhi hT
    (L:=max X (2*K)) (hX.trans_le (le_max_left _ _)) (U:=1/(16*K^2)) (by positivity) (M:=4*K) (by positivity)
  obtain ⟨N₂,h₂⟩ := eventually_source_budget_sparse hθlo hθhi hT hK
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN p hp
  have hw := h₁ N ((le_max_left _ _).trans hN) p hp.1 hp.2
  have hs := h₂ N ((le_max_right _ _).trans hN) p hp.1 hp.2
  refine ⟨hw.1,hw.2.1,hw.2.2.1,hs.1,(le_max_right _ _).trans hw.2.2.2.1,hw.2.2.2.2,?_,hs.2⟩
  simpa [relativeRadius,Real.rpow_one,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using
    hpow (p*N) ((le_max_left _ _).trans hw.2.2.2.1)

theorem SparseRelativeData.dimension_pos {N p K A n : ℝ} (hw : SparseRelativeData N p K A)
    (hK : 1 ≤ K) (hn : N/K ≤ n) : 0 < n :=
  (div_pos hw.N_pos (by linarith)).trans_le hn

theorem SparseRelativeData.epsilon_pos {N p K A : ℝ} (hw : SparseRelativeData N p K A) :
    0 < epsilon N p := by
  exact div_pos (Real.rpow_pos_of_pos (mul_pos hw.p_pos hw.N_pos) _) hw.N_pos

theorem SparseRelativeData.dimension_four {N p K A n : ℝ} (hw : SparseRelativeData N p K A)
    (hK : 1 ≤ K) (hn : N/K ≤ n) : 4 ≤ n := by
  have hK0 : 0 < K := by linarith
  exact ((le_div_iff₀ hK0).mpr hw.N_large).trans hn

theorem SparseRelativeData.mean_small {N p K A n D : ℝ} (hw : SparseRelativeData N p K A)
    (hK : 1 ≤ K) (hn : N/K ≤ n) (hD : D ≤ 2*K*(p*N)) : D ≤ n/8 := by
  have hK0 : 0 < K := by linarith
  have hs := (le_div_iff₀ (by positivity : 0 < 16*K^2)).mp hw.sparse
  have hpn : 2*K*(p*N) ≤ N/(8*K) := by
    apply (le_div_iff₀ (by positivity : 0 < 8*K)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hs hw.N_pos.le]
  exact hD.trans (hpn.trans (by
    have heq : N/(8*K) = (N/K)/8 := by ring
    rw [heq]
    linarith))

theorem SparseRelativeData.reciprocal_le {N p K A n : ℝ} (hw : SparseRelativeData N p K A)
    (hK : 1 ≤ K) (hn : N/K ≤ n) : 1/n ≤ K*epsilon N p := by
  have hK0 : 0 < K := by linarith
  have hn0 := hw.dimension_pos hK hn
  have he : 1 ≤ (p*N)^((1:ℝ)/7) := Real.one_le_rpow hw.degree_one (by norm_num)
  have hrec : 1/n ≤ K/N := by
    apply (div_le_div_iff₀ hn0 hw.N_pos).mpr
    have hh := (div_le_iff₀ hK0).mp hn
    nlinarith
  apply hrec.trans
  unfold epsilon
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (by nlinarith) hw.N_pos.le

theorem SparseRelativeData.degree_lower {N p K A c d : ℝ} (hw : SparseRelativeData N p K A)
    (hK : 1 ≤ K) (hc : p*N/K ≤ c)
    (hd : |d-c| ≤ A*(p*N)^((4:ℝ)/7)+1) : p*N/(2*K) ≤ d := by
  have hK0 : 0 < K := by linarith
  have hr := window_le_radius (A:=A) hw.degree_one
  have hd' := (abs_le.mp hd).1
  have heq : p*N/K = 2*(p*N/(2*K)) := by ring
  have hrr : relativeRadius A (p*N)/2 ≤ p*N/(2*K) := by
    have hx : 0 ≤ p*N := (mul_pos hw.p_pos hw.N_pos).le
    have heq : p*N/(4*K) = (p*N/(2*K))/2 := by ring
    have hh := hw.radius_small
    rw [heq] at hh
    nlinarith [div_nonneg hx (by positivity : 0 ≤ 2*K)]
  linarith

/-- The square radius compared to the actual total product. -/
theorem SparseRelativeData.radius_product {N p K A n D : ℝ} (hw : SparseRelativeData N p K A)
    (hK : 1 ≤ K) (hn : N/K ≤ n) (hD : p*N/(2*K) ≤ D) :
    (relativeRadius A (p*N))^2 ≤
      (8*K^2*(|A|+1)^2)*epsilon N p*D*n := by
  have hK0 : 0 < K := by linarith
  have hx : 0 < p*N := mul_pos hw.p_pos hw.N_pos
  have hn0 := hw.dimension_pos hK hn
  have hD0 : 0 < D := (div_pos hx (by positivity)).trans_le hD
  have hprod := mul_le_mul hD hn (div_nonneg hw.N_pos.le hK0.le) hD0.le
  have hconst : 0 ≤ 8*K^2*(|A|+1)^2*epsilon N p := by
    exact mul_nonneg (by positivity) hw.epsilon_pos.le
  have hh := mul_le_mul_of_nonneg_left hprod hconst
  have heq : (8*K^2*(|A|+1)^2*epsilon N p)*(p*N/(2*K)*(N/K)) =
      (relativeRadius A (p*N))^2 := by
    rw [radius_sq hx hw.N_pos.ne']
    unfold epsilon
    field_simp
    ring
  rw [heq] at hh
  simpa [mul_assoc] using hh


/-- Exact graph main-term conversion on the original and residual windows. -/
theorem graph_approximation_relative_sparse {V : Type*} [Fintype V]
    {N n m : ℕ} {p K A : ℝ} {d : V → ℕ}
    (hK : 1 ≤ K) (hz : SparseRelativeData N p K A) (hw : GraphWindow N n m p K A d)
    (hDl : p*N/(2*K) ≤ graphAverage n m) (hDu : graphAverage n m ≤ 2*K*(p*N))
    (a b : V) :
    |graphApproximation n m (d a) (d b) - (d a:ℝ)*d b/(2*m)| ≤
      ((2+32*K^2*(|A|+1)^2)*K)*epsilon N p*((d a:ℝ)*d b/(2*m)) := by
  have hK0 : 0 < K := by linarith
  have hx : 0 < p*N := mul_pos hz.p_pos hz.N_pos
  have hn0 := hz.dimension_pos hK hw.size_lower
  have hn : 0 < n := by exact_mod_cast hn0
  have hn4 := hz.dimension_four hK hw.size_lower
  have hD0 : 0 < graphAverage n m := (div_pos hx (by positivity)).trans_le hDl
  have hDs := hz.mean_small hK hw.size_lower hDu
  have hav := graphWindow_average hw hn
  have hr := relativeRadius_nonneg (A:=A) hx.le
  have hh := hz.radius_product hK hw.size_lower hDl
  have he : epsilon N p ≤ K*epsilon N p := by nlinarith [hz.epsilon_pos]
  have hspread : (relativeRadius A (p*N))^2 ≤
      (8*K^2*(|A|+1)^2)*(K*epsilon N p)*graphAverage n m*n := by
    exact hh.trans (by
      have hmul := mul_le_mul_of_nonneg_left he
        (by positivity : 0 ≤ (8*K^2*(|A|+1)^2)*graphAverage n m*n)
      simpa [mul_assoc,mul_left_comm,mul_comm] using hmul)
  have hwgt : (d a:ℝ)*d b/(graphAverage n m*(n:ℝ)) = (d a:ℝ)*d b/(2*m) := by
    unfold graphAverage
    rw [div_mul_cancel₀ _ hn0.ne']
  have hc := graph_correction (n:=(n:ℝ)) (D:=graphAverage n m)
    (a:=(d a:ℝ)) (b:=(d b:ℝ)) (w:=(d a:ℝ)*d b/(2*m))
    (r:=relativeRadius A (p*N)) (ε:=K*epsilon N p) (K:=8*K^2*(|A|+1)^2)
    (by linarith) hD0 (by linarith) (by positivity) hwgt
    (centered_relativeRadius hz.degree_one hw.degree_window hav a)
    (centered_relativeRadius hz.degree_one hw.degree_window hav b) hr (by positivity)
    (mul_nonneg hK0.le hz.epsilon_pos.le) (hz.reciprocal_le hK hw.size_lower) hspread
  change |graphApproximation n m (d a) (d b) - (d a:ℝ)*d b/(2*m)| ≤ _ at hc
  exact hc.trans_eq (by ring)

/-- Full bipartite bracket conversion, including both empirical variance terms. -/
theorem bipartite_bracket_relative_sparse {L R : Type*} [Fintype L] [Fintype R]
    {N ell n m : ℕ} {p K A : ℝ} {a : L → ℕ} {b : R → ℕ}
    (hK : 1 ≤ K) (hz : SparseRelativeData N p K A) (hw : BipartiteWindow N ell n m p K A a b)
    (hsl : p*N/(2*K) ≤ leftAverage ell m) (hsu : leftAverage ell m ≤ 2*K*(p*N))
    (htl : p*N/(2*K) ≤ rightAverage n m) (htu : rightAverage n m ≤ 2*K*(p*N))
    (i : L) (j : R) :
    |bipartiteBracket ell n m a b i j - 1| ≤
      (48*K^2*(|A|+1)^2)*epsilon N p := by
  have hK0 : 0 < K := by linarith
  have hx : 0 < p*N := mul_pos hz.p_pos hz.N_pos
  have he0 := hz.dimension_pos hK hw.size_left_lower
  have hn0 := hz.dimension_pos hK hw.size_right_lower
  have hell : 0 < ell := by exact_mod_cast he0
  have hn : 0 < n := by exact_mod_cast hn0
  have hs0 : 0 < leftAverage ell m := (div_pos hx (by positivity)).trans_le hsl
  have ht0 : 0 < rightAverage n m := (div_pos hx (by positivity)).trans_le htl
  have hm0 : 0 < (m:ℝ) := by
    have hh := (lt_div_iff₀ he0).mp hs0
    linarith
  have hms : leftAverage ell m*(ell:ℝ) = (m:ℝ) := div_mul_cancel₀ _ he0.ne'
  have hmt : rightAverage n m*(n:ℝ) = (m:ℝ) := div_mul_cancel₀ _ hn0.ne'
  have hss := hz.mean_small hK hw.size_right_lower hsu
  have hts := hz.mean_small hK hw.size_left_lower htu
  have hr := relativeRadius_nonneg (A:=A) hx.le
  have hrsmall : relativeRadius A (p*N) ≤ p*N/(2*K) := by
    have hh := hz.radius_small
    have heq : p*N/(4*K) = (p*N/(2*K))/2 := by ring
    rw [heq] at hh
    nlinarith [div_pos hx (by positivity : 0 < 2*K)]
  have hav := bipartiteWindow_averages hw hell hn
  have ha : ∀ v, |(a v:ℝ)-leftAverage ell m| ≤ relativeRadius A (p*N) :=
    centered_relativeRadius hz.degree_one hw.degree_left hav.1
  have hb : ∀ v, |(b v:ℝ)-rightAverage n m| ≤ relativeRadius A (p*N) :=
    centered_relativeRadius hz.degree_one hw.degree_right hav.2
  have hva := variance_le_window_sq (d:=a) (show 0 < Fintype.card L by rw [hw.card_left]; exact hell) hr ha
  have hvb := variance_le_window_sq (d:=b) (show 0 < Fintype.card R by rw [hw.card_right]; exact hn) hr hb
  have hdm : (m:ℝ)/2 ≤ m-rightAverage n m*leftAverage ell m := by
    have hh := mul_le_mul_of_nonneg_left hss ht0.le
    nlinarith [hmt]
  have hc := bipartite_correction_simple (a:=(a i:ℝ)) (b:=(b j:ℝ))
    (s:=leftAverage ell m) (t:=rightAverage n m) (m:=(m:ℝ)) (ell:=(ell:ℝ)) (n:=(n:ℝ))
    hs0 ht0 hm0 hms hmt hdm (by linarith) (by linarith) hr
    (hrsmall.trans hsl) (hrsmall.trans htl) (ha i) (hb j) hva.1 hva.2 hvb.1 hvb.2
  have hp := hz.radius_product hK hw.size_left_lower hsl
  rw [mul_assoc _ (leftAverage ell m) (ell:ℝ), hms] at hp
  have hd : (relativeRadius A (p*N))^2/(m:ℝ) ≤
      8*K^2*(|A|+1)^2*epsilon N p := (div_le_iff₀ hm0).mpr hp
  change |bipartiteBracket ell n m a b i j-1| ≤ _ at hc
  exact hc.trans (by
    have hh := mul_le_mul_of_nonneg_left hd (by norm_num : (0:ℝ) ≤ 6)
    convert hh using 1 <;> ring)

end MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Numerics
