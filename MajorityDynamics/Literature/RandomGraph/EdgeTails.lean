import MajorityDynamics.Literature.RandomGraph.OrderedPairs
import MajorityDynamics.Literature.RandomGraph.Bennett
import MajorityDynamics.Literature.RandomGraph.JumblednessExponent

noncomputable section
open MeasureTheory ProbabilityTheory
open MajorityDynamics.Paper
open scoped unitInterval

namespace MajorityDynamics.Literature.RandomGraph

lemma edgeCount_upper_tail {N : ℕ} (s : Set (Sym2 (Fin N)))
    (hs : s ⊆ Sym2.diagSetᶜ) (p : unitInterval)
    (hμ : 0 < (s.ncard : ℝ) * p) (t : ℝ) (ht : 0 ≤ t) :
    graphLaw N p {G | (s.ncard : ℝ) * p + t ≤ (edgeCount s G : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-((s.ncard : ℝ) * p *
        ((1 + t / ((s.ncard : ℝ) * p)) * Real.log (1 + t / ((s.ncard : ℝ) * p)) -
          t / ((s.ncard : ℝ) * p))))) := by
  have h := binomial_bennett s.ncard p hμ t ht
  have he := edgeCount_apply s hs p {k | (s.ncard : ℝ) * p + t ≤ (k : ℝ)}
  simp only [Set.mem_ofPred_eq] at he
  rw [graphLaw, he]
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal h

lemma edgeCount_lower_tail {N : ℕ} (s : Set (Sym2 (Fin N)))
    (hs : s ⊆ Sym2.diagSetᶜ) (p : unitInterval)
    (hμ : 0 < (s.ncard : ℝ) * p) (t : ℝ) (ht : 0 ≤ t) :
    graphLaw N p {G | (edgeCount s G : ℝ) ≤ (s.ncard : ℝ) * p - t} ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * ((s.ncard : ℝ) * p)))) := by
  have h := Concentration.binomial_lower_tail s.ncard p hμ t ht
  have he := edgeCount_apply s hs p {k | (k : ℝ) ≤ (s.ncard : ℝ) * p - t}
  simp only [Set.mem_ofPred_eq] at he
  rw [graphLaw, he]
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal h

/-- The entropy-scale upper bound for one oriented family, including the
zero-trial case. No independence between the two orientations is required. -/
lemma edgeFamily_upper_entropy {N : ℕ} (U W : Finset (Fin N))
    (s : Finset (Sym2 (Fin N))) (hs : (s : Set (Sym2 (Fin N))) ⊆ Sym2.diagSetᶜ)
    (hcard : s.card ≤ U.card * W.card) (p : unitInterval) (hp : 0 < (p : ℝ)) (hu : 0 < U.card) (hw : 0 < W.card)
    (hbal : (W.card : ℝ) ≤ (p : ℝ) * N * U.card) (K : ℝ) (hK : 1 ≤ K) :
    graphLaw N p {G | (s.card : ℝ) * p +
        K * Real.sqrt ((p : ℝ) * N * U.card * W.card) ≤
          (edgeCount s G : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-(K / 6 * subsetEntropy N W.card))) := by
  have hu' : (0 : ℝ) < U.card := by exact_mod_cast hu
  have hw' : (0 : ℝ) < W.card := by exact_mod_cast hw
  have hWN : (W.card : ℝ) ≤ N := by exact_mod_cast (show W.card ≤ N by simpa using Finset.card_le_univ W)
  have hN : (0 : ℝ) < N := hw'.trans_le hWN
  have hd : 0 < (p : ℝ) * N := mul_pos hp hN
  have ht : 0 < K * Real.sqrt ((p : ℝ) * N * U.card * W.card) := by positivity
  by_cases hm : s.card = 0
  · have hempty : {G : Graph N | (s.card : ℝ) * p +
        K * Real.sqrt ((p : ℝ) * N * U.card * W.card) ≤
          (edgeCount s G : ℝ)} = ∅ := by
      ext G
      have hc : edgeCount s G = 0 := by
        have := edgeCount_le (s : Set (Sym2 (Fin N))) G
        simpa [hm] using Nat.eq_zero_of_le_zero (by simpa [hm] using this)
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, hm, hc, Nat.cast_zero, zero_mul, zero_add]
      exact iff_false_intro (not_le.mpr ht)
    rw [hempty, measure_empty]
    exact bot_le
  · have hm' : 0 < (s.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hμ : 0 < (s.card : ℝ) * p := mul_pos hm' hp
    have hμle : (s.card : ℝ) * p ≤
        ((p : ℝ) * N) * U.card * W.card / N := by
      have hc : (s.card : ℝ) ≤ (U.card : ℝ) * W.card := by
        exact_mod_cast hcard
      have he : ((p : ℝ) * N) * U.card * W.card / N = (p : ℝ) * U.card * W.card := by
        field_simp
      rw [he]
      nlinarith
    have he := bennett_sqrt_ge_entropy (N := N) (d := (p : ℝ) * N)
      (u := U.card) (w := W.card) (μ := (s.card : ℝ) * p)
      (K := K) hu' hw' hd hWN hbal hμ hμle hK
    have htail := edgeCount_upper_tail (N := N) (s : Set (Sym2 (Fin N))) hs p
      (by simpa using hμ) _ ht.le
    simp only [Set.ncard_coe_finset] at htail
    exact htail.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg he)))

lemma edgeFamily_lower_entropy {N : ℕ} (U W : Finset (Fin N))
    (s : Finset (Sym2 (Fin N))) (hs : (s : Set (Sym2 (Fin N))) ⊆ Sym2.diagSetᶜ)
    (hcard : s.card ≤ U.card * W.card) (p : unitInterval) (hp : 0 < (p : ℝ)) (hu : 0 < U.card) (hw : 0 < W.card)
    (K : ℝ) (hK : 4 ≤ K) :
    graphLaw N p {G | (edgeCount s G : ℝ) ≤ (s.card : ℝ) * p -
        K * Real.sqrt ((p : ℝ) * N * U.card * W.card)} ≤
      ENNReal.ofReal (Real.exp (-(8 * subsetEntropy N W.card))) := by
  have hu' : (0 : ℝ) < U.card := by exact_mod_cast hu
  have hw' : (0 : ℝ) < W.card := by exact_mod_cast hw
  have hWN : (W.card : ℝ) ≤ N := by exact_mod_cast (show W.card ≤ N by simpa using Finset.card_le_univ W)
  have hN : (0 : ℝ) < N := hw'.trans_le hWN
  have hd : 0 < (p : ℝ) * N := mul_pos hp hN
  have ht : 0 < K * Real.sqrt ((p : ℝ) * N * U.card * W.card) := by positivity
  by_cases hm : s.card = 0
  · have hempty : {G : Graph N | (edgeCount s G : ℝ) ≤ (s.card : ℝ) * p -
        K * Real.sqrt ((p : ℝ) * N * U.card * W.card)} = ∅ := by
      ext G
      have hc : edgeCount s G = 0 := by
        have := edgeCount_le (s : Set (Sym2 (Fin N))) G
        simpa [hm] using Nat.eq_zero_of_le_zero (by simpa [hm] using this)
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, hm, hc, Nat.cast_zero, zero_mul, zero_sub]
      
      exact iff_false_intro (not_le.mpr (neg_neg_of_pos ht))
    rw [hempty, measure_empty]
    exact bot_le
  · have hm' : 0 < (s.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hμ : 0 < (s.card : ℝ) * p := mul_pos hm' hp
    have hμle : (s.card : ℝ) * p ≤
        ((p : ℝ) * N) * U.card * W.card / N := by
      have hc : (s.card : ℝ) ≤ (U.card : ℝ) * W.card := by
        exact_mod_cast hcard
      have he : ((p : ℝ) * N) * U.card * W.card / N = (p : ℝ) * U.card * W.card := by
        field_simp
      rw [he]
      nlinarith
    have he := gaussian_sqrt_ge_entropy (N := N) (d := (p : ℝ) * N)
      (u := U.card) (w := W.card) (μ := (s.card : ℝ) * p)
      (K := K) hu' hw' hd hN hμ hμle hK
    have htail := edgeCount_lower_tail (N := N) (s : Set (Sym2 (Fin N))) hs p
      (by simpa using hμ) _ ht.le
    simp only [Set.ncard_coe_finset] at htail
    exact htail.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg he)))

end MajorityDynamics.Literature.RandomGraph
