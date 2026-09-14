import MajorityDynamics.Probability.DegreeConcentration.Graph
import MajorityDynamics.Probability.DegreeConcentration.Bipartite

/-!
# Lemma A.10 (`lem:gamma_bound`): the public endpoints

The constant is the manuscript's `C_{A.10}(θ,T,K) = max{160 (K+2), 20 T² (K+T)}`; it does not
depend on `θ`. The threshold `n₀ = ⌈T²⌉₊ + 2` only serves to make every admissible density
satisfy `0 < p < 1` (`density_pos_lt_one`) and to have `n ≥ 2`; the two probability bounds
`graph_bound` and `bipartite_bound` hold for every `p ∈ (0,1]`.

* `degree_concentration : DegreeConcentrationTheorem` — both conclusions with one `C`, `n₀`.
* `graph_degree_concentration`, `bipartite_degree_concentration` — the two halves.
* `bipartite_graph_degree_concentration` — the bipartite conclusion for the simple-graph law
  on `Fin ℓ ⊕ Fin n`, with the event written through vertex degrees.
* `degree_concentration_real : RealDegreeConcentrationTheorem` — literal real densities.
-/

noncomputable section

open unitInterval

namespace MajorityDynamics.Probability.DegreeConcentration

/-- `C_{A.10}(θ,T,K) = max{160 (K+2), 20 T² (K+T)}`. -/
def gammaConstant (T K : ℝ) : ℝ := max (160 * (K + 2)) (20 * T ^ 2 * (K + T))

/-- The threshold `n₀ = ⌈T²⌉₊ + 2`. -/
def gammaThreshold (T : ℝ) : ℕ := ⌈T ^ 2⌉₊ + 2

theorem gammaConstant_pos (T K : ℝ) (hK : 0 < K) : 0 < gammaConstant T K :=
  lt_max_of_lt_left (by linarith)

theorem two_le_gammaThreshold (T : ℝ) : 2 ≤ gammaThreshold T := by
  unfold gammaThreshold
  omega

/-- For `n ≥ n₀` every density in the interval `(T⁻¹ n^{-θ}, T n^{-θ})` lies in `(0,1)`. -/
theorem density_pos_lt_one (θ T : ℝ) (hθ : 1 / 2 < θ) (hT : 1 < T) (n : ℕ)
    (hn : gammaThreshold T ≤ n) (p : ℝ) (hp : densityRange θ T n p) : 0 < p ∧ p < 1 := by
  obtain ⟨hlow, hup⟩ := hp
  have hn2 : (2 : ℝ) ≤ n := by
    have := two_le_gammaThreshold T
    exact_mod_cast this.trans hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hT0 : 0 < T := by linarith
  have hT2 : T ^ 2 ≤ n := by
    have h1 : T ^ 2 ≤ (⌈T ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈T ^ 2⌉₊ : ℕ) : ℝ) ≤ n := by
      have : ⌈T ^ 2⌉₊ ≤ n := by
        unfold gammaThreshold at hn
        omega
      exact_mod_cast this
    linarith
  constructor
  · have : 0 < T⁻¹ * (n : ℝ) ^ (-θ) := mul_pos (inv_pos.mpr hT0) (Real.rpow_pos_of_pos hn0 _)
    linarith
  · have hsqrt : T ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow]
      exact (Real.le_sqrt hT0.le hn0.le).mpr hT2
    have hθn : (n : ℝ) ^ ((1 : ℝ) / 2) ≤ (n : ℝ) ^ θ :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hθ.le
    have hTθ : T ≤ (n : ℝ) ^ θ := hsqrt.trans hθn
    have hpos : 0 < (n : ℝ) ^ θ := Real.rpow_pos_of_pos hn0 _
    have : T * (n : ℝ) ^ (-θ) ≤ 1 := by
      rw [Real.rpow_neg hn0.le, ← div_eq_mul_inv, div_le_one hpos]
      exact hTθ
    linarith

/-- Lemma A.10 with a common constant and threshold for both conclusions. -/
theorem degree_concentration : DegreeConcentrationTheorem := by
  intro θ T K hθ _ hT hK
  refine ⟨gammaConstant T K, gammaConstant_pos T K hK, gammaThreshold T, fun n hn p hp ↦ ?_⟩
  obtain ⟨hp0, _⟩ := density_pos_lt_one θ T hθ hT n hn p hp
  have hn2 : 2 ≤ n := (two_le_gammaThreshold T).trans hn
  refine ⟨graph_bound (by omega) p hp0 _ K (le_max_left _ _), fun ℓ hℓ ↦ ?_⟩
  exact bipartite_bound hn2 p hp0 T hT hℓ _ K hK.le (le_max_right _ _)

/-- Lemma A.10(i). -/
theorem graph_degree_concentration : GraphDegreeConcentrationTheorem := by
  intro θ T K hθ hθ1 hT hK
  obtain ⟨C, hC, n₀, h⟩ := degree_concentration θ T K hθ hθ1 hT hK
  exact ⟨C, hC, n₀, fun n hn p hp ↦ (h n hn p hp).1⟩

/-- Lemma A.10(ii). -/
theorem bipartite_degree_concentration : BipartiteDegreeConcentrationTheorem := by
  intro θ T K hθ hθ1 hT hK
  obtain ⟨C, hC, n₀, h⟩ := degree_concentration θ T K hθ hθ1 hT hK
  exact ⟨C, hC, n₀, fun n hn p hp ↦ (h n hn p hp).2⟩

/-- Lemma A.10(ii) for the simple bipartite graph law on `Fin ℓ ⊕ Fin n`. -/
theorem bipartite_graph_degree_concentration : BipartiteGraphDegreeConcentrationTheorem := by
  intro θ T K hθ hθ1 hT hK
  obtain ⟨C, hC, n₀, h⟩ := bipartite_degree_concentration θ T K hθ hθ1 hT hK
  refine ⟨C, hC, n₀, fun n hn p hp ℓ hℓ ↦ ?_⟩
  rw [bipartiteGraphLaw_bad]
  exact h n hn p hp ℓ hℓ

/-- Lemma A.10 for literal real densities; the endpoint supplies `0 < p < 1`. -/
theorem degree_concentration_real : RealDegreeConcentrationTheorem := by
  intro θ T K hθ hθ1 hT hK
  obtain ⟨C, hC, n₀, h⟩ := degree_concentration θ T K hθ hθ1 hT hK
  refine ⟨C, hC, max n₀ (gammaThreshold T), fun n hn p hp1 hp2 ↦ ?_⟩
  have hp : densityRange θ T n p := ⟨hp1, hp2⟩
  have hpos := density_pos_lt_one θ T hθ hT n ((le_max_right _ _).trans hn) p hp
  exact ⟨hpos, h n ((le_max_left _ _).trans hn) ⟨p, hpos.1.le, hpos.2.le⟩ hp⟩

end MajorityDynamics.Probability.DegreeConcentration
