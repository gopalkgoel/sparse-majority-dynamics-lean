import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Main
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Signed
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Relative
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Joint
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Original
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Concentration
import MajorityDynamics.Probability.FixedDegreeEdgeConcentration.SignedInputs

noncomputable section
universe u v
open scoped Classical BigOperators
namespace MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Checks
open FixedDegreeSampling Numerics Literature.EdgeProbabilities

/-- Expanded original/residual graph window: the constants precede all size,
carrier, degree-vector and queried-edge data. -/
theorem graph_window_marginal {θ T K A : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-θ) →
      ∀ (V : Type u) [Fintype V] (n m : ℕ) (d : V → ℕ),
      Fintype.card V = n → (N:ℝ)/K ≤ n → (n:ℝ) ≤ K*N →
      (∀ v, d v ≤ n-1) → (∑ v, d v) = 2*m →
      (∀ v, |(d v:ℝ)-p*N| ≤ A*(p*N)^((4:ℝ)/7)+1) →
      (graphFamily d).Nonempty → ∀ a b, a ≠ b →
      |(fixedDegreeLaw d).real {G | G.Adj a b} - (d a:ℝ)*d b/(2*m)| ≤
        C*((p*N)^((1:ℝ)/7)/N)*((d a:ℝ)*d b/(2*m)) := by
  obtain ⟨C,hC,N₀,h⟩ := graph_window_relative_error.{u} hθlo hθhi hT hK (A:=A)
  refine ⟨C,hC,N₀,?_⟩
  intro N hN p hp₁ hp₂ V _ n m d hc hlo hhi hd ht hw hr a b hab
  exact h N hN p ⟨hp₁,hp₂⟩ V n m d ⟨hc,hlo,hhi,hd,ht,hw,hr⟩ a b hab

/-- Expanded two-sided original/residual window. Both deviations use reference N. -/
theorem bipartite_window_marginal {θ T K A : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-θ) →
      ∀ (L : Type u) (R : Type v) [Fintype L] [Fintype R]
      (ell n m : ℕ) (a : L → ℕ) (b : R → ℕ),
      Fintype.card L = ell → Fintype.card R = n →
      (N:ℝ)/K ≤ ell → (ell:ℝ) ≤ K*N → (N:ℝ)/K ≤ n → (n:ℝ) ≤ K*N →
      (∀ i, a i ≤ n) → (∀ j, b j ≤ ell) → (∑ i, a i) = m → (∑ j, b j) = m →
      (∀ i, |(a i:ℝ)-p*n| ≤ A*(p*N)^((4:ℝ)/7)+1) →
      (∀ j, |(b j:ℝ)-p*ell| ≤ A*(p*N)^((4:ℝ)/7)+1) →
      (bipartiteFamily a b).Nonempty → ∀ i j,
      |(bipartiteFixedDegreeLaw a b).real {E | (i,j) ∈ E} - (a i:ℝ)*b j/m| ≤
        C*((p*N)^((1:ℝ)/7)/N)*((a i:ℝ)*b j/m) := by
  obtain ⟨C,hC,N₀,h⟩ := bipartite_window_relative_error.{u,v} hθlo hθhi hT hK (A:=A)
  refine ⟨C,hC,N₀,?_⟩
  intro N hN p hp₁ hp₂ L R _ _ ell n m a b hL hR hel heu hnl hnu ha hb hta htb hwa hwb hr i j
  exact h N hN p ⟨hp₁,hp₂⟩ L R ell n m a b
    ⟨hL,hR,hel,heu,hnl,hnu,ha,hb,hta,htb,hwa,hwb,hr⟩ i j

/-- Corrected LW17 corollary after uniformization; the n-1 denominators and
the valid full-domain additive error are visible in the checked conclusion. -/
theorem graph_source_formula {θ T K A : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      DensityWindow θ T p N → ∀ (V : Type u) [Fintype V] (n m : ℕ) (d : V → ℕ),
      GraphWindow N n m p K A d → ∀ a b, a ≠ b →
      let D := 2*(m:ℝ)/n
      |(fixedDegreeLaw d).real {G | G.Adj a b} -
        (d a:ℝ)*d b/(D*((n:ℝ)-1))*(1-((d a:ℝ)-D)*((d b:ℝ)-D)/(D*((n:ℝ)-1-D)))| ≤
        C*(D/(n:ℝ)^2) := by
  exact graph_window_source_error.{u} hθlo hθhi hT hK

/-- Literal LW20 formula: the empirical variances and the prefactor on the entire
error remain in the checked conclusion. -/
theorem bipartite_source_formula {θ T K A : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      DensityWindow θ T p N → ∀ (L : Type u) (R : Type v) [Fintype L] [Fintype R]
      (ell n m : ℕ) (a : L → ℕ) (b : R → ℕ),
      BipartiteWindow N ell n m p K A a b → ∀ i j,
      let s := (m:ℝ)/ell
      let t := (m:ℝ)/n
      |(bipartiteFixedDegreeLaw a b).real {E | (i,j) ∈ E} -
        ((a i:ℝ)*b j/m)*(1-((a i:ℝ)-s)*((b j:ℝ)-t)/((m:ℝ)-t*s) +
          ((a i:ℝ)-s)*((∑ j, ((b j:ℝ)-t)^2)/Fintype.card R)/(t*s*((ell:ℝ)-t)) +
          ((b j:ℝ)-t)*((∑ i, ((a i:ℝ)-s)^2)/Fintype.card L)/(t*s*((n:ℝ)-s)))| ≤
        C*(((a i:ℝ)*b j/m)*((min s t)^(4*((7:ℝ)/12)-4)*(m:ℝ)/((n:ℝ)*ell))) := by
  exact bipartite_window_source_error.{u,v} hθlo hθhi hT hK


/-- Every original graph assumption, the actual two counts, both degree-mass
centers, the coefficient-one threshold, and the strict tail cost are expanded. -/
theorem original_graph {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-θ) →
      ∀ (V : Type u) [Fintype V] (m : ℕ) (d : V → ℕ),
      Fintype.card V = N → (∀ v, d v ≤ N-1) → (∑ v, d v) = 2*m →
      |(m:ℝ)-p*N*(N-1)/2| ≤ T*(N:ℝ)^2*p/Real.sqrt (p*N) →
      (∀ v, |(d v:ℝ)-p*N| ≤ (p*N)^((4:ℝ)/7)) → ∀ U : Finset V,
      (fixedDegreeLaw d).real {G | (N:ℝ)^2*p*Real.sqrt ((p*N)^((1:ℝ)/7)/N)*Real.log N ≤
        |(internalCount U G:ℝ)-(∑ v ∈ U, (d v:ℝ))^2/(4*m)|} < 1/Real.log N ∧
      (fixedDegreeLaw d).real {G | (N:ℝ)^2*p*Real.sqrt ((p*N)^((1:ℝ)/7)/N)*Real.log N ≤
        |(cutCount U G:ℝ)-(∑ v ∈ U, (d v:ℝ))*(∑ v ∈ Finset.univ \ U, (d v:ℝ))/(2*m)|} <
          1/Real.log N := by
  obtain ⟨N₀,h⟩ := graph_concentration.{u} hθlo hθhi hT
  exact ⟨N₀,fun N hN p hlo hhi V _ m d hc hd ht hm hw U =>
    h N hN p ⟨hlo,hhi⟩ V m d ⟨hc,hd,ht,hm,hw⟩ U⟩

/-- Both original bipartite deviations use p*N, with the exact rectangle center
and the same coefficient-one strict tail conclusion. -/
theorem original_bipartite {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-θ) →
      ∀ (L : Type u) (R : Type v) [Fintype L] [Fintype R]
      (ell m : ℕ) (a : L → ℕ) (b : R → ℕ),
      Fintype.card L = ell → Fintype.card R = N → (N:ℝ)/T ≤ ell → (ell:ℝ) ≤ T*N →
      (∀ i, a i ≤ N) → (∀ j, b j ≤ ell) → (∑ i, a i) = m → (∑ j, b j) = m →
      |(m:ℝ)-p*ell*N| ≤ T*(N:ℝ)^2*p/Real.sqrt (p*N) →
      (∀ i, |(a i:ℝ)-p*N| ≤ (p*N)^((4:ℝ)/7)) →
      (∀ j, |(b j:ℝ)-p*ell| ≤ (p*N)^((4:ℝ)/7)) →
      ∀ (U : Finset L) (W : Finset R),
      (bipartiteFixedDegreeLaw a b).real {E | (N:ℝ)^2*p*Real.sqrt ((p*N)^((1:ℝ)/7)/N)*Real.log N ≤
        |(rectangleCount U W E:ℝ)-(∑ i ∈ U, (a i:ℝ))*(∑ j ∈ W, (b j:ℝ))/m|} < 1/Real.log N := by
  obtain ⟨N₀,h⟩ := bipartite_concentration.{u,v} hθlo hθhi hT
  exact ⟨N₀,fun N hN p hlo hhi L R _ _ ell m a b hL hR hel heu ha hb hta htb hm hwa hwb U W =>
    h N hN p ⟨hlo,hhi⟩ L R ell m a b ⟨hL,hR,hel,heu,ha,hb,hta,htb,hm,hwa,hwb⟩ U W⟩

/-- Expanded manuscript statement with signed totals and literal tail threshold. -/
theorem paper_graph {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-θ) →
      ∀ (V : Type u) [Fintype V] (m : ℤ) (d : V → ℕ),
        Fintype.card V = N → (∀ v, d v ≤ N-1) →
        (∑ v, (d v:ℤ) = 2*m) →
        |(m:ℝ)-p*N*(N-1)/2| ≤ T*N^2*p/Real.sqrt (p*N) →
        (∀ v, |(d v:ℝ)-p*N| ≤ (p*N)^((4:ℝ)/7)) →
        0 < m ∧ ∀ U : Finset V,
          (N:ℝ)/T ≤ U.card → (N:ℝ)/T ≤ N-(U.card:ℝ) →
          (fixedDegreeLaw d).real {G | (N:ℝ)^2*p*Real.sqrt ((p*N)^((1:ℝ)/7)/N)*Real.log N ≤
            |(internalCount U G:ℝ)-(∑ v ∈ U, (d v:ℝ))^2/(4*(m:ℝ))|} < 1/Real.log N ∧
          (fixedDegreeLaw d).real {G | (N:ℝ)^2*p*Real.sqrt ((p*N)^((1:ℝ)/7)/N)*Real.log N ≤
            |(cutCount U G:ℝ)-(∑ v ∈ U, (d v:ℝ))*
              (∑ v ∈ Finset.univ \ U, (d v:ℝ))/(2*(m:ℝ))|} < 1/Real.log N := by
  exact signed_graph_concentration.{u} hθlo hθhi hT

/-- Expanded manuscript statement with signed totals and literal tail threshold. -/
theorem paper_graph_fin {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-θ) →
      ∀ (m : ℤ) (d : Fin N → ℕ),
        (∀ v, d v ≤ N-1) → (∑ v, (d v:ℤ) = 2*m) →
        |(m:ℝ)-p*N*(N-1)/2| ≤ T*N^2*p/Real.sqrt (p*N) →
        (∀ v, |(d v:ℝ)-p*N| ≤ (p*N)^((4:ℝ)/7)) →
        0 < m ∧ ∀ U : Finset (Fin N),
          (N:ℝ)/T ≤ U.card → (N:ℝ)/T ≤ N-(U.card:ℝ) →
          (fixedDegreeLaw d).real {G | (N:ℝ)^2*p*Real.sqrt ((p*N)^((1:ℝ)/7)/N)*Real.log N ≤
            |(internalCount U G:ℝ)-(∑ v ∈ U, (d v:ℝ))^2/(4*(m:ℝ))|} < 1/Real.log N ∧
          (fixedDegreeLaw d).real {G | (N:ℝ)^2*p*Real.sqrt ((p*N)^((1:ℝ)/7)/N)*Real.log N ≤
            |(cutCount U G:ℝ)-(∑ v ∈ U, (d v:ℝ))*
              (∑ v ∈ Finset.univ \ U, (d v:ℝ))/(2*(m:ℝ))|} < 1/Real.log N := by
  exact signed_graph_concentration_fin hθlo hθhi hT

/-- Expanded manuscript statement with signed totals and literal tail threshold. -/
theorem paper_bipartite {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-θ) →
      ∀ (L : Type u) (R : Type v) [Fintype L] [Fintype R]
        (ell m : ℤ) (a : L → ℕ) (b : R → ℕ),
        (Fintype.card L:ℤ) = ell → Fintype.card R = N →
        (N:ℝ)/T ≤ (ell:ℝ) → (ell:ℝ) ≤ T*N →
        (∀ i, a i ≤ N) → (∀ j, (b j:ℤ) ≤ ell) →
        (∑ i, (a i:ℤ) = m) → (∑ j, (b j:ℤ) = m) →
        |(m:ℝ)-p*(ell:ℝ)*N| ≤ T*N^2*p/Real.sqrt (p*N) →
        (∀ i, |(a i:ℝ)-p*N| ≤ (p*N)^((4:ℝ)/7)) →
        (∀ j, |(b j:ℝ)-p*(ell:ℝ)| ≤ (p*N)^((4:ℝ)/7)) →
        0 < ell ∧ 0 < m ∧ ∀ (U : Finset L) (W : Finset R),
          (N:ℝ)/T ≤ U.card → (N:ℝ)/T ≤ (ell:ℝ)-(U.card:ℝ) →
          (N:ℝ)/T ≤ W.card → (N:ℝ)/T ≤ N-(W.card:ℝ) →
          (bipartiteFixedDegreeLaw a b).real {E | (N:ℝ)^2*p*Real.sqrt ((p*N)^((1:ℝ)/7)/N)*Real.log N ≤
            |(rectangleCount U W E:ℝ)-(∑ i ∈ U, (a i:ℝ))*
              (∑ j ∈ W, (b j:ℝ))/(m:ℝ)|} < 1/Real.log N := by
  exact signed_bipartite_concentration.{u,v} hθlo hθhi hT

/-- Expanded manuscript statement with signed totals and literal tail threshold. -/
theorem paper_bipartite_fin {θ T : ℝ}
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-θ) →
      ∀ (ell m : ℤ) (a : Fin ell.toNat → ℕ) (b : Fin N → ℕ),
        (N:ℝ)/T ≤ (ell:ℝ) → (ell:ℝ) ≤ T*N →
        (∀ i, a i ≤ N) → (∀ j, (b j:ℤ) ≤ ell) →
        (∑ i, (a i:ℤ) = m) → (∑ j, (b j:ℤ) = m) →
        |(m:ℝ)-p*(ell:ℝ)*N| ≤ T*N^2*p/Real.sqrt (p*N) →
        (∀ i, |(a i:ℝ)-p*N| ≤ (p*N)^((4:ℝ)/7)) →
        (∀ j, |(b j:ℝ)-p*(ell:ℝ)| ≤ (p*N)^((4:ℝ)/7)) →
        0 < ell ∧ 0 < m ∧ ∀ (U : Finset (Fin ell.toNat)) (W : Finset (Fin N)),
          (N:ℝ)/T ≤ U.card → (N:ℝ)/T ≤ (ell:ℝ)-(U.card:ℝ) →
          (N:ℝ)/T ≤ W.card → (N:ℝ)/T ≤ N-(W.card:ℝ) →
          (bipartiteFixedDegreeLaw a b).real {E | (N:ℝ)^2*p*Real.sqrt ((p*N)^((1:ℝ)/7)/N)*Real.log N ≤
            |(rectangleCount U W E:ℝ)-(∑ i ∈ U, (a i:ℝ))*
              (∑ j ∈ W, (b j:ℝ))/(m:ℝ)|} < 1/Real.log N := by
  exact signed_bipartite_concentration_fin hθlo hθhi hT

end MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Checks

/-- info: 'MajorityDynamics.Literature.EdgeProbabilities.graph_edge_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Literature.EdgeProbabilities.graph_edge_probability
/-- info: 'MajorityDynamics.Literature.EdgeProbabilities.bipartite_edge_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Literature.EdgeProbabilities.bipartite_edge_probability
/-- info: 'MajorityDynamics.Literature.EdgeProbabilities.graph_window_source_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Literature.EdgeProbabilities.graph_window_source_error
/-- info: 'MajorityDynamics.Literature.EdgeProbabilities.bipartite_window_source_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Literature.EdgeProbabilities.bipartite_window_source_error
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.graph_window_relative_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.graph_window_relative_error
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_window_relative_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_window_relative_error
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Checks.graph_window_marginal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Checks.graph_window_marginal
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Checks.bipartite_window_marginal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Checks.bipartite_window_marginal
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Checks.graph_source_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Checks.graph_source_formula
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Checks.bipartite_source_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Checks.bipartite_source_formula
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Numerics.graph_error_absolute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Numerics.graph_error_absolute
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Numerics.graph_weight_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Numerics.graph_weight_lower
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Numerics.graph_error_relative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Numerics.graph_error_relative
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Numerics.graph_correction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Numerics.graph_correction
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Numerics.bipartite_correction_simple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Numerics.bipartite_correction_simple
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Numerics.bipartite_error_reciprocal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Numerics.bipartite_error_reciprocal
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Numerics.eventually_relativeData' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Numerics.eventually_relativeData
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Numerics.graph_approximation_relative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Numerics.graph_approximation_relative
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Numerics.bipartite_bracket_relative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Numerics.bipartite_bracket_relative
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.graph_fiber_edge_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.graph_fiber_edge_probability
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.graph_neighborhood_edge_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.graph_neighborhood_edge_probability
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.graph_pair_upper_distinct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.graph_pair_upper_distinct
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_left_fiber_edge_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_left_fiber_edge_probability
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_right_fiber_edge_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_right_fiber_edge_probability
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_joint_le_of_left_residual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_joint_le_of_left_residual
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_joint_le_of_right_residual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_joint_le_of_right_residual
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.graph_residual_window' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.graph_residual_window
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_left_residual_window' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_left_residual_window
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_right_residual_window' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_right_residual_window
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.graph_joint_of_marginals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.graph_joint_of_marginals
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_joint_of_marginals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_joint_of_marginals
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.GraphInput.realized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.GraphInput.realized
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.BipartiteInput.realized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.BipartiteInput.realized
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.GraphInput.normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.GraphInput.normalized
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.BipartiteInput.normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.BipartiteInput.normalized
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.internal_weight_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.internal_weight_sum
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.internalCount_eq_filter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.internalCount_eq_filter
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.rectangle_weight_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.rectangle_weight_sum
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.internal_tail_of_edge_estimates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.internal_tail_of_edge_estimates
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.cut_tail_of_edge_estimates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.cut_tail_of_edge_estimates
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.rectangle_tail_of_edge_estimates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.rectangle_tail_of_edge_estimates
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.uniform_graph_edges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.uniform_graph_edges
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.uniform_bipartite_edges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.uniform_bipartite_edges
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.graph_concentration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.graph_concentration
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_concentration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartite_concentration
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.c1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.c1
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Checks.original_graph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Checks.original_graph
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Checks.original_bipartite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Checks.original_bipartite
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.graphInput_of_signed_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.graphInput_of_signed_total
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartiteInput_of_signed_totals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.bipartiteInput_of_signed_totals

/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.signed_graph_concentration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.signed_graph_concentration
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Checks.paper_graph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Checks.paper_graph

/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.signed_graph_concentration_fin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.signed_graph_concentration_fin
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Checks.paper_graph_fin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Checks.paper_graph_fin

/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.signed_bipartite_concentration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.signed_bipartite_concentration
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Checks.paper_bipartite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Checks.paper_bipartite

/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.signed_bipartite_concentration_fin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.signed_bipartite_concentration_fin
/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Checks.paper_bipartite_fin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.Checks.paper_bipartite_fin

/-- info: 'MajorityDynamics.Literature.EdgeProbabilities.graph_sequence_growth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Literature.EdgeProbabilities.graph_sequence_growth

/-- info: 'MajorityDynamics.Literature.EdgeProbabilities.bipartite_sequence_growth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Literature.EdgeProbabilities.bipartite_sequence_growth

/-- info: 'MajorityDynamics.Literature.EdgeProbabilities.window_degree_isTheta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Literature.EdgeProbabilities.window_degree_isTheta

/-- info: 'MajorityDynamics.Literature.EdgeProbabilities.graph_uniform_source_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Literature.EdgeProbabilities.graph_uniform_source_error

/-- info: 'MajorityDynamics.Literature.EdgeProbabilities.bipartite_uniform_source_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Literature.EdgeProbabilities.bipartite_uniform_source_error

/-- info: 'MajorityDynamics.Probability.FixedDegreeEdgeConcentration.measure_indicator_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MajorityDynamics.Probability.FixedDegreeEdgeConcentration.measure_indicator_tail
