import MajorityDynamics.Probability.HypergeometricTiltTail.Applications
import MajorityDynamics.Probability.HypergeometricTiltTail.MeanLaw
import MajorityDynamics.Probability.HypergeometricTiltTail.HypergeomLaw

noncomputable section
open scoped BigOperators
namespace MajorityDynamics.Probability.HypergeometricTiltTail.Checks
open FixedSizeExponential

/-- Original assumptions and quantifier order with the actual factor expanded. -/
theorem original_factor {θ T B : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hB : 0 ≤ B) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-θ) →
      ∀ (V : Type*) [DecidableEq V] (P S : Finset V), S ⊆ P →
      (P.card = N ∨ P.card = N-1) → ∀ h : ℕ,
      (N:ℝ)/T ≤ h → (h:ℝ) ≤ N-(N:ℝ)/T → |(S.card:ℝ)-(h:ℝ)| ≤ 1 →
      ∀ L : ℝ, (N:ℝ)/T ≤ L → L ≤ T*N →
      ∀ β : V → ℝ, (∀ v ∈ P, |β v| ≤ Real.log (N:ℝ)) →
      ∀ d t : ℤ, |(d:ℝ)-p*N| ≤ Real.sqrt (p*N)*Real.log (N:ℝ) →
      0 ≤ t → t ≤ d →
      (Real.log (N:ℝ))^100 ≤ |((t:ℝ)-p*h)/Real.sqrt (p*h)| →
      Real.exp (B*(Real.log (N:ℝ))^4) * (((S.card.choose t.toNat : ℝ) *
          ((P.card-S.card).choose (d-t).toNat : ℝ) / (P.card.choose d.toNat : ℝ)) *
          subsetAverage S t.toNat (fun R => subsetAverage (P \ S) (d-t).toNat
            (fun Q => Real.exp ((∑ v ∈ R ∪ Q, β v) / Real.sqrt (p*L) -
              (∑ v ∈ P \ (R ∪ Q), β v) * Real.sqrt (p*L) / L)))) ≤
        Real.exp (-c*(((t:ℝ)-p*h)/Real.sqrt (p*h))^2) := by
  obtain ⟨c,hc,N₀,h⟩ := uniform_factor hθlo hθhi hT hB
  refine ⟨c,hc,N₀,?_⟩
  intro N hN p hlo hhi V inst P S hSP hM hsize hhlo hhhi hHh L hLlo hLhi β hβ d t hd ht htd hτ
  have hnat : d.toNat-t.toNat = (d-t).toNat := by omega
  simpa only [weightedFactor, hypergeomMass, tiltExpectation, tiltWeight, hnat] using
    h N hN p hlo hhi V P S hSP hM hsize hhlo hhhi hHh L hLlo hLhi β hβ d t hd ht htd hτ

/-- Literal application, including exact choices and normalization. -/
theorem original_graph {θ T B : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hB : 0 ≤ B) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-θ) →
      ∀ (V : Type*) [Fintype V] [DecidableEq V], Fintype.card V = N →
      ∀ (v : V) (S : Finset V),
      (N:ℝ)/T ≤ S.card → (S.card:ℝ) ≤ N-(N:ℝ)/T →
      ∀ β : V → ℝ, (∀ w, |β w| ≤ Real.log (N:ℝ)) →
      ∀ d t : ℤ, |(d:ℝ)-p*N| ≤ Real.sqrt (p*N)*Real.log (N:ℝ) →
      0 ≤ t → t ≤ d →
      (Real.log (N:ℝ))^100 ≤ |((t:ℝ)-p*S.card)/Real.sqrt (p*S.card)| →
      Real.exp (B*(Real.log (N:ℝ))^4) * ((((S.card-if v ∈ S then 1 else 0).choose t.toNat : ℝ) *
          ((N-S.card-if v ∉ S then 1 else 0).choose (d-t).toNat : ℝ) /
          ((N-1).choose d.toNat : ℝ)) *
          subsetAverage (S.erase v) t.toNat (fun R =>
            subsetAverage (Finset.univ \ insert v S) (d-t).toNat (fun Q =>
              Real.exp ((∑ x ∈ R ∪ Q, β x) / Real.sqrt (p*N) -
                (∑ x ∈ Finset.univ \ insert v (R ∪ Q), β x) * Real.sqrt (p*N) / N)))) ≤
        Real.exp (-c*(((t:ℝ)-p*S.card)/Real.sqrt (p*S.card))^2) := by
  obtain ⟨c,hc,N₀,h⟩ := uniform_graph_factor hθlo hθhi hT hB
  refine ⟨c,hc,N₀,?_⟩
  intro N hN p hlo hhi V inst inst' hcard v S hSlo hShi β hβ d t hd ht htd hτ
  have hf := h N hN p hlo hhi V hcard v S hSlo hShi β hβ d t hd ht htd hτ
  simpa only [graphFactor_eq v S ht htd p β, hcard] using hf

/-- Literal application, including exact choices and normalization. -/
theorem original_bipartite {θ T B : ℝ} (hθlo : 1/2 < θ) (hθhi : θ < 1)
    (hT : 1 < T) (hB : 0 ≤ B) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p : ℝ,
      T⁻¹*(N:ℝ)^(-θ) < p → p < T*(N:ℝ)^(-θ) →
      ∀ (V : Type*) [Fintype V] [DecidableEq V], Fintype.card V = N →
      ∀ S : Finset V, (N:ℝ)/T ≤ S.card → (S.card:ℝ) ≤ N-(N:ℝ)/T →
      ∀ L : ℝ, (N:ℝ)/T ≤ L → L ≤ T*N →
      ∀ β : V → ℝ, (∀ w, |β w| ≤ Real.log (N:ℝ)) →
      ∀ d t : ℤ, |(d:ℝ)-p*N| ≤ Real.sqrt (p*N)*Real.log (N:ℝ) →
      0 ≤ t → t ≤ d →
      (Real.log (N:ℝ))^100 ≤ |((t:ℝ)-p*S.card)/Real.sqrt (p*S.card)| →
      Real.exp (B*(Real.log (N:ℝ))^4) * (((S.card.choose t.toNat : ℝ) *
          ((N-S.card).choose (d-t).toNat : ℝ) / (N.choose d.toNat : ℝ)) *
          subsetAverage S t.toNat (fun R =>
            subsetAverage (Finset.univ \ S) (d-t).toNat (fun Q =>
              Real.exp ((∑ x ∈ R ∪ Q, β x) / Real.sqrt (p*L) -
                (∑ x ∈ Finset.univ \ (R ∪ Q), β x) * Real.sqrt (p*L) / L)))) ≤
        Real.exp (-c*(((t:ℝ)-p*S.card)/Real.sqrt (p*S.card))^2) := by
  obtain ⟨c,hc,N₀,h⟩ := uniform_bipartite_factor hθlo hθhi hT hB
  refine ⟨c,hc,N₀,?_⟩
  intro N hN p hlo hhi V inst inst' hcard S hSlo hShi L hLlo hLhi β hβ d t hd ht htd hτ
  have hf := h N hN p hlo hhi V hcard S hSlo hShi L hLlo hLhi β hβ d t hd ht htd hτ
  simpa only [bipartiteFactor_eq S ht htd p L β, hcard] using hf

/-- Each expectation is the literal normalized finite sum, including empty families. -/
theorem actual_average {V : Type*} [DecidableEq V]
    (A : Finset V) (k : ℕ) (f : Finset V → ℝ) :
    subsetAverage A k f = (A.card.choose k : ℝ)⁻¹ * ∑ R ∈ A.powersetCard k, f R := rfl

/-- The hypergeometric term is the probability of the actual intersection count. -/
theorem actual_hypergeometric {V : Type*} [DecidableEq V]
    (P S : Finset V) (hSP : S ⊆ P) {d t : ℕ} (htd : t ≤ d) :
    (S.card.choose t : ℝ) * ((P.card-S.card).choose (d-t) : ℝ) /
      (P.card.choose d : ℝ) =
      (P.card.choose d : ℝ)⁻¹ * ∑ R ∈ P.powersetCard d,
        (if (R ∩ S).card = t then (1 : ℝ) else 0) :=
  hypergeomMass_eq_uniform_average_on P S hSP htd

/-- Every draw count below the population is covered, with no positive lower window. -/
theorem all_draw_sizes {V : Type*} [DecidableEq V]
    (A : Finset V) {k : ℕ} (hk : k < A.card) (a : V → ℝ)
    (ha : ∀ v ∈ A, |a v| ≤ 1) :
    (A.card.choose k : ℝ)⁻¹ * ∑ R ∈ A.powersetCard k,
        Real.exp (∑ v ∈ R, a v) ≤
      max 1 (Real.sqrt (k : ℝ)/centralAtomConstant) *
        Real.exp (((k : ℝ)/A.card)*(∑ v ∈ A, a v) +
          ((k : ℝ)/A.card)*(∑ v ∈ A, (a v)^2)) :=
  subset_average_mgf A hk a ha

/-- Exact inclusion mean, also for the empty set. -/
theorem exact_mean {V : Type*} [DecidableEq V]
    (A : Finset V) {k : ℕ} (hk : k ≤ A.card) (a : V → ℝ) :
    (A.card.choose k : ℝ)⁻¹ * ∑ R ∈ A.powersetCard k, (∑ v ∈ R, a v) =
      ((k : ℝ)/A.card)*(∑ v ∈ A, a v) := subset_average_mean A hk a

/-- The target t=0 leaves the other piece under its genuine fixed-size law. -/
theorem zero_target {V : Type*} [DecidableEq V]
    (P S : Finset V) (d : ℤ) (p L : ℝ) (β : V → ℝ) :
    tiltExpectation P S (0 : ℤ).toNat (d-0).toNat p L β =
      subsetAverage (P \ S) d.toNat (fun R =>
        Real.exp ((∑ v ∈ R, β v)/Real.sqrt (p*L) -
          (∑ v ∈ P \ R, β v)*Real.sqrt (p*L)/L)) := by
  simpa only [Int.toNat_zero, sub_zero, tiltWeight] using
    tiltExpectation_zero_left P S d.toNat p L β

/-- The endpoint t=d has a deterministic empty complement piece. -/
theorem full_target {V : Type*} [DecidableEq V]
    (P S : Finset V) (d : ℤ) (p L : ℝ) (β : V → ℝ) :
    tiltExpectation P S d.toNat (d-d).toNat p L β =
      subsetAverage S d.toNat (fun R =>
        Real.exp ((∑ v ∈ R, β v)/Real.sqrt (p*L) -
          (∑ v ∈ P \ R, β v)*Real.sqrt (p*L)/L)) := by
  simpa only [sub_self, Int.toNat_zero, tiltWeight] using
    tiltExpectation_zero_right P S d.toNat p L β

/-- Infeasible target choices vanish under the actual factor. -/
theorem infeasible_factor {V : Type*} [DecidableEq V]
    (P S : Finset V) (d t : ℤ) (p L : ℝ) (β : V → ℝ)
    (hbad : S.card < t.toNat ∨ (P \ S).card < (d-t).toNat) :
    weightedFactor P S d t p L β = 0 := by
  unfold weightedFactor
  rcases hbad with hbad | hbad
  · rw [tiltExpectation_empty_left P S hbad, mul_zero]
  · rw [tiltExpectation_empty_right P S _ hbad, mul_zero]

/-- The exact mean of the actual pair, with the weight expanded and zero draws allowed. -/
theorem actual_pair_mean {V : Type*} [DecidableEq V]
    {P S : Finset V} (hSP : S ⊆ P) {k l : ℕ}
    (hk : k ≤ S.card) (hl : l ≤ (P \ S).card)
    {p L : ℝ} (hp : 0 < p) (hL : 0 < L) (β : V → ℝ) :
    subsetAverage S k (fun R => subsetAverage (P \ S) l
      (fun Q => (∑ v ∈ R ∪ Q, β v)/Real.sqrt (p*L) -
        (∑ v ∈ P \ (R ∪ Q), β v)*Real.sqrt (p*L)/L)) =
      ((1+p)*k/S.card-p)*(∑ v ∈ S, β v)/Real.sqrt (p*L) +
        ((1+p)*l/(P \ S).card-p)*(∑ v ∈ P \ S, β v)/Real.sqrt (p*L) :=
  pair_tilt_actual_mean hSP hk hl hp hL β

end MajorityDynamics.Probability.HypergeometricTiltTail.Checks

/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.fixedSize_mgf_interior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.fixedSize_mgf_interior
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.fixedSize_mgf_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.fixedSize_mgf_zero
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.fixedSize_mgf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.fixedSize_mgf
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.subsetAverage_eq_expectation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.subsetAverage_eq_expectation
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.subset_average_mgf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.subset_average_mgf
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.subset_average_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.subset_average_mean
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.subsetAverage_empty_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.subsetAverage_empty_family
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.subsetAverage_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.subsetAverage_zero
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.tiltWeight_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.tiltWeight_linear
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.pair_mean_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.pair_mean_eq
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.tiltExpectation_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.tiltExpectation_product
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.tiltExpectation_mgf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.tiltExpectation_mgf
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.tiltExpectation_beta_mgf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.tiltExpectation_beta_mgf
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.mgfPrefactor_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.mgfPrefactor_le
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.hypergeomMass_mul_binomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.hypergeomMass_mul_binomial
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.hypergeomMass_eq_uniform_average_on' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.hypergeomMass_eq_uniform_average_on
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.intersection_fiber_card_on' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.intersection_fiber_card_on
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.Numerics.uniform_regime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.Numerics.uniform_regime
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.Numerics.deviation_conversion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.Numerics.deviation_conversion
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.Numerics.coefficient_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.Numerics.coefficient_bound
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.pair_tilt_mean_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.pair_tilt_mean_bound
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.tiltExpectation_regime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.tiltExpectation_regime
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.polynomial_prefactor_absorb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.polynomial_prefactor_absorb
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.Numerics.eventually_exp_absorb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.Numerics.eventually_exp_absorb
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.graphFactor_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.graphFactor_eq
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.bipartiteFactor_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.bipartiteFactor_eq
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.Checks.actual_average' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.Checks.actual_average
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.Checks.actual_hypergeometric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.Checks.actual_hypergeometric
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.Checks.all_draw_sizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.Checks.all_draw_sizes
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.Checks.exact_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.Checks.exact_mean
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.Checks.zero_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.Checks.zero_target
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.Checks.full_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.Checks.full_target
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.Checks.infeasible_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.Checks.infeasible_factor
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.binomial_atom_chernoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.binomial_atom_chernoff
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.hypergeomMass_chernoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.hypergeomMass_chernoff
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.hypergeomMass_regime_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.hypergeomMass_regime_tail
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.factor_regime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.factor_regime
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.uniform_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.uniform_factor
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.uniform_graph_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.uniform_graph_factor
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.uniform_bipartite_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.uniform_bipartite_factor
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.Checks.original_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.Checks.original_factor
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.Checks.original_graph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.Checks.original_graph
/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.Checks.original_bipartite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.Checks.original_bipartite

/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.pair_tilt_actual_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.pair_tilt_actual_mean

/-- info: 'MajorityDynamics.Probability.HypergeometricTiltTail.Checks.actual_pair_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Probability.HypergeometricTiltTail.Checks.actual_pair_mean
