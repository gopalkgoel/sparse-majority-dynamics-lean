import MajorityDynamics.GraphProcess.GoodArrayProbability.Main

noncomputable section
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory
namespace MajorityDynamics.GraphProcess.GoodArrayProbability.Checks
open Universal
universe u

example (m k : ℕ) (q : Binomial.Probability) :
    Binomial.Approximation.pointMass m k q =
      (ProbabilityTheory.binomial m (Binomial.closedProbability q) {k}).toReal := rfl

example (A : ℝ) (hA : 0 ≤ A) :
    ∃ c : ℝ, 0 < c ∧ ∃ L : ℝ, 1 ≤ L ∧
      ∀ (m : ℕ) (q : Binomial.Probability) (k : ℕ),
      (q : ℝ) ≤ 1/2 → L ≤ (m : ℝ)*(q : ℝ) →
      |(k : ℝ)-(m : ℝ)*(q : ℝ)| ≤ A*Real.sqrt ((m : ℝ)*(q : ℝ)) →
      c / Real.sqrt ((m : ℝ)*(q : ℝ)) ≤
        (ProbabilityTheory.binomial m (Binomial.closedProbability q) {k}).toReal :=
  central_binomial_lower A hA

example {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
      (∀ s t, |(q s t : ℝ)-p| ≤ T*p/Real.sqrt (p*N)) →
      ∀ d : RowArray.Ambient y.part, d ∈ GoodArrays.E0 y T p → ∀ v t,
        c/Real.sqrt (p*N) ≤ Binomial.Approximation.pointMass
          (Local.trials y.sizes (y.part v) t) (RowArray.naturalRows d v t)
          (q (y.part v) t) :=
  uniform_coordinate_lower n hθlo hθhi hT

example {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
      (∀ s t, |(q s t : ℝ)-p| ≤ T*p/Real.sqrt (p*N)) →
      ∀ d : RowArray.Ambient y.part, d ∈ GoodArrays.E0 y T p →
        Real.exp (-C*N)*(p*N)^(-(((2^(n+1)*N : ℕ) : ℝ)/2)) ≤
          (RowArray.law y.part q).real {d} ∧
        Real.exp (-C*N)*(p*N)^(-(((2^(n+1)*N : ℕ) : ℝ)/2)) ≤
          (cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge)).real {d} :=
  uniform_point n hθlo hθhi hT

example {θ T : ℝ} (n : ℕ)
    (hθlo : 1/2 < θ) (hθhi : θ < 1) (hT : 1 < T) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ (y : Local.CoarseData V n) (q : Local.Tilt n),
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
      (∀ s t, |(q s t : ℝ)-p| ≤ T*p/Real.sqrt (p*N)) →
      Real.exp (-C*N) ≤ (RowArray.law y.part q).real (GoodArrays.E0 y T p) ∧
      Real.exp (-C*N) ≤
        (cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge)).real
          (GoodArrays.E0 y T p) ∧
      (GoodArrays.Separated y T p →
        Real.exp (-C*N) ≤ (RowArray.law y.part q).real
          (RowArray.history y.part ∩ RowArray.exactTotals y.part y.edge ∩
            {d | RowArray.Regular p d} ∩ {d | RowArray.Gamma y.part y.edge 1 p d})) :=
  uniform_probability n hθlo hθhi hT

example {V : Type*} [Fintype V] {n : ℕ} (y : Local.CoarseData V n)
    (q : Local.Tilt n) (d : RowArray.Ambient y.part) :
    (RowArray.law y.part q {d}).toReal =
      ∏ v, ∏ t, (ProbabilityTheory.binomial
        (Local.trials y.sizes (y.part v) t)
        (Binomial.closedProbability (q (y.part v) t))
        {RowArray.naturalRows d v t}).toReal := row_atom_product y q d

example {V : Type*} [Fintype V] {n : ℕ} (y : Local.CoarseData V n)
    (q : Local.Tilt n) (d : RowArray.Ambient y.part) (hd : RowArray.totals d = y.edge) :
    (RowArray.law y.part q {d}).toReal ≤
      (cond (RowArray.law y.part q) (RowArray.exactTotals y.part y.edge) {d}).toReal :=
  row_atom_le_conditioned y q d hd

example {a b x : ℝ} (hx : 0 < x) (N m : ℕ) :
    (Real.exp (-a*N)*x^((m:ℝ)/2)) *
      (Real.exp (-b*N)*x^(-((m:ℝ)/2))) = Real.exp (-(a+b)*N) :=
  count_point_cancellation hx N m

end MajorityDynamics.GraphProcess.GoodArrayProbability.Checks

/-- info: 'MajorityDynamics.GraphProcess.GoodArrayProbability.central_log_comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrayProbability.central_log_comparison

/-- info: 'MajorityDynamics.GraphProcess.GoodArrayProbability.central_window_interior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrayProbability.central_window_interior

/-- info: 'MajorityDynamics.GraphProcess.GoodArrayProbability.central_binomial_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrayProbability.central_binomial_lower

/-- info: 'MajorityDynamics.GraphProcess.GoodArrayProbability.coordinateConstant_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrayProbability.coordinateConstant_pos

/-- info: 'MajorityDynamics.GraphProcess.GoodArrayProbability.finite_coordinate_regime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrayProbability.finite_coordinate_regime

/-- info: 'MajorityDynamics.GraphProcess.GoodArrayProbability.uniform_coordinate_regime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrayProbability.uniform_coordinate_regime

/-- info: 'MajorityDynamics.GraphProcess.GoodArrayProbability.row_atom_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrayProbability.row_atom_product

/-- info: 'MajorityDynamics.GraphProcess.GoodArrayProbability.real_le_cond_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrayProbability.real_le_cond_real

/-- info: 'MajorityDynamics.GraphProcess.GoodArrayProbability.row_atom_le_conditioned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrayProbability.row_atom_le_conditioned

/-- info: 'MajorityDynamics.GraphProcess.GoodArrayProbability.E0_le_conditioned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrayProbability.E0_le_conditioned

/-- info: 'MajorityDynamics.GraphProcess.GoodArrayProbability.row_atom_of_coordinate_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrayProbability.row_atom_of_coordinate_bound

/-- info: 'MajorityDynamics.GraphProcess.GoodArrayProbability.coordinate_power_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrayProbability.coordinate_power_bound

/-- info: 'MajorityDynamics.GraphProcess.GoodArrayProbability.card_mul_point_le_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrayProbability.card_mul_point_le_event

/-- info: 'MajorityDynamics.GraphProcess.GoodArrayProbability.count_point_cancellation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrayProbability.count_point_cancellation

/-- info: 'MajorityDynamics.GraphProcess.GoodArrayProbability.uniform_coordinate_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrayProbability.uniform_coordinate_lower

/-- info: 'MajorityDynamics.GraphProcess.GoodArrayProbability.uniform_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrayProbability.uniform_point

/-- info: 'MajorityDynamics.GraphProcess.GoodArrayProbability.uniform_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrayProbability.uniform_probability

