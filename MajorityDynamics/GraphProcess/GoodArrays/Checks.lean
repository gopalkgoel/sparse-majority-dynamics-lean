import MajorityDynamics.GraphProcess.GoodArrays.Main

noncomputable section
open scoped BigOperators Classical
namespace MajorityDynamics.GraphProcess.GoodArrays.Checks
open Universal
universe u

example {V : Type*} [Fintype V] {n : ℕ} (y : Local.CoarseData V n) (T p : ℝ)
    (d : RowArray.Ambient y.part) : d ∈ E0 y T p ↔
      RowArray.totals d = y.edge ∧
      ∀ s t v, v ∈ History.block y.part s →
        |(RowArray.values d v t : ℝ)-(y.edge s t : ℝ)/(y.sizes s : ℝ)| ≤
        Real.sqrt (p*Fintype.card V)/(100*T*((2^(n+1) : ℕ) : ℝ)) := mem_E0 y T p d

example (a : ℕ) (ha : 0 < a) (m : ℤ) : ∑ i, balanced a m i = m := balanced_sum a ha m

example (a : ℕ) (ha : 0 < a) (m : ℤ) (i : Fin a) :
    |(balanced a m i : ℝ)-(m : ℝ)/a| ≤ 1 := balanced_deviation a ha m i

example {θ T : ℝ} (n : ℕ) (hlo : 1/2 < θ) (hhi : θ < 1) (hT : 1 < T) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ y : Local.CoarseData V n,
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
      Real.exp (-C*N)*(p*N)^((((2^(n+1)*N : ℕ) : ℝ))/2) ≤ ((E0 y T p).card : ℝ) :=
  uniform_cardinality n hlo hhi hT

example {θ T : ℝ} (n : ℕ) (hlo : 1/2 < θ) (hhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ y : Local.CoarseData V n,
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
      (∀ s (r : Fin n),
        decision (bits (n+1) s r.castSucc) (bits (n+1) s r.succ)
          ((∑ t, character r.castSucc t * (y.edge s t : ℝ)) -
            sign (bits (n+1) s r.succ) *
              (T⁻¹ * ((Fintype.card V : ℝ)^2*p/Real.sqrt (p*Fintype.card V))))) →
      ∀ d ∈ E0 y T p, RowArray.totals d = y.edge ∧ d ∈ RowArray.history y.part ∧
        RowArray.Regular p d ∧ RowArray.Gamma y.part y.edge 1 p d ∧
        (∀ C : ℝ, 1 ≤ C → RowArray.Gamma y.part y.edge C p d) ∧
        ∃ G : SimpleGraph V, History.degreeArray y.part G = RowArray.values d :=
  uniform_inclusion_graphical n hlo hhi hT

example {θ T : ℝ} (n : ℕ) (hlo : 1/2 < θ) (hhi : θ < 1) (hT : 1 < T) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (V : Type u) [Fintype V], Fintype.card V = N →
      ∀ p : ℝ, T⁻¹*(N : ℝ)^(-θ) < p → p < T*(N : ℝ)^(-θ) →
      ∀ y : Local.CoarseData V n,
      (∀ s, (N : ℝ)/T ≤ (y.sizes s : ℝ)) →
      (∀ s t, |(y.edge s t : ℝ)-p*(y.sizes s : ℝ)*(y.sizes t : ℝ)| ≤
        T*(N : ℝ)^2*p/Real.sqrt (p*N)) →
      (E0 y T p).Nonempty ∧ (Separated y T p → ∀ q : Local.Tilt n,
        0 < RowArray.law y.part q
          (RowArray.history y.part ∩ RowArray.exactTotals y.part y.edge)) :=
  uniform_nonempty_and_positive n hlo hhi hT

end MajorityDynamics.GraphProcess.GoodArrays.Checks

/-- info: 'MajorityDynamics.GraphProcess.GoodArrays.mem_E0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrays.mem_E0

/-- info: 'MajorityDynamics.GraphProcess.GoodArrays.balanced_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrays.balanced_sum

/-- info: 'MajorityDynamics.GraphProcess.GoodArrays.balanced_deviation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrays.balanced_deviation

/-- info: 'MajorityDynamics.GraphProcess.GoodArrays.balancedBlock_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrays.balancedBlock_sum

/-- info: 'MajorityDynamics.GraphProcess.GoodArrays.balancedBlock_deviation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrays.balancedBlock_deviation

/-- info: 'MajorityDynamics.GraphProcess.GoodArrays.shifted_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrays.shifted_bounds

/-- info: 'MajorityDynamics.GraphProcess.GoodArrays.shiftedArray_totals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrays.shiftedArray_totals

/-- info: 'MajorityDynamics.GraphProcess.GoodArrays.shiftedArray_mem_E0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrays.shiftedArray_mem_E0

/-- info: 'MajorityDynamics.GraphProcess.GoodArrays.shiftedArray_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrays.shiftedArray_injective

/-- info: 'MajorityDynamics.GraphProcess.GoodArrays.product_card_le_E0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrays.product_card_le_E0

/-- info: 'MajorityDynamics.GraphProcess.GoodArrays.ordered_size_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrays.ordered_size_sum

/-- info: 'MajorityDynamics.GraphProcess.GoodArrays.uniform_regime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrays.uniform_regime

/-- info: 'MajorityDynamics.GraphProcess.GoodArrays.card_E0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrays.card_E0

/-- info: 'MajorityDynamics.GraphProcess.GoodArrays.uniform_cardinality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrays.uniform_cardinality

/-- info: 'MajorityDynamics.GraphProcess.GoodArrays.separated_of_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrays.separated_of_admissible

/-- info: 'MajorityDynamics.GraphProcess.GoodArrays.e0_history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrays.e0_history

/-- info: 'MajorityDynamics.GraphProcess.GoodArrays.e0_regular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrays.e0_regular

/-- info: 'MajorityDynamics.GraphProcess.GoodArrays.e0_gamma_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrays.e0_gamma_one

/-- info: 'MajorityDynamics.GraphProcess.GoodArrays.e0_gamma_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrays.e0_gamma_mono

/-- info: 'MajorityDynamics.GraphProcess.GoodArrays.uniform_inclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrays.uniform_inclusion

/-- info: 'MajorityDynamics.GraphProcess.GoodArrays.E0_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrays.E0_nonempty

/-- info: 'MajorityDynamics.GraphProcess.GoodArrays.row_history_totals_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrays.row_history_totals_pos

/-- info: 'MajorityDynamics.GraphProcess.GoodArrays.uniform_nonempty_and_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrays.uniform_nonempty_and_positive

/-- info: 'MajorityDynamics.GraphProcess.GoodArrays.uniform_inclusion_graphical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.GraphProcess.GoodArrays.uniform_inclusion_graphical
