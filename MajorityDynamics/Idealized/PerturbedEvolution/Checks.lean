import MajorityDynamics.Idealized.PerturbedEvolution.Applications

/-! Independent expanded statement, actual conditional laws, and exact axiom guards. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace MajorityDynamics.Idealized.PerturbedEvolution
open Universal LinearResponse PerturbedTilt

example : PerturbedEvolutionTheorem := perturbed_evolution
example : PerturbedEvolutionTheorem := perturbed_evolution_finite

/-- Independent expansion of F1/F2 and every LA and template conclusion, with
one common triple of comparison constants before all varying inputs. -/
example :
    ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∀ n : ℕ, (n : ℝ) + 1 < 1 / (1 - θ) →
    ∀ T δ : ℝ, 1 < T → 0 < δ →
    ∃ K : ℝ, T ≤ K ∧ ∃ d : ℝ, 0 < d ∧ ∃ φ : ℝ, 0 < φ ∧ φ < 1 / 2 ∧
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧
    ∀ N ≥ N₀, ∀ p : ℝ, T⁻¹ * (N : ℝ) ^ (-θ) < p → p < T * (N : ℝ) ^ (-θ) →
    ∃ hp : 0 < p ∧ p < 1,
      Process.Specification N ⟨p, hp⟩ (responseHorizon θ) (processExponent θ T)
        (referenceDataReal θ T N p) ∧
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ (V : Type) [Fintype V], Fintype.card V = N → ∀ y : Local.CoarseData V n,
      y.reg = true →
      (∀ s, |(y.sizes s : ℝ) - (((referenceDataReal θ T N p).state n).sizes s : ℝ) -
        τ * (Real.sqrt (N : ℝ) * Real.sqrt (p * N) ^ n) * ε n s| ≤
          T * (Real.sqrt (N : ℝ) * Real.sqrt (p * N) ^ n) * (N : ℝ) ^ (-δ)) →
      (∀ s t, |(y.edge s t : ℝ) - ((referenceDataReal θ T N p).state n).edges s t *
        (1 + τ * (Real.sqrt (p * N) ^ n / Real.sqrt (N : ℝ)) *
          (ε n s / ν n s + ε n t / ν n t))| ≤
        T * (Real.sqrt (p * N) ^ n / Real.sqrt (N : ℝ)) * (N : ℝ) ^ (-δ) * (N : ℝ)^2 * p) →
      let a := referenceDataReal θ T N p
      ∃ q : Local.Tilt n,
        y.reg = true ∧
        (∀ s, K⁻¹ * (N : ℝ) ≤ (y.sizes s : ℝ)) ∧
        (∀ r : Fin n, |∑ t, character r.castSucc t * (y.sizes t : ℝ)| ≤
          K * N / Real.sqrt (p * N)) ∧
        (∀ s t, |(y.edge s t : ℝ) - p * (y.sizes s : ℝ) * (y.sizes t : ℝ)| ≤
          K * ((N : ℝ)^2 * p / Real.sqrt (p * N))) ∧
        (∀ s t, 0 < (y.edge s t : ℝ)) ∧
        (∀ s (r : Fin n), decision (bits (n + 1) s r.castSucc) (bits (n + 1) s r.succ)
          ((∑ t, character r.castSucc t * (y.edge s t : ℝ)) -
            sign (bits (n + 1) s r.succ) * (K⁻¹ * ((N : ℝ)^2 * p / Real.sqrt (p * N))))) ∧
        (∀ s t, |(q s t : ℝ) - p| ≤ K * p / Real.sqrt (p * N)) ∧
        (∀ s, φ ≤ (Local.rowLaw y.sizes q s).real (Binomial.event (Local.historySupport y.sizes s))) ∧
        (∀ s t, (y.sizes s : ℝ) * (∫ z, (z t : ℝ) ∂Local.rowCondition y.sizes q s) = (y.edge s t : ℝ)) ∧
        (∀ q' : Local.Tilt n, (∀ s t, (y.sizes s : ℝ) *
          (∫ z, (z t : ℝ) ∂Local.rowCondition y.sizes q' s) = (y.edge s t : ℝ)) → q' = q) ∧
        (∀ s b, φ ≤ (Local.rowCondition y.sizes q s).real (Binomial.event (Local.childSupport y.sizes s b)) ∧
          (Local.rowCondition y.sizes q s).real (Binomial.event (Local.childSupport y.sizes s b)) ≤ 1 - φ) ∧
        (∀ s t, 0 < (y.sizes t : ℝ) - (if s = t then 1 else 0) - p * ((a.state n).sizes t : ℝ)) ∧
        (∀ s t, 0 < ((a.state n).sizes t : ℝ) - (if s = t then 1 else 0) - p * ((a.state n).sizes t : ℝ)) ∧
        (∀ s t, 0 < (1 - (q s t : ℝ)) * p * ((a.state n).sizes t : ℝ)) ∧
        (∀ s t, 0 < (1 - (a.tilt n s t : ℝ)) * p * ((a.state n).sizes t : ℝ)) ∧
        (∀ s t,
          |Real.log ((q s t : ℝ) * ((y.sizes t : ℝ) - (if s = t then 1 else 0) - p * ((a.state n).sizes t : ℝ)) /
              ((1 - (q s t : ℝ)) * p * ((a.state n).sizes t : ℝ))) -
            Real.log ((a.tilt n s t : ℝ) * (((a.state n).sizes t : ℝ) - (if s = t then 1 else 0) - p * ((a.state n).sizes t : ℝ)) /
              ((1 - (a.tilt n s t : ℝ)) * p * ((a.state n).sizes t : ℝ))) -
            τ * (Real.sqrt (p * N) ^ n / Real.sqrt (N : ℝ)) * β n s t| ≤
              K * (Real.sqrt (p * N) ^ n / Real.sqrt (N : ℝ)) * (N : ℝ) ^ (-d)) ∧
        (∀ u : History (n + 2),
          |Local.templateSizes y.sizes q u - ((a.state (n + 1)).sizes u : ℝ) -
            τ * (Real.sqrt (N : ℝ) * Real.sqrt (p * N) ^ (n + 1)) * ε (n + 1) u| ≤
              K * (Real.sqrt (N : ℝ) * Real.sqrt (p * N) ^ (n + 1)) * (N : ℝ) ^ (-d)) ∧
        (∀ u v : History (n + 2),
          |Local.templateEdges y.sizes y.realEdges q u v - (a.state (n + 1)).edges u v *
            (1 + τ * (Real.sqrt (p * N) ^ (n + 1) / Real.sqrt (N : ℝ)) *
              (ε (n + 1) u / ν (n + 1) u + ε (n + 1) v / ν (n + 1) v))| ≤
                K * (Real.sqrt (p * N) ^ (n + 1) / Real.sqrt (N : ℝ)) * (N : ℝ) ^ (-d) * (N : ℝ)^2 * p) := by
  intro θ hθlo hθhi n hk T δ hT hδ
  obtain ⟨K, hK, d, hd, φ, hφ, hφhi, N₀, hN₀, h⟩ :=
    perturbed_evolution θ hθlo hθhi n hk T δ hT hδ
  refine ⟨K, hK, d, hd, φ, hφ, hφhi, N₀, hN₀, ?_⟩
  intro N hN p hp₀ hp₁
  obtain ⟨hp, ha, h⟩ := h N hN p hp₀ hp₁
  refine ⟨hp, ha, ?_⟩
  intro τ hτ hτT V inst hcard y hreg hF1 hF2
  have hf : Faithful N p T δ τ (referenceDataReal θ T N p) y := by
    refine ⟨hreg, ?_, hF2⟩
    simpa only [Local.CoarseData.integerSizes, Int.cast_natCast, sizeScale] using hF1
  have hc := h τ hτ hτT V hcard y hf
  obtain ⟨q, hq, huniq⟩ := hc.tilt.exists_unique
  have hq' : Local.Solves y.sizes y.realEdges q := by simpa using hq
  have had := hc.admissible q hq'
  have htm := hc.template q hq'
  obtain ⟨_, hden, hrden, heff⟩ := hc.tilt.approximation q hq
  have hres := hc.tilt.residual_pos
  simp only [naturalSizes_coarse] at heff hres
  refine ⟨q, hreg, ?_, ?_, ?_, had.positive, ?_, ?_, ?_, ?_, ?_, ?_,
    hres, hc.tilt.reference_residual_pos, hden, hrden, heff, htm.sizes, htm.edges⟩
  · simpa only [hcard] using had.sizes
  · simpa only [hcard] using had.imbalances
  · simpa only [hcard, Local.edgeScale, Local.CoarseData.realEdges] using had.edge_scale
  · simpa only [hcard, Local.edgeScale, Local.CoarseData.realEdges] using had.separation
  · simpa only [hcard] using had.tilt
  · intro s
    exact (Binomial.eventMass_eq_measure (Local.trials y.sizes s) (q s) (Local.historySupport y.sizes s) ▸ had.conditioning s)
  · intro s t
    rw [← Local.rowMean_eq_integral]
    exact hq' s t
  · intro q' hq''
    apply huniq q'
    simp only [naturalSizes_coarse, realEdges_coarse]
    intro s t
    rw [Local.rowMean_eq_integral]
    exact hq'' s t
  · intro s b
    simpa only [Local.splitProbability_eq_measure] using had.split s b

/-- The carrier accepts only the listed structural inputs, including empty fibers. -/
example {V : Type*} [Fintype V] {n : ℕ}
    (π : V → History (n + 1)) (m : History (n + 1) → History (n + 1) → ℤ)
    (symm : ∀ s t, m s t = m t s) (even : ∀ s, Even (m s s))
    (nonneg : ∀ s t, 0 ≤ m s t)
    (upper : ∀ s t, m s t ≤ (Local.partSizes π s : ℤ) *
      ((Local.partSizes π t : ℤ) - if s = t then 1 else 0))
    (reg : Bool) : Local.CoarseData V n := ⟨π, m, symm, even, nonneg, upper, reg⟩

example {n : ℕ} (sizes : Local.Sizes n) (q : Local.Tilt n) (s : History (n + 1)) :
    Local.rowCondition sizes q s = ProbabilityTheory.cond (Local.rowLaw sizes q s)
      {a | WithLp.toLp 2 (fun t => (a t : ℝ)) ∈ historyEvent s} :=
  Local.rowCondition_eq_actual sizes q s

example {n : ℕ} (sizes : Local.Sizes n) (q : Local.Tilt n)
    (s t : History (n + 1)) (b : Bool) :
    Local.templateHalfEdges sizes q (append s b) t = (sizes s : ℝ) *
      (∫ a, (Binomial.event (Local.childSupport sizes s b)).indicator
        (fun a => (a t : ℝ)) a ∂Local.rowCondition sizes q s) := by
  simp only [Local.templateHalfEdges, parent_append, last_append, Local.splitMoment_eq_integral]

example (x a : ℝ) : decision false false (x - a) ↔ a ≤ x := by
  simp [decision]
  constructor
  · rintro (h | h) <;> linarith
  · intro h
    by_cases he : x = a
    · right; exact sub_eq_zero.mpr he
    · left; exact lt_of_le_of_ne h (Ne.symm he)
example (x a : ℝ) : decision false true (x - a) ↔ x < a := by simp [decision]
example (x a : ℝ) : decision true false (x - a) ↔ a < x := by simp [decision]
example (x a : ℝ) : decision true true (x - a) ↔ x ≤ a := by
  simp [decision]
  constructor
  · rintro (h | h) <;> linarith
  · intro h
    by_cases he : x = a
    · right; exact sub_eq_zero.mpr he
    · left; exact lt_of_le_of_ne h he

end MajorityDynamics.Idealized.PerturbedEvolution

/-- info: 'MajorityDynamics.Idealized.PerturbedEvolution.perturbed_evolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.PerturbedEvolution.perturbed_evolution

/-- info: 'MajorityDynamics.Idealized.PerturbedEvolution.perturbed_evolution_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.PerturbedEvolution.perturbed_evolution_finite

/-- info: 'MajorityDynamics.Idealized.PerturbedEvolution.perturbed_evolution_of_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.PerturbedEvolution.perturbed_evolution_of_partition
