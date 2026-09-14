import MajorityDynamics.Idealized.PerturbedTilt.Main

/-! Exact endpoint types, expanded inputs and outputs, and actual-law bridges. -/
noncomputable section
open MeasureTheory
namespace MajorityDynamics.Idealized.PerturbedTilt
open Universal LinearResponse

example : PerturbedTiltTheorem := perturbed_tilt

/-- Independent expansion of every varying input and the actual solving law.
In particular neither positivity, support geometry, nor a process specification
is an input to this closed statement. -/
example :
    ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∀ n : ℕ, (n : ℝ) + 1 < 1 / (1 - θ) →
    ∀ T δ : ℝ, 1 < T → 0 < δ →
    ∃ T₁ : ℝ, T ≤ T₁ ∧ ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
    ∀ N ≥ N₀, ∀ p : ℝ, T⁻¹ * (N : ℝ) ^ (-θ) < p → p < T * (N : ℝ) ^ (-θ) →
    ∃ hp : 0 < p ∧ p < 1,
      Process.Specification N ⟨p, hp⟩ (responseHorizon θ) (processExponent θ T)
        (referenceDataReal θ T N p) ∧
      ∀ τ : ℝ, T⁻¹ ≤ τ → τ ≤ T →
      ∀ η : History (n + 1) → ℤ, ∀ e : History (n + 1) → History (n + 1) → ℤ,
      (∀ s, |(η s : ℝ) - (((referenceDataReal θ T N p).state n).sizes s : ℝ) -
        τ * (Real.sqrt (N : ℝ) * Real.sqrt (p * N) ^ n) * ε n s| ≤
          T * (Real.sqrt (N : ℝ) * Real.sqrt (p * N) ^ n) * (N : ℝ) ^ (-δ)) →
      (∀ s t, |(e s t : ℝ) - ((referenceDataReal θ T N p).state n).edges s t *
        (1 + τ * (Real.sqrt (p * N) ^ n / Real.sqrt (N : ℝ)) *
          (ε n s / ν n s + ε n t / ν n t))| ≤
          T * (Real.sqrt (p * N) ^ n / Real.sqrt (N : ℝ)) * (N : ℝ) ^ (-δ) * (N : ℝ) ^ 2 * p) →
      let a := referenceDataReal θ T N p
      let sizes := fun s => (η s).toNat
      (∀ s, 0 < η s) ∧ (∀ s, (sizes s : ℝ) = (η s : ℝ)) ∧
      (∀ s t, (Local.trials sizes s t : ℝ) = (η t : ℝ) - (if s = t then 1 else 0)) ∧
      (∀ s t, 0 < (sizes t : ℝ) - (if s = t then 1 else 0) - p * ((a.state n).sizes t : ℝ)) ∧
      (∀ s t, 0 < ((a.state n).sizes t : ℝ) - (if s = t then 1 else 0) - p * ((a.state n).sizes t : ℝ)) ∧
      ∃ q : Local.Tilt n,
        (∀ s, 0 < (Local.rowLaw sizes q s).real (Binomial.event (Local.historySupport sizes s))) ∧
        (∀ s t, (η s : ℝ) * (∫ z, (z t : ℝ) ∂Local.rowCondition sizes q s) = (e s t : ℝ)) ∧
        (∀ q' : Local.Tilt n, (∀ s t, (η s : ℝ) *
          (∫ z, (z t : ℝ) ∂Local.rowCondition sizes q' s) = (e s t : ℝ)) → q' = q) ∧
        (∀ s t, 0 < (1 - (q s t : ℝ)) * p * ((a.state n).sizes t : ℝ)) ∧
        (∀ s t, 0 < (1 - (a.tilt n s t : ℝ)) * p * ((a.state n).sizes t : ℝ)) ∧
        ∀ s t,
          |Real.log ((q s t : ℝ) * ((sizes t : ℝ) - (if s = t then 1 else 0) - p * ((a.state n).sizes t : ℝ)) /
              ((1 - (q s t : ℝ)) * p * ((a.state n).sizes t : ℝ))) -
            Real.log ((a.tilt n s t : ℝ) * (((a.state n).sizes t : ℝ) - (if s = t then 1 else 0) - p * ((a.state n).sizes t : ℝ)) /
              ((1 - (a.tilt n s t : ℝ)) * p * ((a.state n).sizes t : ℝ))) -
            τ * (Real.sqrt (p * N) ^ n / Real.sqrt (N : ℝ)) * β n s t| ≤
            T₁ * (Real.sqrt (p * N) ^ n / Real.sqrt (N : ℝ)) * (N : ℝ) ^ (-δ₁) := by
  intro θ hθlo hθhi n hk T δ hT hδ
  obtain ⟨T₁, hT₁, δ₁, hδ₁, N₀, hN₀, h⟩ := perturbed_tilt θ hθlo hθhi n hk T δ hT hδ
  refine ⟨T₁, hT₁, δ₁, hδ₁, N₀, hN₀, ?_⟩
  intro N hN p hp₀ hp₁
  obtain ⟨hp, ha, h⟩ := h N hN p hp₀ hp₁
  refine ⟨hp, ha, ?_⟩
  intro τ hτ hτT η e hF1 hF2
  have hc := h τ hτ hτT η e ⟨hF1, hF2⟩
  obtain ⟨q, hq, huniq⟩ := hc.exists_unique
  obtain ⟨hmass, hden, hrefden, htilt⟩ := hc.approximation q hq
  refine ⟨hc.sizes_pos, hc.sizes_cast, hc.trials_cast, hc.residual_pos,
    hc.reference_residual_pos, q, ?_, ?_, ?_, hden, hrefden, htilt⟩
  · intro s
    exact (Binomial.eventMass_eq_measure (Local.trials (naturalSizes η) s) (q s)
      (Local.historySupport (naturalSizes η) s) ▸ hmass s)
  · intro s t
    rw [← Local.rowMean_eq_integral]
    rw [← hc.sizes_cast s]
    exact hq s t
  · intro q' hq'
    apply huniq q'
    intro s t
    rw [Local.rowMean_eq_integral, hc.sizes_cast s]
    exact hq' s t

/-- The original tie-sensitive event is retained in the normalized law. -/
example {n : ℕ} (sizes : Local.Sizes n) (q : Local.Tilt n) (s : History (n + 1)) :
    Local.rowCondition sizes q s = ProbabilityTheory.cond (Local.rowLaw sizes q s)
      {a | WithLp.toLp 2 (fun t => (a t : ℝ)) ∈ historyEvent s} :=
  Local.rowCondition_eq_actual sizes q s

example {n N : ℕ} (π : Fin N → History (n + 1)) (s t : History (n + 1)) :
    Local.trials (naturalSizes (partitionSizes π)) s t =
      (Finset.univ.filter (fun v => π v = t)).card - (if s = t then 1 else 0) := by
  rw [naturalSizes_partition]
  rfl

example {n : ℕ} (sizes : Local.Sizes n) (hsize : ∀ t, 2 * n + 5 ≤ sizes t)
    (e : Local.EdgeCounts n) (q q' : Local.Tilt n)
    (hq : ∀ s t, (sizes s : ℝ) * Local.rowMean sizes q s t = e s t)
    (hq' : ∀ s t, (sizes s : ℝ) * Local.rowMean sizes q' s t = e s t) : q = q' :=
  all_solving_tilts_unique sizes hsize e hq hq'

end MajorityDynamics.Idealized.PerturbedTilt

/-- info: 'MajorityDynamics.Idealized.PerturbedTilt.perturbed_tilt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.PerturbedTilt.perturbed_tilt

/-- info: 'MajorityDynamics.Idealized.PerturbedTilt.perturbed_tilt_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.PerturbedTilt.perturbed_tilt_partition

/-- info: 'MajorityDynamics.Idealized.PerturbedTilt.all_solving_tilts_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.PerturbedTilt.all_solving_tilts_unique

/-- info: 'MajorityDynamics.Idealized.PerturbedTilt.partition_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.PerturbedTilt.partition_faithful

/-- info: 'MajorityDynamics.Idealized.PerturbedTilt.perturbed_tilt_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MajorityDynamics.Idealized.PerturbedTilt.perturbed_tilt_spec

